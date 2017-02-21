/*
 * kernel/sched_psn_edf.c
 *
 * Implementation of the PSN-EDF scheduler plugin.
 * Based on kern/sched_part_edf.c and kern/sched_gsn_edf.c.
 *
 * Suspensions and non-preemptable sections are supported.
 * Priority inheritance is not supported.
 */

#include <linux/percpu.h>
#include <linux/sched.h>
#include <linux/list.h>
#include <linux/spinlock.h>
#include <linux/module.h>

#include <litmus/litmus.h>
#include <litmus/jobs.h>
#include <litmus/preempt.h>
#include <litmus/budget.h>
#include <litmus/sched_plugin.h>
#include <litmus/edf_common.h>
#include <litmus/sched_trace.h>
#include <litmus/trace.h>

/* to set up domain/cpu mappings */
#include <litmus/litmus_proc.h>

typedef struct {
	rt_domain_t 		domain;
	int          		cpu;
	struct task_struct* 	scheduled; /* only RT tasks */
/*
 * scheduling lock slock
 * protects the domain and serializes scheduling decisions
 */
#define slock domain.ready_lock

#define JOB_PER_TASK 4

	struct list_head depletedq; /* list of recycled jobs */

} psnedf_domain_t;

DEFINE_PER_CPU(psnedf_domain_t, psnedf_domains);

#define local_edf		(&(this_cpu_ptr(&psnedf_domains)->domain))
#define local_pedf		(this_cpu_ptr(&psnedf_domains))
#define remote_edf(cpu)		(&per_cpu(psnedf_domains, cpu).domain)
#define remote_pedf(cpu)	(&per_cpu(psnedf_domains, cpu))
#define task_edf(task)		remote_edf(get_partition(task))
#define task_pedf(task)		remote_pedf(get_partition(task))


static void psnedf_domain_init(psnedf_domain_t* pedf,
			       check_resched_needed_t check,
			       release_jobs_t release,
			       int cpu)
{
	/* the job version has the correct comparator for jobs */
	edf_job_domain_init(&pedf->domain, check, release);
	pedf->cpu      		= cpu;
	pedf->scheduled		= NULL;

	INIT_LIST_HEAD(&pedf->depletedq);
}

static inline struct job_struct*
job_q_elem(struct list_head *elem)
{
    /* take out job struct from depletedq*/
    return list_entry(elem, struct job_struct, jobq_elem);
}

/*
 * get a job from the depletedq, and link it to t
 */
static struct job_struct* get_job(struct task_struct* t)
{
    psnedf_domain_t* 	pedf = task_pedf(t);
    struct list_head *depletedq = &pedf->depletedq;
    struct job_struct* job = NULL;

    if ( !list_empty(depletedq) )
    {
	job = job_q_elem(depletedq->next);
	list_del_init(&job->jobq_elem);
    }
    else
	TRACE("not enough jobs at %llu\n", litmus_clock()); 

    BUG_ON(!job);
    job->job_params = t->rt_param.job_params; /* copy to a spcific job */
    job->rt = &t->rt_param;
	/* link node to job */
    bheap_node_init(&job->heap_node, job);
    return job;
}

static inline void recycle_job(struct job_struct* job)
{
    psnedf_domain_t* 	pedf = local_pedf;
    struct list_head *depletedq = &pedf->depletedq;

    /* break from task's queue */
    list_del_init(&job->jobq_elem);
    list_add_tail(&job->jobq_elem, depletedq); 
}

/* queues job in EDF order to a task */
static void queue_job_to(struct job_struct* job, struct rt_param* rt)
{
    struct list_head *iter;

    list_for_each ( iter, &rt->queued_jobs )
    {
	struct job_struct* j = job_q_elem(iter);

	if ( lt_before(job->job_params.deadline, j->job_params.deadline))
	    break;
    }
    list_add_tail(&job->jobq_elem, iter);
}

static void requeue_job(struct task_struct* t, rt_domain_t *edf, struct job_struct* job)
{
/*
	if (t->state != TASK_RUNNING)
		TRACE_TASK(t, "requeue: !TASK_RUNNING\n");

	tsk_rt(t)->completed = 0;
	if (is_early_releasing(t) || is_released(t, litmus_clock()))
		__add_ready(edf, t);
	else

		add_release(edf, t);
*/
	BUG_ON(!job);
	if (t->state != TASK_RUNNING)
		TRACE_TASK(t, "requeue: !TASK_RUNNING\n");
	job->rt->completed = 0;
	/* TO_DO: modify job release mechanisms */
	//if ( lt_before_eq(job->job_params.release, litmus_clock()) )
	if ( get_exec_time_job(job) < get_exec_cost(t) )
	{
	    printk("cpu %d add pid %d job %d to readyq\n", smp_processor_id(),t->pid, job->job_params.job_no);
	   __add_ready_job(edf, t, job);
	
	}
	else
	{
	    printk("cpu %d add pid %d job %d to deplq\n", smp_processor_id(), t->pid, job->job_params.job_no);
	    add_release_job(edf, t, job); 
	    recycle_job(job);
	}
}

/* find job from a node reference */
static inline struct job_struct* node2job(struct bheap_node* hn)
{
    return hn ? (struct job_struct*)(hn->value) : NULL;
}

/* find task from a job reference 
static inline struct task_struct* job2task(struct job_struct* j)
{
    BUG_ON(!j);
    return container_of(j->rt, struct task_struct, rt_param);
}
*/

/*
 * recycle all queued jobs for a rt_param except the currently running one.
 * it should be taken care of somewhere else.
 */
static inline void recycle_all_queued_jobs(struct task_struct* tsk)
{
    struct list_head *iter, *tmp;
    struct rt_param* rt = &tsk->rt_param;

    list_for_each_safe ( iter, tmp, &rt->queued_jobs )
    {
        struct job_struct* job = job_q_elem(iter);

        if ( rt->running_job != job )
            recycle_job(job);
    }

}

/* we assume the lock is being held */
static void preempt(psnedf_domain_t *pedf)
{
	preempt_if_preemptable(pedf->scheduled, pedf->cpu);
}

#ifdef CONFIG_LITMUS_LOCKING

static void boost_priority(struct task_struct* t)
{
	unsigned long		flags;
	psnedf_domain_t* 	pedf = task_pedf(t);
	lt_t			now;

	raw_spin_lock_irqsave(&pedf->slock, flags);
	now = litmus_clock();

	TRACE_TASK(t, "priority boosted at %llu\n", now);

	tsk_rt(t)->priority_boosted = 1;
	tsk_rt(t)->boost_start_time = now;

	if (pedf->scheduled != t) {
		/* holder may be queued: first stop queue changes */
		raw_spin_lock(&pedf->domain.release_lock);
		if (is_queued(t) &&
		    /* If it is queued, then we need to re-order. */
		    bheap_decrease(edf_ready_order, tsk_rt(t)->heap_node) &&
		    /* If we bubbled to the top, then we need to check for preemptions. */
		    edf_preemption_needed(&pedf->domain, pedf->scheduled))
				preempt(pedf);
		raw_spin_unlock(&pedf->domain.release_lock);
	} /* else: nothing to do since the job is not queued while scheduled */

	raw_spin_unlock_irqrestore(&pedf->slock, flags);
}

static void unboost_priority(struct task_struct* t)
{
	unsigned long		flags;
	psnedf_domain_t* 	pedf = task_pedf(t);
	lt_t			now;

	raw_spin_lock_irqsave(&pedf->slock, flags);
	now = litmus_clock();

	/* Assumption: this only happens when the job is scheduled.
	 * Exception: If t transitioned to non-real-time mode, we no longer
	 * care about it. */
	BUG_ON(pedf->scheduled != t && is_realtime(t));

	TRACE_TASK(t, "priority restored at %llu\n", now);

	tsk_rt(t)->priority_boosted = 0;
	tsk_rt(t)->boost_start_time = 0;

	/* check if this changes anything */
	if (edf_preemption_needed(&pedf->domain, pedf->scheduled))
		preempt(pedf);

	raw_spin_unlock_irqrestore(&pedf->slock, flags);
}

#endif

static int psnedf_preempt_check(psnedf_domain_t *pedf)
{
	printk("cpu %d check resched\n", smp_processor_id());
	if (edf_job_preemption_needed(&pedf->domain, pedf->scheduled)) {
		preempt(pedf);
		return 1;
	} else
		return 0;
}

/* This check is trivial in partioned systems as we only have to consider
 * the CPU of the partition.
 */
static int psnedf_check_resched(rt_domain_t *edf)
{
	psnedf_domain_t *pedf = container_of(edf, psnedf_domain_t, domain);

	/* because this is a callback from rt_domain_t we already hold
	 * the necessary lock for the ready queue
	 */
	return psnedf_preempt_check(pedf);
}

static void job_completion(struct task_struct* t, int forced)
{
	sched_trace_task_completion(t, forced);
	TRACE_TASK(t, "job_completion(forced=%d).\n", forced);

	tsk_rt(t)->completed = 0;
	recycle_job(t->rt_param.running_job);
	prepare_for_next_period(t);
}

static inline void print_job(struct job_struct* job)
{
    struct rt_job* rtj = &job->job_params;
    printk("job %u - release: %llu dl: %llu  exc: %llu sus: %llu\n", rtj->job_no, rtj->release, rtj->deadline, rtj->exec_time, rtj->last_suspension);
}

static struct task_struct* psnedf_schedule(struct task_struct * prev)
{
	psnedf_domain_t* 	pedf = local_pedf;
	rt_domain_t*		edf  = &pedf->domain;
	struct job_struct*	next;

	int 			out_of_time, sleep, preempt,
				np, exists, blocks, resched;

	raw_spin_lock(&pedf->slock);

	/* sanity checking
	 * differently from gedf, when a task exits (dead)
	 * pedf->schedule may be null and prev _is_ realtime
	 */
	BUG_ON(pedf->scheduled && pedf->scheduled != prev);
	BUG_ON(pedf->scheduled && !is_realtime(prev));

	BUG_ON(pedf->scheduled && !pedf->scheduled->rt_param.running_job);

	if (smp_processor_id() == 2 && pedf->scheduled)
	{
		printk("cpu %d prev sched: pid %d ", smp_processor_id(), pedf->scheduled->pid);
		print_job(pedf->scheduled->rt_param.running_job);	
	}
	/* (0) Determine state */
	exists      = pedf->scheduled != NULL;
	blocks      = exists && !is_current_running();
	out_of_time = exists && budget_enforced(pedf->scheduled)
			     && budget_exhausted_job(pedf->scheduled->rt_param.running_job, pedf->scheduled);
	np 	    = exists && is_np(pedf->scheduled);
	sleep	    = exists && is_completed(pedf->scheduled);
	preempt     = edf_job_preemption_needed(edf, prev);

	//if (smp_processor_id() == 2)
	//	printk("cpu%d done status\n",smp_processor_id());
	/* If we need to preempt do so.
	 * The following checks set resched to 1 in case of special
	 * circumstances.
	 */
	resched = preempt;

	/* If a task blocks we have no choice but to reschedule.
	 */
	if (blocks)
		resched = 1;

	/* Request a sys_exit_np() call if we would like to preempt but cannot.
	 * Multiple calls to request_exit_np() don't hurt.
	 */
	if (np && (out_of_time || preempt || sleep))
		request_exit_np(pedf->scheduled);

	/* Any task that is preemptable and either exhausts its execution
	 * budget or wants to sleep completes. We may have to reschedule after
	 * this.
	 */
	//if (smp_processor_id() == 2)
	//	printk("cpu%d pre-job_comp\n",smp_processor_id());
	if (!np && (out_of_time || sleep)) {
		/* running job is set to NULL, recycled to depletedq inside */
		printk("cpu%d job comp\n", smp_processor_id());
		job_completion(pedf->scheduled, !sleep);
		resched = 1;
	}
	//if (smp_processor_id() == 2)
	//	printk("cpu%d post-job_comp\n",smp_processor_id());

	/* The final scheduling decision. Do we need to switch for some reason?
	 * Switch if we are in RT mode and have no task or if we need to
	 * resched.
	 */
	next = NULL;
	if ((!np || blocks) && (resched || !exists)) {
		/* When preempting a task that does not block, then
		 * re-insert it into either the ready queue or the
		 * release queue (if it completed). requeue() picks
		 * the appropriate queue.
		 */
		if (smp_processor_id() == 2 && pedf->scheduled)
		    printk("cpu %d status: blocks:%d resched:%d exists:%d preempt:%d sleep:%d out_of_time:%d\n",
			smp_processor(), blocks, resched, exists, preempt, sleep, out_of_time);
		
		if (pedf->scheduled && !blocks)
			requeue_job(pedf->scheduled, edf, pedf->scheduled->rt_param.running_job);
		else
		{
		    /* the current running task blocks. not sure whether block() is called
		     * first or this is called first. clear the job queue for this task.
		     */
		}
		if (exists)
			pedf->scheduled->rt_param.running_job = NULL;

		next = node2job(__take_ready_node(edf));
	} else
		/* Only override Linux scheduler if we have a real-time task
		 * scheduled that needs to continue.
		 */
		if (exists)
			pedf->scheduled = prev;

	if (next) {
		next->rt->running_job = next; 
		TRACE_TASK(job2task(next), "scheduled at %llu\n", litmus_clock());
		pedf->scheduled = job2task(next);
		if (smp_processor_id() == 2)
		{
		    printk("cpu %d next sched: pid %d ", smp_processor_id(), pedf->scheduled->pid);
		    print_job(pedf->scheduled->rt_param.running_job);	
		}
	} else
	{
		TRACE("becoming idle at %llu\n", litmus_clock());
		pedf->scheduled = NULL;
	}
	sched_state_task_picked();
	raw_spin_unlock(&pedf->slock);

	return next ? pedf->scheduled : NULL;
}
/*
 * Call back for updating a task. Return 0 if succeeds.
 */ 
static long psnedf_change_params(struct task_struct *task, struct rt_task *new_params)
{
   return 0; 
}

/*	Prepare a task for running in RT mode
 */
static void psnedf_task_new(struct task_struct * t, int on_rq, int is_scheduled)
{
	rt_domain_t* 		edf  = task_edf(t);
	psnedf_domain_t* 	pedf = task_pedf(t);
	unsigned long		flags;
	struct job_struct* job;

	TRACE_TASK(t, "psn edf: task new, cpu = %d\n",
		   t->rt_param.task_params.cpu);

	/* setup job parameters */
	release_at(t, litmus_clock());
	job = get_job(t);
	printk("cpu %d pid %d task_new release: ", smp_processor_id(), t->pid);
	print_job(job);
	
	/* The task should be running in the queue, otherwise signal
	 * code will try to wake it up with fatal consequences.
	 */
	raw_spin_lock_irqsave(&pedf->slock, flags);
	if (is_scheduled) {
		/* there shouldn't be anything else scheduled at the time */
		BUG_ON(pedf->scheduled);
		pedf->scheduled = t;
		t->rt_param.running_job = job;
	} else {
		/* later useful in mode-change */
		t->rt_param.running_job = NULL;
		queue_job_to(job, &t->rt_param);
		/* !is_scheduled means it is not scheduled right now, but it
		 * does not mean that it is suspended. If it is not suspended,
		 * it still needs to be requeued. If it is suspended, there is
		 * nothing that we need to do as it will be handled by the
		 * wake_up() handler. */
		if (on_rq) {
			//requeue(t, edf);
			requeue_job(t, edf, job);
			/* maybe we have to reschedule */
			psnedf_preempt_check(pedf);
		}
	}
	raw_spin_unlock_irqrestore(&pedf->slock, flags);
}

static void psnedf_task_wake_up(struct task_struct *task)
{
	unsigned long		flags;
	psnedf_domain_t* 	pedf = task_pedf(task);
	rt_domain_t* 		edf  = task_edf(task);
	lt_t			now;

	TRACE_TASK(task, "wake_up at %llu\n", litmus_clock());
	raw_spin_lock_irqsave(&pedf->slock, flags);
	printk("cpu %d pid %d wakeup\n", smp_processor_id(), task->pid);
	//BUG_ON(is_queued(task));
	//TO-DO check queued jobs
	now = litmus_clock();
	if (is_sporadic(task) && is_tardy(task, now)
#ifdef CONFIG_LITMUS_LOCKING
	/* We need to take suspensions because of semaphores into
	 * account! If a job resumes after being suspended due to acquiring
	 * a semaphore, it should never be treated as a new job release.
	 */
	    && !is_priority_boosted(task)
#endif
		) {
			inferred_sporadic_job_release_at(task, now);
	}

	/* Only add to ready queue if it is not the currently-scheduled
	 * task. This could be the case if a task was woken up concurrently
	 * on a remote CPU before the executing CPU got around to actually
	 * de-scheduling the task, i.e., wake_up() raced with schedule()
	 * and won.
	 */
	if (pedf->scheduled != task) {
		/* the blocking task(running) is descheduled already */
		/* because all jobs are removed when it blocked
		 * release a new job and add back to queue
		 */
		struct job_struct* job = get_job(task);
		printk("cpu %d wakeup release", smp_processor_id());
		print_job(job);
		/* to-do: use release job here instead */
		requeue_job(task, edf, job);
		psnedf_preempt_check(pedf);
	}
	else /* the blocking task(running) is still not descheduled */
	{
	    //TO_DO: in schedule, when blocked, remove the running job from task.
	}
	raw_spin_unlock_irqrestore(&pedf->slock, flags);
	TRACE_TASK(task, "wake up done\n");
}

static void psnedf_task_block(struct task_struct *t)
{
	/* only running tasks can block, thus t is in no queue */
	TRACE_TASK(t, "block at %llu, state=%d\n", litmus_clock(), t->state);

	BUG_ON(!is_realtime(t));
	/* remove all queued jobs */
	printk("cpu %d pid %d blocked\n", smp_processor_id(), t->pid);
	recycle_all_queued_jobs(t);
	//BUG_ON(is_queued(t));
}

static void psnedf_task_exit(struct task_struct * t)
{
	unsigned long flags;
	psnedf_domain_t* 	pedf = task_pedf(t);
	rt_domain_t*		edf;

	raw_spin_lock_irqsave(&pedf->slock, flags);
	printk("cpu %d pid %d exited\n", smp_processor_id(), t->pid);
	if (has_queued(t)) {
		struct list_head *iter, *tmp;
		/* dequeue */
		edf  = task_edf(t);
		list_for_each_safe ( iter, tmp, &t->rt_param.queued_jobs )
		{
		    struct job_struct* job = job_q_elem(iter);
		    /* running job is recycled in schedule() */
		    if ( t->rt_param.running_job != job )
		    {
			remove_job(edf, job->heap_node);
			recycle_job(job);
		    }
		}
	}
	if (pedf->scheduled == t)
		pedf->scheduled = NULL;

	TRACE_TASK(t, "RIP, now reschedule\n");

	preempt(pedf);
	raw_spin_unlock_irqrestore(&pedf->slock, flags);
}

#ifdef CONFIG_LITMUS_LOCKING

#include <litmus/fdso.h>
#include <litmus/srp.h>

/* ******************** SRP support ************************ */

static unsigned int psnedf_get_srp_prio(struct task_struct* t)
{
	return get_rt_relative_deadline(t);
}

/* ******************** FMLP support ********************** */

/* struct for semaphore with priority inheritance */
struct fmlp_semaphore {
	struct litmus_lock litmus_lock;

	/* current resource holder */
	struct task_struct *owner;

	/* FIFO queue of waiting tasks */
	wait_queue_head_t wait;
};

static inline struct fmlp_semaphore* fmlp_from_lock(struct litmus_lock* lock)
{
	return container_of(lock, struct fmlp_semaphore, litmus_lock);
}
int psnedf_fmlp_lock(struct litmus_lock* l)
{
	struct task_struct* t = current;
	struct fmlp_semaphore *sem = fmlp_from_lock(l);
	wait_queue_t wait;
	unsigned long flags;

	if (!is_realtime(t))
		return -EPERM;

	/* prevent nested lock acquisition --- not supported by FMLP */
	if (tsk_rt(t)->num_locks_held ||
	    tsk_rt(t)->num_local_locks_held)
		return -EBUSY;

	spin_lock_irqsave(&sem->wait.lock, flags);

	if (sem->owner) {
		/* resource is not free => must suspend and wait */

		init_waitqueue_entry(&wait, t);

		/* FIXME: interruptible would be nice some day */
		set_task_state(t, TASK_UNINTERRUPTIBLE);

		__add_wait_queue_tail_exclusive(&sem->wait, &wait);

		TS_LOCK_SUSPEND;

		/* release lock before sleeping */
		spin_unlock_irqrestore(&sem->wait.lock, flags);

		/* We depend on the FIFO order.  Thus, we don't need to recheck
		 * when we wake up; we are guaranteed to have the lock since
		 * there is only one wake up per release.
		 */

		schedule();

		TS_LOCK_RESUME;

		/* Since we hold the lock, no other task will change
		 * ->owner. We can thus check it without acquiring the spin
		 * lock. */
		BUG_ON(sem->owner != t);
	} else {
		/* it's ours now */
		sem->owner = t;

		/* mark the task as priority-boosted. */
		boost_priority(t);

		spin_unlock_irqrestore(&sem->wait.lock, flags);
	}

	tsk_rt(t)->num_locks_held++;

	return 0;
}

int psnedf_fmlp_unlock(struct litmus_lock* l)
{
	struct task_struct *t = current, *next;
	struct fmlp_semaphore *sem = fmlp_from_lock(l);
	unsigned long flags;
	int err = 0;

	spin_lock_irqsave(&sem->wait.lock, flags);

	if (sem->owner != t) {
		err = -EINVAL;
		goto out;
	}

	tsk_rt(t)->num_locks_held--;

	/* we lose the benefit of priority boosting */

	unboost_priority(t);

	/* check if there are jobs waiting for this resource */
	next = __waitqueue_remove_first(&sem->wait);
	if (next) {
		/* boost next job */
		boost_priority(next);

		/* next becomes the resouce holder */
		sem->owner = next;

		/* wake up next */
		wake_up_process(next);
	} else
		/* resource becomes available */
		sem->owner = NULL;

out:
	spin_unlock_irqrestore(&sem->wait.lock, flags);
	return err;
}

int psnedf_fmlp_close(struct litmus_lock* l)
{
	struct task_struct *t = current;
	struct fmlp_semaphore *sem = fmlp_from_lock(l);
	unsigned long flags;

	int owner;

	spin_lock_irqsave(&sem->wait.lock, flags);

	owner = sem->owner == t;

	spin_unlock_irqrestore(&sem->wait.lock, flags);

	if (owner)
		psnedf_fmlp_unlock(l);

	return 0;
}

void psnedf_fmlp_free(struct litmus_lock* lock)
{
	kfree(fmlp_from_lock(lock));
}

static struct litmus_lock_ops psnedf_fmlp_lock_ops = {
	.close  = psnedf_fmlp_close,
	.lock   = psnedf_fmlp_lock,
	.unlock = psnedf_fmlp_unlock,
	.deallocate = psnedf_fmlp_free,
};

static struct litmus_lock* psnedf_new_fmlp(void)
{
	struct fmlp_semaphore* sem;

	sem = kmalloc(sizeof(*sem), GFP_KERNEL);
	if (!sem)
		return NULL;

	sem->owner   = NULL;
	init_waitqueue_head(&sem->wait);
	sem->litmus_lock.ops = &psnedf_fmlp_lock_ops;

	return &sem->litmus_lock;
}

/* **** lock constructor **** */


static long psnedf_allocate_lock(struct litmus_lock **lock, int type,
				 void* __user unused)
{
	int err = -ENXIO;
	struct srp_semaphore* srp;

	/* PSN-EDF currently supports the SRP for local resources and the FMLP
	 * for global resources. */
	switch (type) {
	case FMLP_SEM:
		/* Flexible Multiprocessor Locking Protocol */
		*lock = psnedf_new_fmlp();
		if (*lock)
			err = 0;
		else
			err = -ENOMEM;
		break;

	case SRP_SEM:
		/* Baker's Stack Resource Policy */
		srp = allocate_srp_semaphore();
		if (srp) {
			*lock = &srp->litmus_lock;
			err = 0;
		} else
			err = -ENOMEM;
		break;
	};

	return err;
}

#endif

static struct domain_proc_info psnedf_domain_proc_info;
static long psnedf_get_domain_proc_info(struct domain_proc_info **ret)
{
	*ret = &psnedf_domain_proc_info;
	return 0;
}

static void psnedf_setup_domain_proc(void)
{
	int i, cpu;
	int release_master =
#ifdef CONFIG_RELEASE_MASTER
		atomic_read(&release_master_cpu);
#else
		NO_CPU;
#endif
	int num_rt_cpus = num_online_cpus() - (release_master != NO_CPU);
	struct cd_mapping *cpu_map, *domain_map;

	memset(&psnedf_domain_proc_info, 0, sizeof(psnedf_domain_proc_info));
	init_domain_proc_info(&psnedf_domain_proc_info, num_rt_cpus, num_rt_cpus);
	psnedf_domain_proc_info.num_cpus = num_rt_cpus;
	psnedf_domain_proc_info.num_domains = num_rt_cpus;

	for (cpu = 0, i = 0; cpu < num_online_cpus(); ++cpu) {
		if (cpu == release_master)
			continue;
		cpu_map = &psnedf_domain_proc_info.cpu_to_domains[i];
		domain_map = &psnedf_domain_proc_info.domain_to_cpus[i];

		cpu_map->id = cpu;
		domain_map->id = i; /* enumerate w/o counting the release master */
		cpumask_set_cpu(i, cpu_map->mask);
		cpumask_set_cpu(cpu, domain_map->mask);
		++i;
	}
}

static long psnedf_activate_plugin(void)
{
#ifdef CONFIG_RELEASE_MASTER
	int cpu;

	for_each_online_cpu(cpu) {
		remote_edf(cpu)->release_master = atomic_read(&release_master_cpu);
	}
#endif

#ifdef CONFIG_LITMUS_LOCKING
	get_srp_prio = psnedf_get_srp_prio;
#endif

	psnedf_setup_domain_proc();

	return 0;
}

static long psnedf_deactivate_plugin(void)
{
	destroy_domain_proc_info(&psnedf_domain_proc_info);
	return 0;
}

static long psnedf_admit_task(struct task_struct* tsk)
{
	psnedf_domain_t* 	pedf = local_pedf;
	struct list_head *depletedq = &pedf->depletedq;
	int i;

	if (task_cpu(tsk) == tsk->rt_param.task_params.cpu
#ifdef CONFIG_RELEASE_MASTER
	    /* don't allow tasks on release master CPU */
	     && task_cpu(tsk) != remote_edf(task_cpu(tsk))->release_master
#endif
		)
	{
	    for ( i = 0; i < JOB_PER_TASK; i++ )
	    {
		struct job_struct* job = job_struct_alloc(GFP_ATOMIC);

		INIT_LIST_HEAD(&job->jobq_elem);
		job->heap_node = bheap_node_alloc(GFP_ATOMIC);
		job->rt = NULL;
		/* node should be init with a task when released */
		//bheap_node_init(&job->heap_node, tsk);
		list_add_tail(&job->jobq_elem, depletedq);
	    }

	    INIT_LIST_HEAD(&tsk->rt_param.queued_jobs);
	    tsk->rt_param.running_job = NULL;
	    printk("cpu %d pid %d admitted\n", smp_processor_id(), tsk->pid);
 
	    return 0;
	}
	else
	    return -EINVAL;
}

static void psn_edf_release_jobs(rt_domain_t* rt, struct bheap* tasks)
{
	struct bheap_node* node;
	struct job_struct* job;
	unsigned long flags;
	
	raw_spin_lock_irqsave(&rt->ready_lock, flags);
	node = __take_node_from_relheap(rt, tasks);
	while ( node )
	{
	    struct task_struct* tsk = bheap2task(node);
	    
	    job = get_job(tsk);
	    bheap_insert(rt->order, &rt->ready_queue, job->heap_node);
	    printk("cpu %d pid %d timer release", smp_processor_id(), tsk->pid);
	    print_job(job);
	    node = __take_node_from_relheap(rt, tasks);
	}
	rt->check_resched(rt);
	raw_spin_unlock_irqrestore(&rt->ready_lock, flags);
}

/*	Plugin object	*/
static struct sched_plugin psn_edf_plugin __cacheline_aligned_in_smp = {
	.plugin_name		= "PSN-EDF",
	.task_new		= psnedf_task_new,
	.complete_job		= complete_job,
	.task_exit		= psnedf_task_exit,
	.task_change_params	= psnedf_change_params,
	.schedule		= psnedf_schedule,
	.task_wake_up		= psnedf_task_wake_up,
	.task_block		= psnedf_task_block,
	.admit_task		= psnedf_admit_task,
	.activate_plugin	= psnedf_activate_plugin,
	.deactivate_plugin	= psnedf_deactivate_plugin,
	.get_domain_proc_info	= psnedf_get_domain_proc_info,
#ifdef CONFIG_LITMUS_LOCKING
	.allocate_lock		= psnedf_allocate_lock,
#endif
};


static int __init init_psn_edf(void)
{
	int i;

	/* We do not really want to support cpu hotplug, do we? ;)
	 * However, if we are so crazy to do so,
	 * we cannot use num_online_cpu()
	 */
	for (i = 0; i < num_online_cpus(); i++) {
		psnedf_domain_init(remote_pedf(i),
				   psnedf_check_resched,
				   psn_edf_release_jobs, i);
	}
	/* TO-DO 
	 * add domain release function
	 */
	return register_sched_plugin(&psn_edf_plugin);
}

module_init(init_psn_edf);
