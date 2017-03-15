/*
 * sched_task_trace.c -- record scheduling events to a byte stream
 */

#define NO_TASK_TRACE_DECLS

#include <linux/module.h>
#include <linux/sched.h>
#include <linux/percpu.h>

#include <litmus/ftdev.h>
#include <litmus/litmus.h>

#include <litmus/sched_trace.h>
#include <litmus/feather_trace.h>
#include <litmus/ftdev.h>

#define NO_EVENTS		(1 << CONFIG_SCHED_TASK_TRACE_SHIFT)

#define now() litmus_clock()

struct local_buffer {
	struct st_event_record record[NO_EVENTS];
	char   flag[NO_EVENTS];
	struct ft_buffer ftbuf;
};

DEFINE_PER_CPU(struct local_buffer, st_event_buffer);

static struct ftdev st_dev;

static int st_dev_can_open(struct ftdev *dev, unsigned int cpu)
{
	return cpu_online(cpu) ? 0 : -ENODEV;
}

static int __init init_sched_task_trace(void)
{
	struct local_buffer* buf;
	int i, ok = 0, err;
	printk("Allocated %u sched_trace_xxx() events per CPU "
	       "(buffer size: %d bytes)\n",
	       NO_EVENTS, (int) sizeof(struct local_buffer));

	err = ftdev_init(&st_dev, THIS_MODULE,
			num_online_cpus(), "sched_trace");
	if (err)
		goto err_out;

	for (i = 0; i < st_dev.minor_cnt; i++) {
		buf = &per_cpu(st_event_buffer, i);
		ok += init_ft_buffer(&buf->ftbuf, NO_EVENTS,
				     sizeof(struct st_event_record),
				     buf->flag,
				     buf->record);
		st_dev.minor[i].buf = &buf->ftbuf;
	}
	if (ok == st_dev.minor_cnt) {
		st_dev.can_open = st_dev_can_open;
		err = register_ftdev(&st_dev);
		if (err)
			goto err_dealloc;
	} else {
		err = -EINVAL;
		goto err_dealloc;
	}

	return 0;

err_dealloc:
	ftdev_exit(&st_dev);
err_out:
	printk(KERN_WARNING "Could not register sched_trace module\n");
	return err;
}

static void __exit exit_sched_task_trace(void)
{
	ftdev_exit(&st_dev);
}

module_init(init_sched_task_trace);
module_exit(exit_sched_task_trace);


static inline struct st_event_record* get_record(u8 type, struct task_struct* t)
{
	struct st_event_record* rec = NULL;
	struct local_buffer* buf;

	buf = &get_cpu_var(st_event_buffer);
	if (ft_buffer_start_write(&buf->ftbuf, (void**) &rec)) {
		rec->hdr.type = type;
		rec->hdr.cpu  = smp_processor_id();
		rec->hdr.pid  = t ? t->pid : 0;
		//rec->hdr.job  = t ? t->rt_param.job_params.job_no : 0;
		rec->hdr.job  = t ? ( t->rt_param.running_job ?
		t->rt_param.running_job->job_params.job_no : 0) : 0;
	} else {
		put_cpu_var(st_event_buffer);
	}
	/* rec will be NULL if it failed */
	return rec;
}

static inline void put_record(struct st_event_record* rec)
{
	struct local_buffer* buf;
	/* don't use get_cpu_var() here, get_record() did that already for us */
	buf = this_cpu_ptr(&st_event_buffer);
	ft_buffer_finish_write(&buf->ftbuf, rec);
	/* matches the get_cpu_var() in get_record() */
	put_cpu_var(st_event_buffer);
}

/*
 * called only after the task_admit callback finishes, which sets
 * running_job to NULL. So it's safe to set job_id to 0.
 */
feather_callback void do_sched_trace_task_name(unsigned long id, unsigned long _task)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec = get_record(ST_NAME, t);
	int i;
	if (rec) {
		for (i = 0; i < min(TASK_COMM_LEN, ST_NAME_LEN); i++)
			rec->data.name.cmd[i] = t->comm[i];
		put_record(rec);
	}
}

/*
 * same as above. safe to set job_id to 0. 
 */
feather_callback void do_sched_trace_task_param(unsigned long id, unsigned long _task)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec = get_record(ST_PARAM, t);
	if (rec) {
		rec->data.param.wcet      = get_exec_cost(t);
		rec->data.param.period    = get_rt_period(t);
		rec->data.param.phase     = get_rt_phase(t);
		rec->data.param.partition = get_partition(t);
		rec->data.param.class     = get_class(t);
		put_record(rec);
	}
}

/*
 * slightly more complicated than above. It is called during sporatic release after wakeup,
 * during arm_release_timer(). The former already has the latest info. 
 * The later needs a overwite on the job_id.
 */
feather_callback void do_sched_trace_task_release(unsigned long id, unsigned long _task)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec = get_record(ST_RELEASE, t);
	if (rec) {
		/* the original struct has the latest release info, so
		  over write the job_no */
		rec->hdr.job = t->rt_param.job_params.job_no; 
		rec->data.release.release  = get_release(t);
		rec->data.release.deadline = get_deadline(t);
		put_record(rec);
	}
}

/* skipped: st_assigned_data, we don't use it atm */

/*
 * called after pick_next_task. Safe to use running_job.
 * not sure what schedule_tail does
 */
feather_callback void do_sched_trace_task_switch_to(unsigned long id,
						    unsigned long _task)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec;
	if (is_realtime(t)) {
		rec = get_record(ST_SWITCH_TO, t);
		if (rec) {
			rec->data.switch_to.when      = now();
			//rec->data.switch_to.exec_time = get_exec_time(t);
			/* this is only called when a task is picked so running_job is not NULL */
			BUG_ON(!tsk_rt(t)->running_job);
			rec->data.switch_to.exec_time = get_exec_time_job(tsk_rt(t)->running_job);
			put_record(rec);
		}
	}
}

/*
 * called before pick_next_task. safe to use running_job
 */
feather_callback void do_sched_trace_task_switch_away(unsigned long id,
						      unsigned long _task)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec;
	if (is_realtime(t)) {
		rec = get_record(ST_SWITCH_AWAY, t);
		if (rec) {
			rec->data.switch_away.when      = now();
			/* this is only called before schedule is called so running_job is not NULL */
			BUG_ON(!tsk_rt(t)->running_job);
			rec->data.switch_away.exec_time = 
			    get_exec_time_job(tsk_rt(t)->running_job);
			put_record(rec);
		}
	}
}

/*
 * called before task_exit callback, not necessarily has running job.
 * called during psn_schedule() but running job is still valid.
 */
feather_callback void do_sched_trace_task_completion(unsigned long id,
						     unsigned long _task,
						     unsigned long forced)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec = get_record(ST_COMPLETION, t);
	if (rec) {
		rec->data.completion.when   = now();
		rec->data.completion.forced = forced;
		//rec->data.completion.exec_time = get_exec_time(t);
		printk("cpu %d trace comp at %llu\n", smp_processor_id(), now());
		if ( tsk_rt(t)->running_job )
		{
		    rec->data.completion.exec_time = get_exec_time_job(tsk_rt(t)->running_job);
		    printk("trace: comp %llu\n", get_exec_time_job(tsk_rt(t)->running_job));
		}
		else
		{
		   printk("trace: comp no running job\n"); 
		}
    		put_record(rec);
	}
}

feather_callback void do_sched_trace_last_suspension_as_completion(
	unsigned long id,
	unsigned long _task)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec = get_record(ST_COMPLETION, t);
	if (rec) {
		rec->data.completion.when
			= tsk_rt(t)->job_params.last_suspension;
		rec->data.completion.forced = 0;
		rec->data.completion.exec_time = get_exec_time(t);
		put_record(rec);
	}
}

feather_callback void do_sched_trace_task_block(unsigned long id,
						unsigned long _task)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec = get_record(ST_BLOCK, t);
	if (rec) {
		rec->data.block.when      = now();
		put_record(rec);
	}
}

feather_callback void do_sched_trace_task_resume(unsigned long id,
						 unsigned long _task)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec = get_record(ST_RESUME, t);
	if (rec) {
		rec->data.resume.when      = now();
		put_record(rec);
	}
}

feather_callback void do_sched_trace_sys_release(unsigned long id,
						 unsigned long _start)
{
	lt_t *start = (lt_t*) _start;
	struct st_event_record* rec = get_record(ST_SYS_RELEASE, NULL);
	if (rec) {
		rec->data.sys_release.when    = now();
		rec->data.sys_release.release = *start;
		put_record(rec);
	}
}

feather_callback void do_sched_trace_action(unsigned long id,
					    unsigned long _task,
					    unsigned long action)
{
	struct task_struct *t = (struct task_struct*) _task;
	struct st_event_record* rec = get_record(ST_ACTION, t);

	if (rec) {
		rec->data.action.when   = now();
		rec->data.action.action = action;
		put_record(rec);
	}
}
