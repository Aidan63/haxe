package haxe.coro;

class CoroutineContext {
    public final scheduler : IScheduler;

    public final job : Job;

    public function new(scheduler, job) {
        this.scheduler = scheduler;
        this.job       = job;
    }
}