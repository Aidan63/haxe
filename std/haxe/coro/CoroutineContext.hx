package haxe.coro;

class CoroutineContext {
    public final scheduler : IScheduler;

    public final coroutine : ICoroutine;

    public function new(scheduler, coroutine) {
        this.scheduler = scheduler;
        this.coroutine = coroutine;
    }
}