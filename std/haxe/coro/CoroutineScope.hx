package haxe.coro;

import haxe.exceptions.NotImplementedException;

class CoroutineScope {
    public final context : CoroutineContext;

    public function new(context) {
        this.context = context;
    }

    public function start(c:Coroutine<CoroutineScope->Void>):Job {
        final newJob     = new Job(context.job);
        final newContext = new CoroutineContext(context.scheduler, newJob);
        final newScope   = new CoroutineScope(newContext);

        newContext.scheduler.schedule(() -> {
            c(newScope);
        });

        return newJob;
    }
}

