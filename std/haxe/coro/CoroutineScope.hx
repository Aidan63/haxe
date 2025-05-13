package haxe.coro;

import haxe.coro.continuations.JobContinuation;

class CoroutineScope {
    public final context : CoroutineContext;

    public function new(context) {
        this.context = context;
    }

    public function start(c:Coroutine<CoroutineScope->Void>):Job {
        final newJob     = context.job.create();
        final newContext = new CoroutineContext(context.scheduler, newJob);
        final newScope   = new CoroutineScope(newContext);
        final cont       = new JobContinuation(newContext);

        newContext.scheduler.schedule(() -> {
            final result = c(newScope, cont);

            switch result.state {
                case Pending:
                    return;
                case Returned:
                    newJob.complete(result.result);
                case Thrown:
                    newJob.completeExceptionally(result.error);
            }
        });

        return newJob;
    }
}
