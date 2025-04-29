package haxe.coro;

import haxe.exceptions.NotImplementedException;
import haxe.coro.continuations.JobContinuation;

class CoroutineScope {
    public final context : CoroutineContext;

    public function new(context) {
        this.context = context;
    }

    public function start(c:Coroutine<CoroutineScope->Void>):Job {
        final newJob     = new Job(context.job);
        final newContext = new CoroutineContext(context.scheduler, newJob);
        final newScope   = new CoroutineScope(newContext);
        final cont       = new JobContinuation(newJob, newContext);

        newContext.scheduler.schedule(() -> {
            final result = c(cont, newScope);

            switch result.control {
                case Pending:
                    return;
                case Returned:
                    // TODO :
                    // - Wait for any children to complete
                    // - If any children errored, then error this job instead
                    // - Finally if no children errored then complete with the result
                    newJob.complete(result.result);
                case Thrown:
                    // TODO :
                    // - Cancel all job children
                    // - Wait for all children to complete
                    // - Then complete exceptionally

                    newJob.completeExceptionally(result.error);
            }
        });

        return newJob;
    }
}
