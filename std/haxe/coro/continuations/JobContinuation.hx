import haxe.Exception;
import haxe.coro.IContinuation;

class JobContinuation<T> implements IContinuation<T> {
    final context:CoroutineContext;

    public function new(context) {
        this.context = context;
    }

    public function resume(v:T, exn:Exception) {
        if (exn == null) {
            // TODO :
            // - Wait for any children to complete
            // - If any children errored, then error this job instead
            // - Finally if no children errored then complete with the result

            context.job.complete(v);
        } else {
            // TODO :
            // - Cancel all job children
            // - Wait for all children to complete
            // - Then complete exceptionally
            
            context.job.completeExceptionally(exn);
        }
    }
}