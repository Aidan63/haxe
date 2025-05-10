package haxe.coro.continuations;

import haxe.exceptions.NotImplementedException;
import haxe.Exception;
import haxe.coro.IContinuation;

class JobContinuation<T> implements IContinuation<T> {
    public final context:CoroutineContext;

    public function new(context) {
        this.context = context;
    }

    public function resume(v:T, exn:Exception) {
        if (exn == null) {
            context.job.complete(v);
        } else {
            throw new NotImplementedException();
        }
    }
}