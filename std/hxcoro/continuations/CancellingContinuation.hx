package hxcoro.continuations;

import haxe.Exception;
import haxe.exceptions.CancellationException;
import haxe.coro.IContinuation;
import haxe.coro.ICancellingContinuation;
import haxe.coro.context.Context;
import haxe.coro.schedulers.Scheduler;
import haxe.coro.cancellation.ICancellationHandle;
import haxe.coro.cancellation.CancellationToken;
import haxe.coro.cancellation.ICancellationCallback;

class CancellingContinuation<T> implements ICancellingContinuation<T> implements ICancellationCallback {
	final cont : IContinuation<T>;

	final handle : ICancellationHandle;

	public var context (get, never) : Context;

	function get_context() {
		return cont.context;
	}

	public var onCancellationRequested (null, set) : ()->Void;

	function get_onCancellationRequested() {
		return onCancellationRequested;
	}

	function set_onCancellationRequested(f : ()->Void) {
		return if (cont.context.get(CancellationToken.key).isCancellationRequested) {
			f();

			f;
		} else {
			onCancellationRequested = f;
		}

	}

	public function new(cont) {
		this.cont   = cont;
		this.handle = this.cont.context.get(CancellationToken.key).onCancellationRequested(this);
	}

	public function resume(result:T, error:Exception) {
		handle.close();

		if (this.cont.context.get(CancellationToken.key).isCancellationRequested) {
			context.get(Scheduler.key).schedule(0, () -> {
				cont.resume(null, new CancellationException());
			});
		} else {
			context.get(Scheduler.key).schedule(0, () -> {
				cont.resume(result, error);
			});
		}

	}

	public function onCancellation() {
		if (null != onCancellationRequested) {
			onCancellationRequested();
		}

		resume(null, null);
	}
}