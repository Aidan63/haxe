package hxcoro.continuations;

import haxe.exceptions.CancellationException;
import haxe.coro.cancellation.ICancellationHandle;
import haxe.coro.cancellation.CancellationToken;
import haxe.Exception;
import haxe.coro.context.Context;
import haxe.coro.IContinuation;
import haxe.coro.ICancellingContinuation;

class CancellingContinuation<T> implements ICancellingContinuation<T> {
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
		return onCancellationRequested = f;
	}

	public function new(cont) {
		this.cont   = cont;
		this.handle = this.cont.context.get(CancellationToken.key).onCancellationRequested(doCancellation);
	}

	public function resume(result:T, error:Exception) {
		if (this.cont.context.get(CancellationToken.key).isCancellationRequested) {
			cont.resume(null, new CancellationException());
		} else {
			cont.resume(result, error);
		}

	}

	function doCancellation() {
		if (null != onCancellationRequested) {
			onCancellationRequested();
		}

		resume(null, null);
	}
}