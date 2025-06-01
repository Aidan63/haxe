package hxcoro.ds;

import haxe.Exception;
import haxe.exceptions.CancellationException;
import haxe.coro.cancellation.CancellationToken;
import haxe.coro.cancellation.ICancellationHandle;
import haxe.coro.context.Context;
import haxe.coro.IContinuation;
import hxcoro.Coro.suspend;

private class SuspendedWrite<T> implements IContinuation<T> {
	final handle : ICancellationHandle;
	final callback : (self:SuspendedWrite<T>)->Void;
	public final continuation : IContinuation<T>;
	public final value : T;

	public var context (get, never) : Context;

	inline function get_context() {
		return continuation.context;
	}

	public function new(continuation, value, callback) {
		this.continuation = continuation;
		this.value        = value;
		this.callback     = callback;
		this.handle       = context.get(CancellationToken.key).onCancellationRequested(onCancellation);
	}

	public function resume(v:T, error:Exception) {
		handle.close();
		if (context.get(CancellationToken.key).isCancellationRequested) {
			continuation.resume(null, new CancellationException());
		} else {
			continuation.resume(v, error);
		}
	}

	function onCancellation() {
		callback(this);
		resume(null, null);
	}
}

class Channel<T> {
	final capacity : Int;
	final writeQueue : Array<T>;
	final suspendedWrites : Array<SuspendedWrite<T>>;
	final suspendedReads :  PagedDeque<IContinuation<T>>;

	/**
		Creates a new empty Channel.
	**/
	public function new(capacity) {
		this.capacity = capacity;

		writeQueue      = [];
		suspendedWrites = [];
		suspendedReads  = new PagedDeque();
	}

	/**
		Writes `v` to this channel. If the operation cannot be completed immediately, execution is
		suspended. It can be resumed by a later call to `read`.
	**/
	@:coroutine public function write(v:T) {
		if (suspendedReads.isEmpty()) {
			if (writeQueue.length < capacity) {
				writeQueue.push(v);
			} else {
				suspend(cont -> {
					suspendedWrites.push(new SuspendedWrite(cont, v, removeSuspendedWrite));
				});
			}
		} else {
			suspendedReads.pop().resume(v, null);
		}
	}

	/**
		Reads an element from this channel. If the operation cannot be completed immediately,
		execution is suspended. It can be resumed by a later call to `write`.
	**/
	@:coroutine public function read():T {
		while ((capacity == 0 || writeQueue.length < capacity) && suspendedWrites.length > 0) {
			final resuming = suspendedWrites.shift();
			resuming.continuation.resume(null, null);
			if (writeQueue.length == 0) {
				return resuming.value;
			} else {
				writeQueue.push(resuming.value);
			}
		}
		switch writeQueue.shift() {
			case null:
				return suspend(cont -> {
					suspendedReads.push(cont);
				});
			case v:
				return v;
		}
	}

	function removeSuspendedWrite(write:SuspendedWrite<T>) {
		suspendedWrites.remove(write);
	}
}
