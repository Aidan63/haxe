package hxcoro.ds;

import haxe.Exception;
import haxe.exceptions.CancellationException;
import haxe.coro.cancellation.CancellationToken;
import haxe.coro.cancellation.ICancellationHandle;
import haxe.coro.context.Context;
import haxe.coro.IContinuation;
import hxcoro.Coro.suspend;

private class SuspendedWrite<T> implements IContinuation<T> {
	final continuation : IContinuation<T>;
	final callback : (self:SuspendedWrite<T>)->Void;
	final handle : ICancellationHandle;

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

private class SuspendedRead<T> implements IContinuation<T> {
	final continuation : IContinuation<T>;
	final callback : (self:SuspendedRead<T>)->Void;
	final handle : ICancellationHandle;

	public var context (get, never) : Context;

	inline function get_context() {
		return continuation.context;
	}

	public function new(continuation, callback) {
		this.continuation = continuation;
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
	final suspendedReads : Array<SuspendedRead<T>>;

	/**
		Creates a new empty Channel.
	**/
	public function new(capacity) {
		this.capacity = capacity;

		writeQueue      = [];
		suspendedWrites = [];
		suspendedReads  = [];
	}

	/**
		Writes `v` to this channel. If the operation cannot be completed immediately, execution is
		suspended. It can be resumed by a later call to `read`.
	**/
	@:coroutine public function write(v:T) {
		if (suspendedReads.length == 0) {
			if (writeQueue.length < capacity) {
				writeQueue.push(v);
			} else {
				suspend(cont -> {
					suspendedWrites.push(new SuspendedWrite(cont, v, removeSuspendedWrite));
				});
			}
		} else {
			suspendedReads.shift().resume(v, null);
		}
	}

	/**
		Reads an element from this channel. If the operation cannot be completed immediately,
		execution is suspended. It can be resumed by a later call to `write`.
	**/
	@:coroutine public function read():T {
		while ((capacity == 0 || writeQueue.length < capacity) && suspendedWrites.length > 0) {
			final resuming = suspendedWrites.shift();
			resuming.resume(null, null);
			if (writeQueue.length == 0) {
				return resuming.value;
			} else {
				writeQueue.push(resuming.value);
			}
		}
		switch writeQueue.shift() {
			case null:
				return suspend(cont -> {
					suspendedReads.push(new SuspendedRead(cont, removeSuspendedRead));
				});
			case v:
				return v;
		}
	}

	function removeSuspendedWrite(write:SuspendedWrite<T>) {
		suspendedWrites.remove(write);
	}

	function removeSuspendedRead(read:SuspendedRead<T>) {
		suspendedReads.remove(read);
	}
}
