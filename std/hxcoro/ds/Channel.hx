package hxcoro.ds;

import haxe.Exception;
import haxe.exceptions.CancellationException;
import haxe.coro.cancellation.CancellationToken;
import haxe.coro.cancellation.ICancellationHandle;
import haxe.coro.context.Context;
import haxe.coro.IContinuation;
import hxcoro.Coro.suspend;
import hxcoro.ds.PagedDeque;

private class SuspendedWrite<T> implements IContinuation<T> {
	final continuation : IContinuation<T>;
	final handle : ICancellationHandle;

	public final value : T;

	public var context (get, never) : Context;

	var hostPage:Page<Any>;
	var hostIndex:Int;

	inline function get_context() {
		return continuation.context;
	}

	public function new(continuation, value, suspendedWrites:PagedDeque<Any>) {
		this.continuation = continuation;
		this.value        = value;
		this.handle       = context.get(CancellationToken.key).onCancellationRequested(onCancellation);
		// writeMutex.acquire();
		hostPage = suspendedWrites.push(this);
		hostIndex = suspendedWrites.lastIndex - 1;
		// writeMutex.release();
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
		// writeMutex.acquire();
		if (hostPage.data[hostIndex] == this) {
			hostPage.data[hostIndex] = null;
		}
		// writeMutex.release();
		resume(null, null);
	}
}

private class SuspendedRead<T> implements IContinuation<T> {
	final continuation : IContinuation<T>;
	final handle : ICancellationHandle;

	public var context (get, never) : Context;

	var hostPage:Page<Any>;
	var hostIndex:Int;

	inline function get_context() {
		return continuation.context;
	}

	public function new(continuation, suspendedReads:PagedDeque<Any>) {
		this.continuation = continuation;
		this.handle       = context.get(CancellationToken.key).onCancellationRequested(onCancellation);

		// readMutex.acquire();
		hostPage = suspendedReads.push(this);
		hostIndex = suspendedReads.lastIndex - 1;
		// readMutex.release();
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
		// readMutex.acquire();
		if (hostPage.data[hostIndex] == this) {
			hostPage.data[hostIndex] = null;
		}
		// readMutex.release();
		resume(null, null);
		resume(null, null);
	}
}

class Channel<T> {
	final capacity : Int;
	final writeQueue : Array<T>;
	final suspendedWrites : PagedDeque<SuspendedWrite<T>>;
	final suspendedReads : PagedDeque<SuspendedRead<T>>;

	/**
		Creates a new empty Channel.
	**/
	public function new(capacity) {
		this.capacity = capacity;

		writeQueue      = [];
		suspendedWrites = new PagedDeque();
		suspendedReads  = new PagedDeque();
	}

	/**
		Writes `v` to this channel. If the operation cannot be completed immediately, execution is
		suspended. It can be resumed by a later call to `read`.
	**/
	@:coroutine public function write(v:T) {
		while (true) {
			if (suspendedReads.isEmpty()) {
				if (writeQueue.length < capacity) {
					writeQueue.push(v);
				} else {
					suspend(cont -> {
						new SuspendedWrite(cont, v, suspendedWrites);
					});
				}
				break;
			} else {
				final suspendedRead = suspendedReads.pop();
				if (suspendedRead == null) {
					continue;
				} else {
					suspendedRead.resume(v, null);
					break;
				}
			}
		}
	}

	/**
		Reads an element from this channel. If the operation cannot be completed immediately,
		execution is suspended. It can be resumed by a later call to `write`.
	**/
	@:coroutine public function read():T {
		while ((capacity == 0 || writeQueue.length < capacity) && !suspendedWrites.isEmpty()) {
			final resuming = suspendedWrites.pop();
			if (resuming == null) {
				continue;
			}
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
					new SuspendedRead(cont, suspendedReads);
				});
			case v:
				return v;
		}
	}
}
