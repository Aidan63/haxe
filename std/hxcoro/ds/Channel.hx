package hxcoro.ds;

import haxe.coro.IContinuation;
import haxe.coro.Mutex;
import hxcoro.Coro.suspend;

@:structInit
private class SuspendedWrite<T> {
	public final v:T;
	public final cont:IContinuation<T>;
}

/**
	A Channel is a queue with asynchronous `read` and `write` operations that are thread-safe.

	If such an operation cannot be fulfilled immediately, execution is suspended. It can be resumed
	from a later call to `read` or `write.
**/
class Channel<T> {
	final lock = new Mutex();

	final maxQueueSize = 3;

	final writeQueue = new Array<T>();

	final suspendedWrites = new Array<SuspendedWrite<Any>>();

	final suspendedReads = new Array<IContinuation<T>>();

	/**
		Creates a new empty Channel.
	**/
	public function new() {}

	/**
		Writes `v` to this channel. If the operation cannot be completed immediately, execution is
		suspended. It can be resumed by a later call to `read`.
	**/
	@:coroutine public function write(v:T) {
		lock.acquire();

		switch suspendedReads.shift() {
			case null:
				if (writeQueue.length < maxQueueSize) {
					writeQueue.push(v);
					lock.release();
				} else {
					lock.release();
					suspend(cont -> {
						suspendedWrites.push({v: v, cont: cont});
					});
				}
			case cont:
				lock.release();
				cont.resume(v, null);
		}
	}

	/**
		Reads an element from this channel. If the operation cannot be completed immediately,
		execution is suspended. It can be resumed by a later call to `write`.
	**/
	@:coroutine public function read():T {
		lock.acquire();

		while (writeQueue.length < maxQueueSize && suspendedWrites.length > 0) {
			final write = suspendedWrites.shift();
			lock.acquire();
			writeQueue.push(write.v);
			lock.release();
			write.cont.resume(null, null);
		}

		switch writeQueue.shift() {
			case null:
				lock.release();
				return suspend(cont -> {
					lock.acquire();
					suspendedReads.push(cont);
					lock.release();
				});
			case v:
				lock.release();
				return v;
		}
	}
}
