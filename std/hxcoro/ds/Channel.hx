package hxcoro.ds;

import haxe.coro.IContinuation;
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
		switch suspendedReads.shift() {
			case null:
				if (writeQueue.length < maxQueueSize) {
					writeQueue.push(v);
				} else {
					suspend(cont -> {
						suspendedWrites.push({v: v, cont: cont});
					});
				}
			case cont:
				cont.resume(v, null);
		}
	}

	/**
		Reads an element from this channel. If the operation cannot be completed immediately,
		execution is suspended. It can be resumed by a later call to `write`.
	**/
	@:coroutine public function read():T {
		while (writeQueue.length < maxQueueSize && suspendedWrites.length > 0) {
			final write = suspendedWrites.shift();
			write.cont.resume(null, null);
			if (writeQueue.length == 0) {
				return write.v;
			} else {
				writeQueue.push(write.v);
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
}
