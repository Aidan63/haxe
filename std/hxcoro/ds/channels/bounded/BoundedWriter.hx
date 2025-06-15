package hxcoro.ds.channels.bounded;

import haxe.ds.Vector;
import haxe.coro.IContinuation;
import hxcoro.exceptions.ChannelClosedException;

using hxcoro.util.Convenience;

final class BoundedWriter<T> implements IChannelWriter<T> {
	var closed : Bool;

	final buffer : Array<T>;

	final maxBufferSize : Int;

	final writeWaiters : PagedDeque<IContinuation<Bool>>;

	final readWaiters : PagedDeque<IContinuation<Bool>>;

	public function new(buffer, maxBufferSize, writeWaiters, readWaiters) {
		this.buffer        = buffer;
		this.maxBufferSize = maxBufferSize;
		this.writeWaiters  = writeWaiters;
		this.readWaiters   = readWaiters;
	}

	public function tryWrite(v:T):Bool {
		if (closed) {
			return false;
		}

		return if (buffer.length < maxBufferSize) {
			buffer.push(v);

			while (readWaiters.isEmpty() == false) {
				switch (readWaiters.pop()) {
					case null:
						continue;
					case cont:		
						cont.succeedAsync(true);
				}
			};

			true;
		} else {
			false;
		}
	}

	@:coroutine public function write(v:T) {
		while (waitForWrite()) {
			if (tryWrite(v)) {
				return;
			}
		}

		throw new ChannelClosedException();
	}

	@:coroutine public function waitForWrite():Bool {
		if (closed) {
			return false;
		}

		return if (buffer.length < maxBufferSize) {
			true;
		} else {
			return suspendCancellable(cont -> {
				final hostPage  = writeWaiters.push(cont);
				final hostIndex = writeWaiters.lastIndex - 1;

				cont.onCancellationRequested = _ -> {
					final data:Vector<Any> = hostPage.data;
					if (data[hostIndex] == cont) {
						data[hostIndex] = null;
					}
				}
			});
		}
	}

	public function close() {
		if (closed) {
			return;
		}

		closed = true;

		while (writeWaiters.isEmpty() == false) {
			switch writeWaiters.pop() {
				case null:
					continue;
				case cont:
					cont.succeedAsync(false);
			}
		};

		while (readWaiters.isEmpty() == false) {
			switch (readWaiters.pop()) {
				case null:
					continue;
				case cont:		
					cont.succeedAsync(false);
			}
		};
	}
}
