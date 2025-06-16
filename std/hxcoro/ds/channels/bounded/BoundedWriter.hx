package hxcoro.ds.channels.bounded;

import haxe.ds.Vector;
import haxe.coro.IContinuation;
import hxcoro.exceptions.ChannelClosedException;
import hxcoro.ds.Out;

using hxcoro.util.Convenience;

final class BoundedWriter<T> implements IChannelWriter<T> {
	var closed : Out<Bool>;

	final buffer : Array<T>;

	final maxBufferSize : Int;

	final writeWaiters : PagedDeque<IContinuation<Bool>>;

	final readWaiters : PagedDeque<IContinuation<Bool>>;

	public function new(buffer, maxBufferSize, writeWaiters, readWaiters, closed) {
		this.buffer        = buffer;
		this.maxBufferSize = maxBufferSize;
		this.writeWaiters  = writeWaiters;
		this.readWaiters   = readWaiters;
		this.closed        = closed;
	}

	public function tryWrite(v:T):Bool {
		if (closed.get()) {
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
		if (closed.get()) {
			return false;
		}

		return if (buffer.length < maxBufferSize) {
			true;
		} else {
			return suspendCancellable(cont -> {
				final hostPage  = writeWaiters.push(cont);

				cont.onCancellationRequested = _ -> {
					writeWaiters.remove(hostPage, cont);
				}
			});
		}
	}

	public function close() {
		if (closed.get()) {
			return;
		}

		closed.set(true);

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
