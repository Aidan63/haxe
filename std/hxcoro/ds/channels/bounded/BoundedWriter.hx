package hxcoro.ds.channels.bounded;

import haxe.coro.IContinuation;
import hxcoro.ds.Out;
import hxcoro.ds.channels.Channel;
import hxcoro.exceptions.ChannelClosedException;

using hxcoro.util.Convenience;

final class BoundedWriter<T> implements IChannelWriter<T> {
	final closed : Out<Bool>;

	final buffer : Array<T>;

	final maxBufferSize : Int;

	final writeWaiters : PagedDeque<IContinuation<Bool>>;

	final readWaiters : PagedDeque<IContinuation<Bool>>;

	final behaviour : FullBehaviour<T>;

	public function new(buffer, maxBufferSize, writeWaiters, readWaiters, closed, behaviour) {
		this.buffer        = buffer;
		this.maxBufferSize = maxBufferSize;
		this.writeWaiters  = writeWaiters;
		this.readWaiters   = readWaiters;
		this.closed        = closed;
		this.behaviour     = behaviour;
	}

	public function tryWrite(v:T):Bool {
		if (closed.get()) {
			return false;
		}

		return if (buffer.length < maxBufferSize) {
			buffer.push(v);

			final cont = new Out();
			while (readWaiters.tryPop(cont)) {
				cont.get().succeedAsync(true);
			}

			true;
		} else {
			false;
		}
	}

	@:coroutine public function write(v:T) {
		if (tryWrite(v)) {
			return;
		}

		switch behaviour {
			case Wait:
				while (waitForWrite()) {
					if (tryWrite(v)) {
						return;
					}
				}
			case DropNewest(f):
				while (tryWrite(v) == false) {
					f(buffer.pop());
				}

				return;
			case DropOldest(f):
				while (tryWrite(v) == false) {
					f(buffer.shift());
				}
				
				return;
			case DropWrite(f):
				f(v);

				return;
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
