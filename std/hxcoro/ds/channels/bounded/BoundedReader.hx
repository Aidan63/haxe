package hxcoro.ds.channels.bounded;

import haxe.ds.Vector;
import haxe.coro.IContinuation;
import hxcoro.ds.Out;
import hxcoro.exceptions.ChannelClosedException;

using hxcoro.util.Convenience;

class BoundedReader<T> implements IChannelReader<T> {
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

	public function tryRead(out:Out<T>):Bool {
		return if (buffer.length > 0) {
			out.set(buffer.shift());

			while (writeWaiters.isEmpty() == false) {
				switch writeWaiters.pop() {
					case null:
						continue;
					case cont:
						cont.succeedSync(true);
				}
			};

			true;
		} else {
			false;
		}
	}

	@:coroutine public function read():T {
		final out = new Out();

		while (true)
		{
			if (waitForRead() == false) {
				throw new ChannelClosedException();
			}

			if (tryRead(out)) {
				return out.get();
			}
		}
	}

	@:coroutine public function waitForRead():Bool {
		if (buffer.length > 0) {
			return true;
		}

		return suspendCancellable(cont -> {
			final hostPage  = readWaiters.push(cont);
			final hostIndex = readWaiters.lastIndex - 1;

			cont.onCancellationRequested = _ -> {
				final data:Vector<Any> = hostPage.data;
				if (data[hostIndex] == cont) {
					data[hostIndex] = null;
				}
			}
		});
	}
}