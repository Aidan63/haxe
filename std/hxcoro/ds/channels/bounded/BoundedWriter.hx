package hxcoro.ds.channels.bounded;

import haxe.ds.Vector;
import haxe.coro.IContinuation;
import hxcoro.ds.Out;
import hxcoro.exceptions.ChannelClosedException;

using hxcoro.util.Convenience;

class BoundedWriter<T> implements IChannelWriter<T> {
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
		return if (buffer.length < maxBufferSize) {
			buffer.push(v);

			while (readWaiters.isEmpty() == false) {
				switch (readWaiters.pop()) {
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

	@:coroutine public function write(v:T) {
		while (waitForWrite()) {
			if (tryWrite(v)) {
				return;
			}
		}

		throw new ChannelClosedException();
	}

	@:coroutine public function waitForWrite():Bool {
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
}
