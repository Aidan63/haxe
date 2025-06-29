package hxcoro.ds.channels.bounded;

import haxe.Exception;
import haxe.coro.IContinuation;
import haxe.coro.context.Context;
import hxcoro.ds.Out;
import hxcoro.exceptions.ChannelClosedException;

using hxcoro.util.Convenience;

private final class WaitContinuation<T> implements IContinuation<Bool> {
	final cont : IContinuation<Bool>;

	final buffer : Array<T>;

	final closed : Out<Bool>;

	public var context (get, never) : Context;

	function get_context() {
		return cont.context;
	}

	public function new(cont, buffer, closed) {
		this.cont   = cont;
		this.buffer = buffer;
		this.closed = closed;
	}

	public function resume(result:Bool, error:Exception) {
		if (false == result) {
			closed.set(false);

			cont.succeedAsync(buffer.length == 0);
		} else {
			cont.succeedAsync(true);
		}
	}
}

final class BoundedReader<T> implements IChannelReader<T> {
	final buffer : Array<T>;

	final maxBufferSize : Int;

	final writeWaiters : PagedDeque<IContinuation<Bool>>;

	final readWaiters : PagedDeque<IContinuation<Bool>>;

	final closed : Out<Bool>;

	public function new(buffer, maxBufferSize, writeWaiters, readWaiters, closed) {
		this.buffer        = buffer;
		this.maxBufferSize = maxBufferSize;
		this.writeWaiters  = writeWaiters;
		this.readWaiters   = readWaiters;
		this.closed        = closed;
	}

	public function tryRead(out:Out<T>):Bool {
		return if (buffer.length > 0) {
			out.set(buffer.shift());

			final cont = new Out();
			while (writeWaiters.tryPop(cont)) {
				cont.get().succeedAsync(true);
			}

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

		if (closed.get()) {
			return false;
		}

		return suspendCancellable(cont -> {
			final obj       = new WaitContinuation(cont, buffer, closed);
			final hostPage  = readWaiters.push(obj);

			cont.onCancellationRequested = _ -> {
				readWaiters.remove(hostPage, obj);
			}
		});
	}
}