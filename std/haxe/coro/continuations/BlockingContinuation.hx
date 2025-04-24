package haxe.coro.continuations;

class BlockingContinuation<T> implements IContinuation<T> {
	public final _hx_context:CoroutineContext;

	final loop:EventLoop;

	var running:Bool;
	var result:T;
	var error:Exception;

	public function new(loop, scheduler) {
		this.loop = loop;

		_hx_context = new CoroutineContext(scheduler);
		running = true;
		error = null;
	}

	public function resume(result:T, error:Exception) {
		running = false;

		this.result = result;
		this.error = error;
	}

	public function wait():T {
		while (loop.tick() || running) {
			// Busy wait
		}

		if (error != null) {
			trace((cast result : haxe.CallStack));

			throw new haxe.exceptions.CoroutineException(error.message, null, cast result, haxe.CallStack.callStack());
		} else {
			return result;
		}
	}
}
