package haxe.coro.continuations;

import haxe.coro.context.CoroutineContext;

class BlockingContinuation implements IContinuation<Any> {
	public final _hx_context:CoroutineContext;

	final loop:EventLoop;

	var running:Bool;
	var result:Any;
	var error:Exception;

	public function new(loop : EventLoop, scheduler : Scheduler) {
		this.loop = loop;

		_hx_context = CoroutineContext.empty + scheduler;
		running = true;
		result = 0;
		error = null;
	}

	public function resume(result:Any, error:Exception) {
		running = false;

		this.result = result;
		this.error = error;
	}

	public function wait():Any {
		while (loop.tick()) {
			// Busy wait
		}

		if (error != null) {
			throw error;
		} else {
			return cast result;
		}
	}
}
