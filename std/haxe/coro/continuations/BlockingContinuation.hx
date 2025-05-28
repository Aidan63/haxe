package haxe.coro.continuations;

import haxe.CallStack;
import haxe.coro.context.Context;
import haxe.coro.schedulers.EventLoopScheduler;

class BlockingContinuation<T> implements IContinuation<T> {
	public final context:Context;

	final scheduler:EventLoopScheduler;

	var running:Bool;
	var result:T;
	var error:Exception;

	public function new(scheduler:EventLoopScheduler) {
		this.scheduler = scheduler;

		context = Context.create(scheduler, new BaseContinuation.StackTraceManager());
		running = true;
		error   = null;
	}

	public function resume(result:T, error:Exception) {
		running = false;

		this.result = result;
		this.error = error;
	}

	public function wait():T {
		while (running) {
			scheduler.run();
		}

		if (error != null) {
			throw error;
		} else {
			return result;
		}
	}
}
