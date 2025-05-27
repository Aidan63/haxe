package haxe.coro.coroutines;

import haxe.coro.context.Context;
import haxe.coro.scopes.DefaultScopeComponent;
import haxe.CallStack.StackItem;
import haxe.coro.schedulers.EventLoopScheduler;

class BlockingCoroutine<T> extends BaseCoroutine<T> {
	final scheduler : EventLoopScheduler;

	public function new(scheduler : EventLoopScheduler) {
		super(Context.create(new DefaultScopeComponent(), scheduler, new BaseContinuation.StackTraceManager()));

		this.scheduler = scheduler;

		error = null;
	}

	public function wait():T {
		while (state != Completed && state != Cancelled) {
			scheduler.run();
		}

		if (error != null) {
			throw error;
		} else {
			return result;
		}
	}
}