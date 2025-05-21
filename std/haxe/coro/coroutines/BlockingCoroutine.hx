package haxe.coro.coroutines;

import haxe.coro.context.Context;
import haxe.coro.scopes.DefaultScopeComponent;
import haxe.CallStack.StackItem;
import haxe.coro.schedulers.EventLoopScheduler;

class BlockingCoroutine<T> extends BaseCoroutine<T> {
	final loop : EventLoop;

	public function new(loop : EventLoop) {
		super(Context.create(new DefaultScopeComponent(), new EventLoopScheduler(loop), new BaseContinuation.StackTraceManager()));

		this.loop = loop;

		error = null;
	}

	public function wait():T {
		while (loop.tick() || (state != Completed && state != Cancelled)) {
			// Busy wait
		}

		if (error != null) {
			throw error;
		} else {
			return result;
		}
	}
}