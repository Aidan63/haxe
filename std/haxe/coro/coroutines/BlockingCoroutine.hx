package haxe.coro.coroutines;

import haxe.coro.context.Context;
import haxe.coro.scopes.DefaultScopeComponent;
import haxe.coro.Coroutine;
import haxe.CallStack.StackItem;
import haxe.coro.schedulers.EventLoopScheduler;

class BlockingCoroutine<T> extends BaseCoroutine<T> {
	final loop : EventLoop;

	public function new(loop : EventLoop, lambda : ScopedCoroutine<T>) {
		super(Context.create(new DefaultScopeComponent(), new EventLoopScheduler(loop), new BaseContinuation.StackTraceManager()), lambda);

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