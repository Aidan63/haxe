package haxe.coro.coroutines;

import haxe.coro.context.Context;
import haxe.CallStack.StackItem;
import haxe.coro.schedulers.EventLoopScheduler;

class BlockingCoroutine<T> extends BaseCoroutine<T> {
	final loop : EventLoop;

	public function new(loop : EventLoop) {
		super(Context.empty(), null);

		context.add(this);
		context.add(new EventLoopScheduler(loop));

		this.loop = loop;

		error = null;
	}

	public function wait():T {
		while (loop.tick() || (state != Completed && state != Cancelled)) {
			// Busy wait
		}

		if (error != null) {
			final coroStack = (cast result : Array<StackItem>) ?? [];
			final topStack = CallStackHelper.takeStackItemsUntil(error.stack.asArray(), coroStack[0]);
			final bottomStack = CallStack.callStack();
			error.stack = topStack.concat(coroStack).concat(bottomStack);
			throw error;
		} else {
			return result;
		}
	}
}