package haxe.coro.coroutines;

import haxe.coro.context.Context;
import haxe.CallStack.StackItem;
import haxe.coro.schedulers.EventLoopScheduler;

class BlockingCoroutine<T> extends BaseCoroutine<T> {
	final loop : EventLoop;

	var error : Exception;

	public function new(loop : EventLoop) {
		super(Context.empty(), null);

		context.add(this);
		context.add(new EventLoopScheduler(loop));

		this.loop = loop;

		error = null;
	}

	public function wait():T {
		while (loop.tick() || state != Completed) {
			// Busy wait
		}

		if (error != null) {
			final topStack = [];
			for (item in error.stack.asArray()) {
				switch (item) {
					// TODO: this needs a better check
					case FilePos(_, _, -1, _):
						break;
					// this is a hack
					case FilePos(Method(_, "invokeResume"), _):
						break;
					case _:
						topStack.push(item);
				}
			}
			final coroStack = (cast result : Array<StackItem>) ?? [];
			final bottomStack = CallStack.callStack();
			error.stack = topStack.concat(coroStack).concat(bottomStack);
			throw error;
		} else {
			return result;
		}
	}
}