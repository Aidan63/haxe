package haxe.coro.coroutines;

import haxe.CallStack;
import haxe.coro.schedulers.Scheduler;
import haxe.coro.context.IElement;
import haxe.coro.context.Context;
import haxe.exceptions.NotImplementedException;

private enum abstract CoroutineState(Int) {
    final Running;
    final Completing;
    final Completed;
	final Cancelling;
	final Cancelled;
}

abstract class BaseCoroutine<T> implements IElement<ICoroutine<Any>> implements ICoroutine<T> implements ICoroutineScope implements IContinuation<T> {
	public final context : Context;

	public final parent : Null<ICoroutine<Any>>;

	public final children : Array<ICoroutine<Any>>;

	final completionCallbacks : Array<()->Void>;

	var result : T;

	public var error : Exception;

	public var state : CoroutineState;

	var completedChildren : Int;

	public function new(context : Context, parent : Null<ICoroutine<Any>>) {
		this.context  = context;
		this.parent   = parent;
		this.children = [];

		completionCallbacks = [];
		completedChildren   = 0;
		state               = Running;
	}

	@:coroutine public function await() : T {
		return Coroutine.suspend(cont -> {
            if (state == Completed) {
                cont.resume(result, null);
            } else {
                completionCallbacks.push(() -> cont.resume(result, null));
            }
        });
	}

	public function resume(result : T, error : Exception) : Void {
		switch error {
			case null:
				complete(result);
			case _:
				completeExceptionally(error, cast result);
		}
	}

	public function start<T>(c : Coroutine<ICoroutineScope->T>) : ICoroutine<T> {
		final coroutine = new ChildCoroutine<T>(context);

		children.push(coroutine);

		coroutine.onCompletion(onChildCompleted.bind(coroutine));
		coroutine.context.get(Scheduler.key).schedule(() -> {
			final result = c(coroutine, coroutine);

			switch result.state {
				case Pending:
					return;
				case Returned:
					coroutine.complete(result.result);
				case Thrown:
					coroutine.completeExceptionally(result.error, cast result.result);
			}
		});

		return coroutine;
	}

	public function onCompletion(c : ()->Void) {
		completionCallbacks.push(c);
	}

	public function cancel(cause : Exception) {
		completeExceptionally(cause, []);
	}

	public function toString() {
		return 'Coroutine';
	}

	public function getKey() {
		return Coroutine.key;
	}

	public function complete(result : T) {
		this.result = result;

		if (children.length == 0 || children.length == completedChildren) {
			state = Completed;

			for (callback in completionCallbacks) {
				callback();
			}
		} else {
			state = Completing;
		}
	}

	public function completeExceptionally(error : Exception, stack:Array<StackItem>) {
		this.error = error;
		this.result = cast stack;

		if (children.length == 0 || children.length == completedChildren)
		{
			state = Cancelled;

			for (callback in completionCallbacks) {
				callback();
			}
		}
		else
		{
			state = Cancelling;
		}
	}

	function onChildCompleted(completed : ChildCoroutine<Any>) {
		completedChildren++;

		switch state {
			case Completing if (completed.state == Completed):
				complete(result);
			case Completing if (completed.state == Cancelled):
				completeExceptionally(completed.error, completed.result);
			case _:
				throw new Exception("Unexpected coroutine state");
		}
	}
}