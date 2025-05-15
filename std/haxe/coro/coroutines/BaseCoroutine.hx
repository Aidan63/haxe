package haxe.coro.coroutines;

import haxe.coro.schedulers.Scheduler;
import haxe.coro.context.IElement;
import haxe.coro.context.Context;
import haxe.exceptions.NotImplementedException;

private enum abstract CoroutineState(Int) {
    final Running;
    final AwaitingChildren;
    final Completed;
}

abstract class BaseCoroutine<T> implements IElement<ICoroutine<Any>> implements ICoroutine<T> implements ICoroutineScope implements IContinuation<T> {
	public final context : Context;

	public final parent : Null<ICoroutine<Any>>;

	public final children : Array<ICoroutine<Any>>;

	final completionCallbacks : Array<()->Void>;

	var result : T;

	var state : CoroutineState;

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
				this.result = result;

				if (children.length == 0 || children.length == completedChildren) {
					state = Completed;

					for (callback in completionCallbacks) {
						callback();
					}
				} else {
					state = AwaitingChildren;
				}
			case _:
				throw new NotImplementedException();
		}
	}

	public function start<T>(c : Coroutine<ICoroutineScope->T>) : ICoroutine<T> {
		final coroutine = new ChildCoroutine<T>(context);

		children.push(coroutine);

		coroutine.onCompletion(onChildCompleted);
		coroutine.context.get(Scheduler.key).schedule(() -> {
			final result = c(coroutine, coroutine);

			switch result.state {
				case Pending:
					return;
				case Returned:
					coroutine.resume(result.result, null);
				case Thrown:
					coroutine.resume(null, result.error);
			}
		});

		return coroutine;
	}

	public function onCompletion(c : ()->Void) {
		completionCallbacks.push(c);
	}

	public function toString() {
		return 'Coroutine';
	}

	public function getKey() {
		return Coroutine.key;
	}

	function onChildCompleted() {
		completedChildren++;

		if (state == AwaitingChildren && children.length == completedChildren) {
			state = Completed;

			for (callback in completionCallbacks) {
				callback();
			}
		}
	}
}