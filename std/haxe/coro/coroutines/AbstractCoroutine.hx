package haxe.coro.coroutines;

import haxe.exceptions.NotImplementedException;

private enum abstract JobState(Int) {
    final Running;
    final AwaitingChildren;
    final Completed;
}

abstract class AbstractCoroutine<T> implements ICoroutine<T> implements ICoroutineScope implements IContinuation<T> {
	public final context : CoroutineContext;

	public final parent : Null<ICoroutine<Any>>;

	public final children : Array<ICoroutine<Any>>;

	final completionCallbacks : Array<()->Void>;

	var result : T;

	var state : JobState;

	var completedChildren : Int;

	public function new(context, parent) {
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
		coroutine.context.scheduler.schedule(() -> {
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