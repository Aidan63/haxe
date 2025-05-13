package haxe.coro;

import haxe.exceptions.NotImplementedException;

interface ICoroutine {
	final parent : Null<ICoroutine>;

	final children : Array<ICoroutine>;

	@:coroutine function await() : Void;
}

interface ICoroutineScope {
	final context : CoroutineContext;

	function start(c:Coroutine<ICoroutineScope->Void>):ICoroutine;
}

private enum abstract JobState(Int) {
    final Running;
    final AwaitingChildren;
    final Completed;
}

abstract class AbstractCoroutine<T> implements ICoroutine implements ICoroutineScope implements IContinuation<T> {
	public final context : CoroutineContext;

	public final parent : Null<ICoroutine>;

	public final children : Array<ICoroutine>;

	final completionCallbacks : Array<()->Void>;

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

	@:coroutine public function await() : Void {
		Coroutine.suspend(cont -> {
            if (state == Completed) {
                cont.resume(null, null);
            } else {
                completionCallbacks.push(() -> cont.resume(null, null));
            }
        });
	}

	public function resume(result : T, error : Exception) : Void {
		switch error {
			case null:
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

	public function start(c : Coroutine<ICoroutineScope->Void>) : ICoroutine {
		final coroutine = new ChildCoroutine(context);

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

class ChildCoroutine extends AbstractCoroutine<Any> {
	public function new(parentContext : CoroutineContext) {
		super(new CoroutineContext(parentContext.scheduler, this), parentContext.coroutine);
	}
}