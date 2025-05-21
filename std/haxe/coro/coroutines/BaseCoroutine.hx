package haxe.coro.coroutines;

import haxe.exceptions.CancellationException;
import haxe.CallStack;
import haxe.coro.schedulers.Scheduler;
import haxe.coro.context.IElement;
import haxe.coro.context.Context;
import haxe.coro.scopes.ScopeComponent;

private enum abstract CoroutineState(Int) {
    final Running;
    final Completing;
    final Completed;
	final Cancelling;
	final Cancelled;
}

abstract class BaseCoroutine<T> implements IElement<ICoroutine<Any>> implements ICoroutine<T> implements ICoroutineScope implements IContinuation<T> {
	public final context : Context;

	public var isRunning (get, never) : Bool;

	public var isCancelled (get, never) : Bool;

	public var isCompleted (get, never) : Bool;

	public var result : T;

	public var error : Exception;

	public var state : CoroutineState;

	final children : Array<ChildCoroutine<Any>>;

	final completionCallbacks : Array<()->Void>;

	var completedChildren : Int;

	public function new(context : Context) {
		this.context  = context;
		this.children = [];

		completionCallbacks = [];
		completedChildren   = 0;
		state               = Running;
	}

	@:coroutine public function await() : T {
		return Coroutine.suspend(cont -> {
			switch state {
				case Completed:
					cont.resume(result, null);
				case Cancelled:
					cont.resume(null, error);
				case _:
					completionCallbacks.push(() -> {
						if (error != null) {
							cont.resume(null, error);
						} else {
							cont.resume(result, null);
						}
					});
			}
        });
	}

	public function resume(result : T, error : Exception) : Void {
		switch error {
			case null:
				complete(result);
			case _:
				completeExceptionally(error);
		}
	}

	public function child<T>() {
		final coroutine = new ChildCoroutine<T>(context);

		coroutine.onCompletion(() -> {
			completedChildren++;
		});

		children.push(coroutine);

		return coroutine;
	}

	public function start<T>(c : Coroutine<ICoroutineScope->T>) : ICoroutine<T> {
		final coroutine : ChildCoroutine<T> = child();

		coroutine.onCompletion(() -> context.get(ScopeComponent.key).onCompletion(this, coroutine));

		coroutine.context.get(Scheduler.key).schedule(() -> {
			// TODO: are we potentially ereasing a stack track here?
			// would it be better to have the coroutine function pre-amble to check this and error "normally"?
			if (coroutine.isCancelled) {
				coroutine.completeExceptionally(coroutine.error);

				return;
			}

			final result = c(coroutine, coroutine);

			switch result.state {
				case Pending:
					return;
				case Returned:
					coroutine.complete(result.result);
				case Thrown:
					coroutine.completeExceptionally(result.error);
			}
		});

		return coroutine;
	}

	public function onCompletion(c : ()->Void) {
		switch state {
			case Completed, Cancelled:
				c();
			case _:
				completionCallbacks.push(c);
		}
	}

	public function cancel() {
		context.get(ScopeComponent.key).cancel(this);
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

	public function completeExceptionally(error : Exception) {
		this.error  = error;

		if (children.length == 0 || children.length == completedChildren) {
			state = Cancelled;

			for (callback in completionCallbacks) {
				callback();
			}
		}
		else {
			state = Cancelling;

			for (child in children) {
				child.cancel();
			}
		}
	}

	function get_isRunning() {
		return state == Running;
	}

	function get_isCancelled() {
		return state == Cancelling || state == Cancelled;
	}

	function get_isCompleted() {
		return state == Completed || state == Cancelled;
	}
}