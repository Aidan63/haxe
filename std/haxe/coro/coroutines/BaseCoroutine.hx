package haxe.coro.coroutines;

import haxe.exceptions.CancellationException;
import haxe.CallStack;
import haxe.coro.schedulers.Scheduler;
import haxe.coro.context.IElement;
import haxe.coro.context.Context;
import haxe.coro.scopes.ScopeComponent;
import haxe.coro.Coroutine;

private enum abstract CoroutineState(Int) {
	/**
		The coroutine itself is still running.
	**/
	final Created;
	/**
		The coroutine itself is still running.
	**/
    final Running;
	/**
		The coroutine itself has completed, but some of its children are still running.
	**/
    final Completing;
	/**
		The coroutine itself and all of its children are completed.
	**/
    final Completed;
	/**
		The coroutine itself has been cancelled, but some of its children are still running.
	**/
	final Cancelling;
	/**
		The coroutine itself and all of its children have been cancelled.
	**/
	final Cancelled;
}

class AdjustedContext<T> implements ICoroutineScope {
	public final context:Context;
	final coroutine:BaseCoroutine<T>;

	public function new(context:Context, coroutine:BaseCoroutine<T>) {
		this.context = context;
		this.coroutine = coroutine;
	}

	@:access(haxe.coro.coroutines.BaseCoroutine)
	public function start<T>(c:Coroutine<ICoroutineScope->T>):ICoroutine<T> {
		return coroutine.startChild(coroutine.child(context, c));
	}

	public function with(...elements:IElement<Any>) {
		return new AdjustedContext(context.clone().with(...elements), coroutine);
	}
}

class BaseCoroutine<T> implements IElement<ICoroutine<Any>> implements ICoroutine<T> implements ICoroutineScope implements IContinuation<T> {
	public final context : Context;

	public var isRunning (get, never) : Bool;

	public var isCancelled (get, never) : Bool;

	public var isCompleted (get, never) : Bool;

	public var result : T;

	public var error : Exception;

	public var state : CoroutineState;

	var lambda : ScopedCoroutine<T>;

	final children : Array<BaseCoroutine<Any>>;

	var completionCallbacks : Array<()->Void>;

	var completedChildren : Int;

	public function new(context : Context, lambda : ScopedCoroutine<T>) {
		this.context  = context.clone().with(this);
		this.children = [];

		this.lambda         = lambda;
		completionCallbacks = [];
		completedChildren   = 0;
		state               = Created;
	}

	public function launch() {
		switch (state) {
			case Created:
				state = Running;
				final result = lambda(this, this);
				switch result.state {
					case Pending:
						return;
					case Returned:
						resume(result.result, null);
					case Thrown:
						resume(null, result.error);
				}
			case _:
		}
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

	public function child<T>(context:Context, lambda:ScopedCoroutine<T>) {
		final coroutine = new BaseCoroutine<T>(context, lambda);

		coroutine.onCompletion(() -> {
			completedChildren++;
		});

		children.push(coroutine);

		return coroutine;
	}

	public function with(...elements:IElement<Any>) {
		return new AdjustedContext(context.clone().with(...elements), this);
	}

	public function start<T>(c:Coroutine<ICoroutineScope->T>):ICoroutine<T> {
		return startChild(child(context, c));
	}

	function startChild<T>(coroutine:BaseCoroutine<T>):ICoroutine<T> {

		coroutine.onCompletion(() -> context.get(ScopeComponent.key).onCompletion(this, coroutine));

		coroutine.context.get(Scheduler.key).schedule(() -> {
			// TODO: are we potentially ereasing a stack track here?
			// would it be better to have the coroutine function pre-amble to check this and error "normally"?
			if (coroutine.isCancelled) {
				coroutine.completeExceptionally(coroutine.error);

				return;
			}

			coroutine.launch();
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

	function handleCompletionCallbacks() {
		while (completionCallbacks.length > 0) {
			final callbacks = completionCallbacks;
			completionCallbacks = [];
			for (callback in callbacks) {
				callback();
			}
		}
	}

	public function complete(result : T) {
		this.result = result;

		if (children.length == 0 || children.length == completedChildren) {
			state = Completed;

			handleCompletionCallbacks();
		} else {
			state = Completing;
		}
	}

	public function completeExceptionally(error : Exception) {
		this.error  = error;

		if (children.length == 0 || children.length == completedChildren) {
			state = Cancelled;

			handleCompletionCallbacks();
		}
		else {
			state = Cancelling;

			for (child in children) {
				child.cancel();
			}
		}
	}

	function get_isRunning() {
		return switch state {
			case Created | Running: true;
			case _: false;
		}
	}

	function get_isCancelled() {
		return switch state {
			case Cancelling | Cancelled:
				true;
			case _:
				false;
		}
	}

	function get_isCompleted() {
		return switch state {
			case Completed | Cancelled:
				true;
			case _:
				false;
		}
	}
}