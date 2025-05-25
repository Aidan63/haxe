package haxe.coro.coroutines;

import haxe.exceptions.CancellationException;
import haxe.coro.schedulers.Scheduler;
import haxe.coro.context.IElement;
import haxe.coro.context.Context;
import haxe.coro.scopes.ScopeComponent;
import haxe.coro.Coroutine.ScopedCoroutine;

private enum abstract CoroutineState(Int) {
	/**
		The coroutine was created but is not running yet.
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

private interface ICoroutineHost<T> extends ICoroutine<T> {
	function awaitChild<T>(child:ICoroutine<T>, continuation:IContinuation<T>):Void;
	function childCompletes<T>(child:ICoroutine<T>, result:T):Void;
	function childErrors(child:ICoroutine<Any>, error:Exception):Void;
	function childCancels(child:ICoroutine<Any>, error:Exception):Void;
}

private class ChildAwait<T> {
	public final continuation:IContinuation<T>;
	public final child:ICoroutine<T>;

	public function new(continuation:IContinuation<T>, child:ICoroutine<T>) {
		this.continuation = continuation;
		this.child = child;
	}
}

class AdjustedContext<T> implements ICoroutineScope {
	public final context:Context;
	final coroutine:BaseCoroutine<T>;

	public function new(context:Context, coroutine:BaseCoroutine<T>) {
		this.context = context;
		this.coroutine = coroutine;
	}

	public function create<T>(f:ScopedCoroutine<T>) {
		return coroutine.createChild(context, f);
	}

	public function start<T>(f:ScopedCoroutine<T>) {
		final child = coroutine.createChild(context, f);
		child.context.get(Scheduler.key).schedule(() -> {
			child.launch();
		});
		return child;
	}

	public function with(...elements:IElement<Any>) {
		return new AdjustedContext(context.clone().with(...elements), coroutine);
	}
}

class BaseCoroutine<T> implements IElement<ICoroutine<Any>> implements ICoroutine<T> implements ICoroutineScope implements IContinuation<T> implements ICoroutineHost<T> {
	public final context : Context;

	public var isCancellable (get, never) : Bool;

	public var isCompleted (get, never) : Bool;

	public var result : T;

	public var error : Exception;

	public var state : CoroutineState;

	public final parent:Null<ICoroutineHost<Any>>;

	final lambda:ScopedCoroutine<T>;
	final children : Array<BaseCoroutine<Any>>;
	var childAwait:Null<ChildAwait<Any>>;
	var completionCallbacks:Array<() -> Void>;
	var completedChildren : Int;
	var isCancelling : Bool;

	public function new(context : Context, lambda:ScopedCoroutine<T>, ?parent : ICoroutineHost<Any>) {
		this.context  = context.clone().with(this);
		this.parent   = parent;
		this.children = [];

		this.lambda         = lambda;
		completionCallbacks = [];
		completedChildren   = 0;
		state               = Created;
		isCancelling        = false;
	}

	@:coroutine public function await() : T {
		return Coroutine.suspend(cont -> {
			switch state {
				case Completed:
					cont.resume(result, null);
				case Cancelled:
					cont.resume(null, error);
				case _:
					final current = cont.context.get(Coroutine.key);
					if (current == parent) {
						parent.awaitChild(this, cont);
					} else {
						completionCallbacks.push(() -> {
							if (error != null) {
								cont.resume(null, error);
							} else {
								cont.resume(result, null);
							}
						});
					}
					launch();
			}
		});
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

	public function resume(result:T, error:Exception) {
		this.result = result;
		this.error = error;
		if (error == null) {
			state = Completing;
		} else {
			state = Cancelling;
			final cancellationException = if (error is CancellationException) {
				isCancelling = true;
				(cast error : CancellationException);
			} else {
				new CancellationException();
			}
			for (child in children) {
				child.cancel(cancellationException);
			}
		}
		checkCompletion();
	}

	function checkCompletion() {
		switch (state) {
			case Completing:
				if (completedChildren == children.length) {
					state = Completed;
					parent?.childCompletes(this, result);
					handleCompletionCallbacks();
				}
			case Cancelling:
				if (completedChildren == children.length) {
					state = Cancelled;
					if (isCancelling) {
						parent?.childCancels(this, error);
					} else {
						parent?.childErrors(this, error);
					}
					handleCompletionCallbacks();
				}
			case _:
		}
	}

	public function onCompletion(c:() -> Void) {
		switch state {
			case Completed, Cancelled:
				c();
			case _:
				completionCallbacks.push(c);
		}
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
				// Is is okay to silently ignore this for all states?
		}
	}

	// children

	public function createChild<T>(context:Context, f:ScopedCoroutine<T>) {
		final childCoro = new BaseCoroutine<T>(context, f, this);
		children.push(childCoro);
		return childCoro;
	}

	public function awaitChildren() {
		for (child in children) {
			switch (child.state) {
				case Created:
					child.context.get(Scheduler.key).schedule(() -> {
						child.launch();
					});
				case Completing:
					child.awaitChildren();
				case _:
			}
		}
	}

	public function create<T>(f:ScopedCoroutine<T>) {
		return createChild(context, f);
	}

	public function with(...elements:IElement<Any>) {
		return new AdjustedContext(context.clone().with(...elements), this);
	}

	public function start<T>(f:ScopedCoroutine<T>):ICoroutine<T> {
		final child = create(f);
		child.context.get(Scheduler.key).schedule(() -> {
			child.launch();
		});
		return child;
	}

	public function awaitChild<T>(child:ICoroutine<T>, continuation:IContinuation<T>) {
		childAwait = new ChildAwait(continuation, child);
	}

	public function childCompletes<T>(child:ICoroutine<T>, result:T) {
		completedChildren++;
		if (childAwait?.child == child) {
			childAwait.continuation.resume(result, null);
		}
		checkCompletion();
	}

	public function childErrors(child:ICoroutine<Any>, error:Exception) {
		completedChildren++;
		if (childAwait?.child == child) {
			childAwait.continuation.resume(null, error);
		} else {
			context.get(ScopeComponent.key).childErrors(this, child, error);
		}
		checkCompletion();
	}

	public function childCancels(child:ICoroutine<Any>, error:Exception) {
		completedChildren++;
		if (childAwait?.child == child) {
			childAwait.continuation.resume(null, error);
		} else {
			context.get(ScopeComponent.key).childCancels(this, child, error);
		}
		checkCompletion();
	}

	public function cancel(?error:CancellationException) {
		if (isCancellable) {
			resume(null, error ?? new CancellationException());
		}
	}

	public function toString() {
		return 'Coroutine';
	}

	public function getKey() {
		return Coroutine.key;
	}

	function get_isCancellable() {
		return switch (state) {
			case Created | Running | Completing:
				true;
			case Cancelling | Cancelled | Completed:
				false;
		}
	}

	function get_isCompleted() {
		return switch (state) {
			case Completed | Cancelled:
				true;
			case Created | Completing | Cancelling | Running:
				false;
		}
	}
}