package hxcoro;

import haxe.exceptions.CancellationException;
import hxcoro.AbstractTask;
import hxcoro.ICoroTask;
import haxe.coro.Coroutine;
import haxe.coro.context.Context;
import haxe.coro.context.Key;
import haxe.coro.context.IElement;
import haxe.coro.IContinuation;
import haxe.Exception;

class CoroTask<T> extends AbstractTask implements IContinuation<T> implements ICoroScope implements IStartableCoroTask<T> implements IElement<CoroTask<Any>> {
	public static final key:Key<CoroTask<Any>> = Key.createNew('Task');

	public final lambda:ScopedLambda<T>;

	var result:Null<T>;

	var completionCallbacks:Array<() -> Void>;

	public function new(context:Context, lambda:ScopedLambda<T>, parent:AbstractTask) {
		super(context, parent);
		this.context = context.clone().with(this);
		this.lambda = lambda;
		completionCallbacks = [];
	}

	public function get() {
		return result;
	}

	public function getException() {
		return error;
	}

	public function getKey() {
		return key;
	}

	public function start() {
		switch (state) {
			case Created:
				state = Running;
			case _:
				return;
		}
		// TODO: don't do this if we're already cancelling
		final result = lambda(this, this);
		switch result.state {
			case Pending:
				return;
			case Returned:
				resume(result.result, null);
			case Thrown:
				resume(null, result.error);
		}
	}

	@:coroutine public function await():T {
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
					start();
			}
		});
	}

	public function resume(result:T, error:Exception) {
		if (error == null) {
			this.result = result;
			state = Completing;
			checkCompletion();
		} else {
			this.error = error;
			selfError();
		}
	}

	function selfError() {
		state = Cancelling;
		cancelChildren();
		checkCompletion();
	}

	// called from parent

	function childSucceeds(_) {}

	function childErrors(_, error:Exception) {
		switch (state) {
			case Created | Running | Completing:
				// inherit child error
				this.error = error;
				selfError();
			case Cancelling:
				// not sure about this one, what if we cancel normally and then get a real exception?
			case Completed | Cancelled:
		}
	}

	function childCancels(_, cause:CancellationException) {
		// Cancellation is often issues from the parent anyway, but I don't know if that's always the case
		// Calling cancel is fine because it won't do anything if we're already cancelling
		cancel(cause);
	}

	function complete() {
		parent?.childCompletes(this);
		handleCompletionCallbacks();
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
}
