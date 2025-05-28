package hxcoro;

import haxe.exceptions.CancellationException;
import hxcoro.AbstractTask;
import hxcoro.ICoroTask;
import haxe.coro.Coroutine;
import haxe.coro.context.Context;
import haxe.coro.context.Key;
import haxe.coro.context.IElement;
import haxe.coro.IContinuation;
import haxe.coro.schedulers.Scheduler;
import haxe.Exception;

private class CoroTaskWith<T> implements ICoroScope {
	public final context:Context;

	final task:CoroTask<T>;

	public function new(context:Context, task:CoroTask<T>) {
		this.context = context;
		this.task = task;
	}

	public function async<T>(lambda:ScopedLambda<T>) {
		final child = lazy(lambda);
		context.get(Scheduler.key).schedule(() -> {
			child.start();
		});
		return child;
	}

	public function lazy<T>(lambda:ScopedLambda<T>) {
		return new CoroTask(context, lambda, task);
	}

	public function cancel(?cause:CancellationException) {
		task.cancel();
	}

	public function with(...elements:IElement<Any>) {
		return task.with(...elements);
	}
}

class CoroTask<T> extends AbstractTask implements IContinuation<T> implements ICoroScope implements IStartableCoroTask<T> implements IElement<CoroTask<Any>> {
	public static final key:Key<CoroTask<Any>> = Key.createNew('Task');

	public final context:Context;
	public final lambda:ScopedLambda<T>;

	var result:Null<T>;

	var awaitingContinuations:Array<IContinuation<T>>;
	var wasResumed:Bool;

	public function new(context:Context, lambda:ScopedLambda<T>, parent:Null<AbstractTask>) {
		super(parent);
		this.context = context.clone().with(this);
		this.lambda = lambda;
		awaitingContinuations = [];
		wasResumed = false;
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

	public function lazy<T>(lambda:ScopedLambda<T>):IStartableCoroTask<T> {
		return new CoroTask(context, lambda, this);
	}

	public function async<T>(lambda:ScopedLambda<T>):ICoroTask<T> {
		final child = lazy(lambda);
		context.get(Scheduler.key).schedule(() -> {
			child.start();
		});
		return child;
	}

	public function with(...elements:IElement<Any>) {
		return new CoroTaskWith(context.clone().with(...elements), this);
	}

	public function maybeContinue(cont:IContinuation<T>) {
		switch state {
			case Completed:
				cont.resume(result, null);
			case Cancelled:
				cont.resume(null, error);
			case _:
				awaitingContinuations.push(cont);
				start();
		}
	}

	override function checkCompletion() {
		if (!wasResumed) {
			return;
		}
		super.checkCompletion();
	}

	@:coroutine public function await():T {
		return Coroutine.suspend(maybeContinue);
	}

	public function resume(result:T, error:Exception) {
		wasResumed = true;
		if (error == null) {
			switch (state) {
				case Running:
					this.result = result;
					state = Completing;
				case _:
			}
			checkCompletion();
		} else {
			if (this.error == null) {
				this.error = error;
			}
			cancel();
		}
	}

	// called from parent

	function childSucceeds(_) {}

	function childErrors(_, error:Exception) {
		switch (state) {
			case Created | Running | Completing:
				// inherit child error
				if (this.error == null) {
					this.error = error;
				}
				cancel();
			case Cancelling:
				// not sure about this one, what if we cancel normally and then get a real exception?
			case Completed | Cancelled:
		}
	}

	function childCancels(_, cause:CancellationException) {
		// Cancellation is often issued from the parent anyway, but I don't know if that's always the case
		// Calling cancel is fine because it won't do anything if we're already cancelling
		cancel(cause);
	}

	function complete() {
		parent?.childCompletes(this);
		handleAwaitingContinuations();
	}

	function handleAwaitingContinuations() {
		while (awaitingContinuations.length > 0) {
			final continuations = awaitingContinuations;
			awaitingContinuations = [];
			if (error != null) {
				for (cont in continuations) {
					cont.resume(null, error);
				}
			} else {
				for (cont in continuations) {
					cont.resume(result, null);
				}
			}
		}
	}
}
