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
		}, 0);
		return child;
	}

	public function lazy<T>(lambda:ScopedLambda<T>) {
		return new CoroChildTask(context, lambda, task);
	}

	public function cancel(?cause:CancellationException) {
		task.cancel();
	}

	public function with(...elements:IElement<Any>) {
		return task.with(...elements);
	}
}

/**
	CoroTask provides the basic functionality for coroutine tasks.
**/
abstract class CoroTask<T> extends AbstractTask<T> implements IContinuation<T> implements ICoroScope implements IStartableCoroTask<T>
		implements IElement<CoroTask<Any>> {
	public static final key:Key<CoroTask<Any>> = Key.createNew('Task');

	/**
		This task's immutable `Context`.
	**/
	public final context:Context;

	final lambda:ScopedLambda<T>;
	var result:Null<T>;
	var awaitingContinuations:Array<IContinuation<T>>;
	var wasResumed:Bool;

	/**
		Creates a new task using the provided `context` in order to execute `lambda`.
	**/
	public function new(context:Context, lambda:ScopedLambda<T>) {
		super();
		this.context = context.clone().with(this);
		this.lambda = lambda;
		awaitingContinuations = [];
		wasResumed = true;
	}

	public function get() {
		return result;
	}

	public function getKey() {
		return key;
	}

	/**
		Starts executing this task's `lambda`. Has no effect if the task is already active or has completed.
	**/
	public function start() {
		switch (state) {
			case Created:
				beginRunning();
				wasResumed = false;
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

	/**
		Creates a lazy child task to execute `lambda`. The child task does not execute until its `start`
		method is called. This occurrs automatically once this task has finished execution.
	**/
	public function lazy<T>(lambda:ScopedLambda<T>):IStartableCoroTask<T> {
		return new CoroChildTask(context, lambda, this);
	}

	/**
		Creates a child task to execute `lambda` and starts it automatically.
	**/
	public function async<T>(lambda:ScopedLambda<T>):ICoroTask<T> {
		final child = lazy(lambda);
		context.get(Scheduler.key).schedule(() -> {
			child.start();
		}, 0);
		return child;
	}

	/**
		Returns a copy of this tasks `Context` with `elements` added, which can be used to start child tasks.
	**/
	public function with(...elements:IElement<Any>) {
		return new CoroTaskWith(context.clone().with(...elements), this);
	}

	/**
		Resumes `cont` with this task's outcome.

		If this task is no longer active, the continuation is resumed immediately. Otherwise, it is registered
		to be resumed upon completion.

		This function also starts this task if it has not been started yet.
	**/
	public function awaitContinuation(cont:IContinuation<T>) {
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

	/**
		Suspends this task until it completes.
	**/
	@:coroutine public function await():T {
		return Coroutine.suspend(awaitContinuation);
	}

	/**
		Resumes the task with the provided `result` and `error`.
	**/
	public function resume(result:T, error:Exception) {
		wasResumed = true;
		if (error == null) {
			switch (state) {
				case Running:
					this.result = result;
					beginCompleting();
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

	override function checkCompletion() {
		if (!wasResumed) {
			return;
		}
		super.checkCompletion();
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
