package hxcoro.task;

import hxcoro.task.node.CoroChildStrategy;
import hxcoro.task.node.CoroScopeStrategy;
import hxcoro.task.node.CoroSupervisorStrategy;
import hxcoro.task.node.INodeStrategy;
import hxcoro.task.ICoroTask;
import hxcoro.task.AbstractTask;
import hxcoro.task.ICoroNode;
import haxe.Exception;
import haxe.exceptions.CancellationException;
import haxe.coro.IContinuation;
import haxe.coro.context.Key;
import haxe.coro.context.Context;
import haxe.coro.context.IElement;
import haxe.coro.schedulers.Scheduler;
import haxe.coro.cancellation.CancellationToken;

private class CoroTaskWith<T, C> implements ICoroNodeWith<C> {
	public var context(get, null):Context;

	final task:CoroTask<T, C>;

	public function new(context:Context, task:CoroTask<T, C>) {
		this.context = context;
		this.task = task;
	}

	inline function get_context() {
		return context;
	}

	public function async<T:C, R>(lambda:NodeLambda<T, R>):ICoroTask<T> {
		final child = new CoroTask(context, CoroTask.CoroChildStrategy);
		context.get(Scheduler.key).schedule(0, () -> {
			child.runNodeLambda(lambda);
		});
		return child;
	}

	public function lazy<T:C, R>(lambda:NodeLambda<T, R>):IStartableCoroTask<T> {
		return new StartableCoroTask(context, lambda, CoroTask.CoroChildStrategy);
	}

	public function with(...elements:IElement<Any>) {
		return task.with(...elements);
	}
}

/**
	CoroTask provides the basic functionality for coroutine tasks.
**/
class CoroTask<T, C = Any> extends AbstractTask<T, C> implements IContinuation<T> implements ICoroNode<C> implements ICoroTask<T>
		implements IElement<CoroTask<Any>> {
	public static final key = new Key<CoroTask<Any>>('Task');

	static public final CoroChildStrategy = new CoroChildStrategy();
	static public final CoroScopeStrategy = new CoroScopeStrategy();
	static public final CoroSupervisorStrategy = new CoroSupervisorStrategy();

	/**
		This task's immutable `Context`.
	**/
	public var context(get, null):Context;

	final nodeStrategy:INodeStrategy;
	var initialContext:Context;
	var result:Null<T>;
	var awaitingContinuations:Null<Array<IContinuation<T>>>;
	var awaitingChildContinuation:Null<IContinuation<C>>;
	var wasResumed:Bool;

	/**
		Creates a new task using the provided `context`.
	**/
	public function new(context:Context, nodeStrategy:INodeStrategy) {
		super(context.get(CoroTask.key));
		initialContext = context;
		this.nodeStrategy = nodeStrategy;
		wasResumed = true;
	}

	inline function get_context() {
		if (context == null) {
			context = initialContext.clone().with(this).add(CancellationToken.key, this);
		}
		return context;
	}

	public function get() {
		return result;
	}

	public function getKey() {
		return key;
	}

	public function doStart() {
		wasResumed = false;
	}

	/**
		Indicates that the task has been suspended, which allows it to clean up some of
		its internal resources. Has no effect on the observable state of the task.

		This function should be called when it is expected that the task might not be resumed
		for a while, e.g. when waiting on a sparse `Channel` or a contended `Mutex`.
	**/
	public function putOnHold() {
		context = null;
		if (awaitingContinuations != null && awaitingContinuations.length == 0) {
			awaitingContinuations = null;
		}
		if (cancellationCallbacks != null && cancellationCallbacks.length == 0) {
			cancellationCallbacks = null;
		}
		if (allChildrenCompleted) {
			children = null;
		}
	}

	public function runNodeLambda(lambda:NodeLambda<T, C>) {
		final result = lambda(this, this);
		start();
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
	public function lazy<T:C, R>(lambda:NodeLambda<T, R>):IStartableCoroTask<T> {
		return new StartableCoroTask(context, lambda, CoroChildStrategy);
	}

	/**
		Creates a child task to execute `lambda` and starts it automatically.
	**/
	public function async<T:C, R>(lambda:NodeLambda<T, R>):ICoroTask<T> {
		final child = new CoroTask<T, R>(context, CoroChildStrategy);
		context.get(Scheduler.key).schedule(0, () -> {
			child.runNodeLambda(lambda);
		});
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
				awaitingContinuations ??= [];
				awaitingContinuations.push(cont);
				start();
		}
	}

	@:coroutine public function awaitChildren() {
		if (allChildrenCompleted) {
			awaitingChildContinuation?.resume(null, null);
		}
		startChildren();
		Coro.suspend(cont -> awaitingChildContinuation = cont);
	}

	/**
		Suspends this task until it completes.
	**/
	@:coroutine public function await():T {
		return Coro.suspend(awaitContinuation);
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
		if (awaitingContinuations == null) {
			return;
		}
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

	// strategy dispatcher

	function complete() {
		nodeStrategy.complete(this);
	}

	function childrenCompleted() {
		nodeStrategy.childrenCompleted(this);
	}

	function childSucceeds(child:AbstractTask<C>) {
		nodeStrategy.childSucceeds(this, child);
	}

	function childErrors(child:AbstractTask<C>, cause:Exception) {
		nodeStrategy.childErrors(this, child, cause);
	}

	function childCancels(child:AbstractTask<C>, cause:CancellationException) {
		nodeStrategy.childCancels(this, child, cause);
	}
}

class StartableCoroTask<T, C> extends CoroTask<T, C> implements IStartableCoroTask<T> {
	final lambda:NodeLambda<T, C>;

	/**
		Creates a new task using the provided `context` in order to execute `lambda`.
	**/
	public function new(context:Context, lambda:NodeLambda<T, C>, nodeStrategy:INodeStrategy) {
		super(context, nodeStrategy);
		this.lambda = lambda;
	}

	/**
		Starts executing this task's `lambda`. Has no effect if the task is already active or has completed.
	**/
	override public function doStart() {
		super.doStart();
		runNodeLambda(lambda);
	}
}
