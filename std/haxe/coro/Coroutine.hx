package haxe.coro;

import haxe.coro.schedulers.Scheduler;
import haxe.coro.IContinuation;
import haxe.coro.SuspensionResult;
import haxe.coro.context.Context;
import haxe.coro.context.IElement;
import haxe.coro.EventLoop;
import haxe.coro.schedulers.EventLoopScheduler;
import haxe.exceptions.CancellationException;
import hxcoro.ScopedLambda;
import hxcoro.CoroScopeTask;

private class CoroSuspend<T> extends haxe.coro.BaseContinuation<T> {
	public function new(completion:haxe.coro.IContinuation<T>) {
		super(completion, 1);
	}

	public function invokeResume():SuspensionResult<T> {
		return Coroutine.suspend(null, this);
	}
}

private abstract RunnableContext(ElementTree) {
	inline function new(tree:ElementTree) {
		this = tree;
	}

	public function run<T>(lambda:ScopedLambda<T>):T {
		return Coroutine.runIn(new Context(this), lambda);
	}

	@:from static function fromAdjustableContext(context:AdjustableContext) {
		return new RunnableContext(cast context);
	}

	public function with(...elements:IElement<Any>):RunnableContext {
		return new AdjustableContext(this.copy()).with(...elements);
	}
}

@:callable
@:coreType
abstract Coroutine<T:haxe.Constraints.Function> {
	@:coroutine @:coroutine.transformed
	public static function suspend<T>(func:haxe.coro.IContinuation<T>->Void, completion:haxe.coro.IContinuation<T>):T {
		var continuation = new CoroSuspend(completion);
		var safe = new haxe.coro.continuations.RacingContinuation(completion, continuation);
		func(safe);
		safe.resolve();
		return cast continuation;
	}

	static function cancellationRequested(cont:IContinuation<Any>) {
		return cont.context.get(hxcoro.CoroTask.key)?.cancellationRequested();
	}

	@:coroutine @:coroutine.nothrow public static function delay(ms:Int):Void {
		suspend(cont -> {
			cont.context.get(Scheduler.key).scheduleIn(() -> {
				cont.resume(null, cancellationRequested(cont) ? new CancellationException() : null);
			}, ms);
		});
	}

	@:coroutine @:coroutine.nothrow public static function yield():Void {
		suspend(cont -> {
			cont.context.get(Scheduler.key).schedule(() -> {
				cont.resume(null, cancellationRequested(cont) ? new CancellationException() : null);
			});
		});
	}

	static var defaultContext(get, null):Context;

	static function get_defaultContext() {
		if (defaultContext != null) {
			return defaultContext;
		}
		final loop = new EventLoop();
		final schedulerComponent = new EventLoopScheduler(loop);
		final stackTraceManagerComponent = new haxe.coro.BaseContinuation.StackTraceManager();
		defaultContext = Context.create(schedulerComponent, stackTraceManagerComponent);
		return defaultContext;
	}

	public static function with(...elements:IElement<Any>):RunnableContext {
		return defaultContext.clone().with(...elements);
	}

	static public function run<T>(lambda:Coroutine<() -> T>):T {
		return runScoped(_ -> lambda());
	}

	static public function runScoped<T>(lambda:ScopedLambda<T>):T {
		return runIn(defaultContext, lambda);
	}

	static public function runIn<T>(context:Context, lambda:ScopedLambda<T>):T {
		final scope = new CoroScopeTask(context, lambda, null);
		scope.join();
		return scope.get();
	}

	@:coroutine static public function scope<T>(lambda:ScopedLambda<T>):T {
		return suspend(cont -> {
			final context = cont.context;
			final scope = new CoroScopeTask(context, lambda, context.get(hxcoro.CoroTask.key));
			scope.await(cont);
			scope.join();
		});
	}
}
