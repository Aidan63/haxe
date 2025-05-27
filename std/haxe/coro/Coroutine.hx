package haxe.coro;

import haxe.coro.schedulers.Scheduler;
import haxe.coro.IContinuation;
import haxe.coro.SuspensionResult;
import haxe.coro.context.Context;
import haxe.coro.EventLoop;
import haxe.coro.schedulers.EventLoopScheduler;
import haxe.exceptions.CancellationException;
import hxcoro.ScopedLambda;
import hxcoro.CoroScope;

private class CoroSuspend<T> extends haxe.coro.BaseContinuation<T> {
	public function new(completion:haxe.coro.IContinuation<T>) {
		super(completion, 1);
	}

	public function invokeResume():SuspensionResult<T> {
		return Coroutine.suspend(null, this);
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

	static public function run<T>(lambda:Coroutine<() -> T>):T {
		return runScoped(_ -> lambda());
	}

	static public function runScoped<T>(lambda:ScopedLambda<T>):T {
		final loop = new EventLoop();
		final schedulerComponent = new EventLoopScheduler(loop);
		final stackTraceManagerComponent = new haxe.coro.BaseContinuation.StackTraceManager();
		final context = Context.create(schedulerComponent, stackTraceManagerComponent);
		final scope = new CoroScope(context);
		final task = scope.async(lambda);
		scope.join();
		return task.get();
	}

	@:coroutine static public function scope<T>(lambda:ScopedLambda<T>):T {
		return suspend(cont -> {
			final scope = new CoroScope(cont.context, cont.context.get(hxcoro.CoroTask.key));
			final task = scope.async(lambda);
			task.await(cont);
			scope.join();
		});
	}
}
