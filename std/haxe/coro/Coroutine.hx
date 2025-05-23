package haxe.coro;

import haxe.coro.EventLoop;
import haxe.coro.context.Context;
import haxe.coro.context.Key;
import haxe.coro.coroutines.BaseCoroutine;
import haxe.coro.schedulers.EventLoopScheduler;
import haxe.coro.schedulers.Scheduler;
import haxe.coro.continuations.RacingContinuation;
import haxe.coro.continuations.BlockingContinuation;
import haxe.coro.scopes.DefaultScopeComponent;
import haxe.exceptions.NotImplementedException;

private class CoroSuspend<T> extends haxe.coro.BaseContinuation<T> {
	public function new(completion:haxe.coro.IContinuation<T>) {
		super(completion, 1);
	}

	public function invokeResume():SuspensionResult<T> {
		return Coroutine.suspend(null, this);
	}
}

/**
	Coroutine function.
**/
@:callable
@:coreType
abstract Coroutine<T:haxe.Constraints.Function> {
	public static final key : Key<ICoroutine<Any>> = Key.createNew('_hx_coroutine');

	@:coroutine @:coroutine.transformed
	public static function suspend<T>(func:haxe.coro.IContinuation<T>->Void, completion:haxe.coro.IContinuation<T>):T {
		var continuation = new CoroSuspend(completion);
		var safe = new RacingContinuation(completion, continuation);
		func(safe);
		safe.resolve();
		return cast continuation;
	}

	@:coroutine @:coroutine.nothrow public static function delay(ms:Int):Void {
		Coroutine.suspend(cont -> {
			cont.context.get(Scheduler.key).scheduleIn(() -> cont.resume(null, null), ms);
		});
	}

	@:coroutine @:coroutine.nothrow public static function yield():Void {
		Coroutine.suspend(cont -> {
			cont.context.get(Scheduler.key).schedule(() -> cont.resume(null, null));
		});
	}

	public static function run<T>(f:Coroutine<() -> T>):T {
		final loop    = new EventLoop();
		final cont    = new BlockingContinuation<T>(loop, new EventLoopScheduler(loop));
		final result  = f(cont);

		return switch (result.state) {
			case Pending:
				cont.wait();
			case Returned:
				result.result;
			case Thrown:
				throw result.error;
		}
	}

	public static function runScoped<T>(f:Coroutine<(scope : ICoroutineScope)->T>):T {
		final loop = new EventLoop();
		final schedulerComponent = new EventLoopScheduler(loop);
		final scopeComponent = new DefaultScopeComponent();
		final stackTraceManagerComponent = new haxe.coro.BaseContinuation.StackTraceManager();
		final coro = new BaseCoroutine(Context.create(scopeComponent, schedulerComponent, stackTraceManagerComponent));
		final result = f(coro, coro);
		switch (result.state) {
			case Pending:
				//
			case Returned:
				coro.resume(result.result, null);
			case Thrown:
				coro.resume(null, result.error);
		}
		while (loop.tick()) {
			switch (coro.state) {
				case Completed | Cancelled:
					break;
				case _:
			}
			// Busy wait
		}
		if (coro.error != null) {
			throw coro.error;
		} else {
			return coro.result;
		}
	}
}