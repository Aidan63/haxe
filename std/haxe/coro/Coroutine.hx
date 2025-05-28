package haxe.coro;

import haxe.coro.EventLoop;
import haxe.coro.context.Key;
import haxe.coro.coroutines.BlockingCoroutine;
import haxe.coro.schedulers.EventLoopScheduler;
import haxe.coro.schedulers.Scheduler;
import haxe.coro.continuations.RacingContinuation;
import haxe.coro.continuations.BlockingContinuation;
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
			cont.context.get(Scheduler.key).schedule(() -> cont.resume(null, null), ms);
		});
	}

	@:coroutine @:coroutine.nothrow public static function yield():Void {
		Coroutine.suspend(cont -> {
			cont.context.get(Scheduler.key).schedule(() -> cont.resume(null, null), 0);
		});
	}

	public static function run<T>(f:Coroutine<() -> T>):T {
		final cont    = new BlockingContinuation<T>(new EventLoopScheduler());
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
		final cont   = new BlockingCoroutine(new EventLoopScheduler());
		final result = f(cont, cont);

		switch (result.state) {
			case Pending:
				//
			case Returned:
				cont.resume(result.result, null);
			case Thrown:
				cont.resume(null, result.error);
		}

		return cont.wait();
	}

	@:coroutine public static function scope<T>(f:Coroutine<(scope : ICoroutineScope)->T>):T {
		return Coroutine.suspend(cont -> {
			final coro   = cont.context.get(key);
			final child  = coro.child(cont.context);
			final result = f(child, child);

			switch result.state {
				case Pending:
					//
				case Returned:
					child.complete(result.result);
				case Thrown:
					child.completeExceptionally(result.error);
			}

			child.onCompletion(() -> {
				switch child.state {
					case Completed:
						cont.resume(child.result, null);
					case Cancelled:
						cont.resume(null, child.error);
					case _:
						throw new Exception('Unexpected coroutine state');
				}
			});
		});
	}
}