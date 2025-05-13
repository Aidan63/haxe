package haxe.coro;

import haxe.CallStack;
import haxe.coro.EventLoop;
import haxe.coro.ICoroutine;
import haxe.coro.schedulers.EventLoopScheduler;
import haxe.coro.continuations.RacingContinuation;
import haxe.coro.continuations.BlockingContinuation;

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
			cont.context.scheduler.scheduleIn(() -> cont.resume(null, null), ms);
		});
	}

	@:coroutine @:coroutine.nothrow public static function yield():Void {
		Coroutine.suspend(cont -> {
			cont.context.scheduler.schedule(() -> cont.resume(null, null));
		});
	}

	public static function run<T>(f:Coroutine<() -> T>):T {
		final loop    = new EventLoop();
		final context = new CoroutineContext(new EventLoopScheduler(loop), null);
		final cont    = new BlockingContinuation<T>(loop, context);
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
		final loop   = new EventLoop();
		final cont   = new BlockingCoroutine(loop);
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
}

private class BlockingCoroutine<T> extends AbstractCoroutine<T> {
	final loop : EventLoop;

	var result : T;

	var error : Exception;

	public function new(loop : EventLoop) {
		super(new CoroutineContext(new EventLoopScheduler(loop), this), null);

		this.loop = loop;

		error = null;
	}

	public function wait():T {
		while (loop.tick() || state != Completed) {
			// Busy wait
		}

		if (error != null) {
			final topStack = [];
			for (item in error.stack.asArray()) {
				switch (item) {
					// TODO: this needs a better check
					case FilePos(_, _, -1, _):
						break;
					// this is a hack
					case FilePos(Method(_, "invokeResume"), _):
						break;
					case _:
						topStack.push(item);
				}
			}
			final coroStack = (cast result : Array<StackItem>) ?? [];
			final bottomStack = CallStack.callStack();
			error.stack = topStack.concat(coroStack).concat(bottomStack);
			throw error;
		} else {
			return result;
		}
	}
}
