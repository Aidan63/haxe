package haxe.coro.continuations;

import haxe.coro.context.Context;
import haxe.coro.schedulers.Scheduler;

@:coreApi class RacingContinuation<T> implements IContinuation<T> {
	final inputCont:IContinuation<T>;
	final outputCont:SuspensionResult<T>;

	final lock:Mutex;

	var assigned:Bool;

	public var context(get, null):Context;

	public function new(inputCont:IContinuation<T>, outputCont:SuspensionResult<T>) {
		this.inputCont = inputCont;
		this.outputCont = outputCont;
		context = inputCont.context;
		assigned = false;
		lock = new Mutex();
	}

	inline function get_context() {
		return context;
	}

	public function resume(result:T, error:Exception):Void {
		context.get(Scheduler.key).schedule(0, () -> {
			lock.acquire();

			if (assigned) {
				lock.release();
				inputCont.resume(result, error);
			} else {
				assigned = true;
				outputCont.result = result;
				outputCont.error = error;

				lock.release();
			}
		});
	}

	public function resolve():Void {
		lock.acquire();
		if (assigned) {
			if (outputCont.error != null) {
				outputCont.state = Thrown;
				lock.release();
			} else {
				outputCont.state = Returned;
				lock.release();
			}
		} else {
			assigned = true;
			outputCont.state = Pending;
			lock.release();
		}
	}
}
