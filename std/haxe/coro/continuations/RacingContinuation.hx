package haxe.coro.continuations;

import haxe.coro.context.Context;
import haxe.coro.schedulers.Scheduler;

class RacingContinuation<T> extends SuspensionResult<T> implements IContinuation<T> {
	final inputCont:IContinuation<T>;

	var lock:Mutex;

	var resumed:Bool;
	var resolved:Bool;

	public var context(get, null):Context;

	public function new(inputCont:IContinuation<T>) {
		this.inputCont = inputCont;
		context = inputCont.context;
		resumed = false;
		resolved = false;
		lock = new Mutex();
	}

	inline function get_context() {
		return context;
	}

	public function resume(result:T, error:Exception):Void {
		lock.acquire();
		if (resolved) {
			// if we already have a value, schedule the follow-up resume call with that value
			final inputCont = inputCont;
			context.get(Scheduler.key).schedule(0, () -> {
				inputCont.resume(result, error);
			});
			lock.release();
			lock = null;
		} else {
			// otherwise we can assign immediately
			resumed = true;
			this.result = result;
			this.error = error;
			lock.release();
		}
	}

	public function resolve():Void {
		lock.acquire();
		if (resumed) {
			if (error != null) {
				state = Thrown;
			} else {
				state = Returned;
			}
			lock.release();
			lock = null;
		} else {
			resolved = true;
			state = Pending;
			lock.release();
		}
	}
}
