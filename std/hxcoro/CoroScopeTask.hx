package hxcoro;

import haxe.Exception;
import haxe.exceptions.CancellationException;
import haxe.coro.schedulers.Scheduler;

class CoroScopeTask<T> extends CoroTask<T> {
	public function join() {
		start();
		startChildren();
		final loop = context.get(Scheduler.key);
		while (loop.tick()) {
			if (!isRunning()) {
				break;
			}
		}
		if (error != null) {
			throw error;
		}
	}

	override function childSucceeds(_) {}

	override function childErrors(_, error:Exception) {
		if (this.error == null) {
			this.error = error;
			cancel();
		}
	}

	override function childCancels(_, cause:CancellationException) {}

	override function complete() {
		// don't notify parent
		handleCompletionCallbacks();
	}
}
