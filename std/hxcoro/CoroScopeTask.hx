package hxcoro;

import haxe.Exception;
import haxe.exceptions.CancellationException;

class CoroScopeTask<T> extends CoroTask<T> {
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
