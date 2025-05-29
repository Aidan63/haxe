package hxcoro;

import haxe.Exception;
import haxe.exceptions.CancellationException;

class CoroScopeTask<T> extends CoroTask<T> {
	function childSucceeds(_) {}

	function childErrors(_, error:Exception) {
		if (this.error == null) {
			this.error = error;
			cancel();
		}
	}

	function childCancels(_, cause:CancellationException) {}

	function complete() {
		// don't notify parent
		handleAwaitingContinuations();
	}
}
