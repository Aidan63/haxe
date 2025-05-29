package hxcoro;

import haxe.Exception;
import haxe.exceptions.CancellationException;
import haxe.coro.context.Context;

class CoroScopeTask<T> extends CoroTask<T> {
	public function new(context:Context, lambda:ScopedLambda<T>) {
		super(context, lambda);
		context.get(hxcoro.CoroTask.key)?.addChild(this);
	}

	function childSucceeds(_) {}

	function childErrors(_, error:Exception) {
		if (this.error == null) {
			this.error = error;
			cancel();
		}
	}

	function childCancels(_, cause:CancellationException) {}

	function complete() {
		handleAwaitingContinuations();
	}
}
