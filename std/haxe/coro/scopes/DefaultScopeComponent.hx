package haxe.coro.scopes;

import haxe.exceptions.CancellationException;
import haxe.coro.coroutines.BaseCoroutine;

@:access(haxe.coro.coroutines.BaseCoroutine)
class DefaultScopeComponent extends ScopeComponent {
	public function new() {}

	public function cancel(coroutine:BaseCoroutine<Any>) {
		switch coroutine.state {
			case Created | Running:
				coroutine.completeExceptionally(new CancellationException());
			case Completing:
				coroutine.state = Cancelling;
				coroutine.error = new CancellationException();

				for (child in coroutine.children) {
					child.cancel();
				}
			case _:
				//
		}
	}

	public function onCompletion(coroutine:BaseCoroutine<Any>, childCoroutine:BaseCoroutine<Any>) {
		// if we are not in a cancelled state, transition to one now.
		// TODO : what should we do if we are already cancelling and another child fails,
		// some sort of AggregateException which holds both errors?
		if (childCoroutine.isCancelled && coroutine.isCancelled == false) {
			coroutine.state = Cancelling;
			coroutine.error = childCoroutine.error;

			for (child in coroutine.children) {
				if (child == childCoroutine) {
					continue;
				}

				child.cancel();
			}
		}

		// There are still children running, so exit.
		if (coroutine.children.length != coroutine.completedChildren) {
			return;
		}

		// All children have completed but the scopes block is still running, so exit.
		if (coroutine.isRunning) {
			return;
		}

		switch coroutine.state {
			case Cancelling:
				coroutine.state = Cancelled;
			case Completing:
				coroutine.state = Completed;
			case _:
				throw new Exception('Unexpected coroutine state : ${coroutine.state}');
		}

		for (callback in @:privateAccess coroutine.completionCallbacks) {
			callback();
		}
	}
}