package hxcoro.task.node;

import haxe.Exception;
import haxe.exceptions.CancellationException;

@:access(hxcoro.task.AbstractTask)
@:access(hxcoro.task.CoroTask)
class CoroScopeStrategy implements INodeStrategy {
	public function new() {}

	public function complete<T, C>(task:CoroTask<T, C>) {
		task.parent?.childCompletes(task, false);
		task.handleAwaitingContinuations();
	}

	public function childrenCompleted<T, C>(task:CoroTask<T, C>) {
		task.awaitingChildContinuation?.resume(null, null);
	}

	public function childSucceeds<T, C>(task:CoroTask<T, C>, child:AbstractTask<C>) {}

	public function childErrors<T, C>(task:CoroTask<T, C>, child:AbstractTask<C>, cause:Exception) {
		switch (task.state) {
			case Created | Running | Completing:
				// inherit child error
				if (task.error == null) {
					task.error = cause;
				}
				task.cancel();
			case Cancelling:
				// not sure about this one, what if we cancel normally and then get a real exception?
			case Completed | Cancelled:
		}
	}

	public function childCancels<T, C>(task:CoroTask<T, C>, child:AbstractTask<C>, cause:CancellationException) {}
}
