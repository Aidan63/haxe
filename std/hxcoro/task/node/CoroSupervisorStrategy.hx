package hxcoro.task.node;

import haxe.Exception;
import haxe.exceptions.CancellationException;

@:access(hxcoro.task.AbstractTask)
@:access(hxcoro.task.CoroTask)
class CoroSupervisorStrategy<T, C> implements INodeStrategy<T, C> {
	public function new() {}

	public function complete(task:CoroTask<T, C>) {
		task.parent?.childCompletes(task, false);
		task.handleAwaitingContinuations();
	}

	public function childrenCompleted(task:CoroTask<T, C>) {
		task.awaitingChildContinuation?.resume(null, null);
	}

	public function childSucceeds(task:CoroTask<T, C>, child:AbstractTask<C>) {}

	public function childErrors(task:CoroTask<T, C>, child:AbstractTask<C>, cause:Exception) {}

	public function childCancels(task:CoroTask<T, C>, child:AbstractTask<C>, cause:CancellationException) {}
}
