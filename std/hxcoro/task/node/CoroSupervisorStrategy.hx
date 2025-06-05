package hxcoro.task.node;

import haxe.Exception;
import haxe.exceptions.CancellationException;

@:access(hxcoro.task.AbstractTask)
@:access(hxcoro.task.CoroTask)
class CoroSupervisorStrategy implements INodeStrategy {
	public function new() {}

	public function complete<T, C>(task:CoroTask<T, C>) {
		task.parent?.childCompletes(task, false);
		task.handleAwaitingContinuations();
	}

	public function childrenCompleted<T, C>(task:CoroTask<T, C>) {
		task.awaitingChildContinuation?.resume(null, null);
	}

	public function childSucceeds<T, C>(task:CoroTask<T, C>, child:AbstractTask<C>) {}

	public function childErrors<T, C>(task:CoroTask<T, C>, child:AbstractTask<C>, cause:Exception) {}

	public function childCancels<T, C>(task:CoroTask<T, C>, child:AbstractTask<C>, cause:CancellationException) {}
}
