package hxcoro.task.node;

import haxe.Exception;
import haxe.exceptions.CancellationException;

@:access(hxcoro.task.AbstractTask)
@:access(hxcoro.task.CoroTask)
class CoroSupervisorStrategy implements INodeStrategy {
	public function new() {}

	public function complete<T>(task:CoroTask<T>) {
		task.parent?.childCompletes(task, false);
		task.handleAwaitingContinuations();
	}

	public function childrenCompleted<T>(task:CoroTask<T>) {
		task.awaitingChildContinuation?.resume(null, null);
	}

	public function childSucceeds<T>(task:CoroTask<T>, child:AbstractTask) {}

	public function childErrors<T>(task:CoroTask<T>, child:AbstractTask, cause:Exception) {}

	public function childCancels<T>(task:CoroTask<T>, child:AbstractTask, cause:CancellationException) {}
}
