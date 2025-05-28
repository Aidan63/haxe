package hxcoro;

import hxcoro.ICoroTask.IStartableCoroTask;
import haxe.exceptions.CancellationException;
import haxe.Exception;

enum abstract TaskState(Int) {
	final Created;
	final Running;
	final Completing;
	final Completed;
	final Cancelling;
	final Cancelled;
}

class TaskException extends Exception {}

abstract class AbstractTask {
	var state:TaskState;
	final children:Array<AbstractTask>;
	final parent:Null<AbstractTask>;

	var error:Null<Exception>;

	public function new(?parent:AbstractTask) {
		state = Created;
		children = [];
		if (parent != null) {
			this.parent = parent;
			parent.addChild(this);
		}
	}

	public function cancel(?cause:CancellationException) {
		switch (state) {
			case Created | Running | Completing:
				cause ??= new CancellationException();
				error = cause;
				state = Cancelling;
				cancelChildren(cause);
				checkCompletion();
			case _:
		}
	}

	function cancelChildren(?cause:CancellationException) {
		for (child in children) {
			child.cancel(cause);
		}
	}

	public function isRunning() {
		return switch (state) {
			case Completed | Cancelled:
				false;
			case _:
				true;
		}
	}

	public function cancellationRequested() {
		return switch (state) {
			case Cancelling | Cancelled:
				true;
			case _:
				false;
		}
	}

	function startChildren() {
		var hasUnfinishedChild = false;
		for (child in children) {
			switch (child.state) {
				case Created:
					child.start();
					hasUnfinishedChild = true;
				case Cancelled | Completed:
				case Running | Completing | Cancelling:
					hasUnfinishedChild = true;
			}
		}
		return hasUnfinishedChild;
	}

	function checkCompletion() {
		switch (state) {
			case Created | Running | Completed | Cancelled:
				return;
			case _:
		}
		if (startChildren()) {
			return;
		}
		switch (state) {
			case Completing:
				state = Completed;
			case Cancelling:
				state = Cancelled;
			case _:
				throw new TaskException('Invalid state $state in checkCompletion');
		}
		complete();
	}

	abstract function start():Void;

	abstract function complete():Void;

	abstract function childSucceeds(child:AbstractTask):Void;

	abstract function childErrors(child:AbstractTask, cause:Exception):Void;

	abstract function childCancels(child:AbstractTask, cause:CancellationException):Void;

	// called from child

	function childCompletes(child:AbstractTask) {
		if (child.error != null) {
			if (child.error is CancellationException) {
				childCancels(child, cast child.error);
			} else {
				childErrors(child, child.error);
			}
		} else {
			childSucceeds(child);
		}
		checkCompletion();
	}

	function addChild(child:AbstractTask) {
		children.push(child);
	}
}
