package hxcoro;

import haxe.exceptions.CancellationException;
import haxe.Exception;
import haxe.coro.context.Key;
import haxe.coro.context.IElement;
import hxcoro.AbstractTask;
import haxe.coro.schedulers.Scheduler;
import haxe.coro.context.Context;

class CoroScope extends AbstractTask implements ICoroScope implements IElement<CoroScope> {
	public static final key:Key<CoroScope> = Key.createNew('Scope');

	public function new(context:Context, ?parent:AbstractTask) {
		super(context, parent);
		this.context = context.clone().with(this);
	}

	public function getKey() {
		return key;
	}

	public function start() {
		switch (state) {
			case Created:
				state = Completing;
			case _:
		}
	}

	public function join() {
		start();
		// checkCompletion starts any lingering tasks, so let's call it here
		checkCompletion();
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

	function childSucceeds(_) {}

	function childErrors(_, error:Exception) {
		if (this.error == null) {
			// remember first child error by default
			this.error = error;
			state = Cancelling;
		}
	}

	function childCancels(_, cause:CancellationException) {}

	function complete() {}
}
