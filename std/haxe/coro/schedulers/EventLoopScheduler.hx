package haxe.coro.schedulers;

import haxe.exceptions.ArgumentException;

private class ScheduledEvent {
	public final func : ()->Void;
	public final runTime : Float;
	public var next : Null<ScheduledEvent>;
	public var previous : Null<ScheduledEvent>;

	public function new(func, runTime) {
		this.func    = func;
		this.runTime = runTime;

		next     = null;
		previous = null;
	}
}

class EventLoopScheduler extends Scheduler {
	var events : Null<ScheduledEvent>;

	public function new() {
		super();

		events = null;
	}

    public function schedule(func:()->Void, ms:Int) {
		if (ms < 0) {
			throw new ArgumentException("Time must be greater or equal to zero");
		}

		final event = new ScheduledEvent(func, now() + (ms / 1000));

		if (events == null) {
			events = event;

			return;
		}
		
		var current  = events;
		var previous = null;
		while (true) {
			if (current == null) {
				previous.next  = event;
				event.previous = previous;
				break;
			} else if (event.runTime < current.runTime) {
				event.next = current;
				current.previous = event;
				switch previous {
					case null:
						events = event;
					case _:
						event.previous   = previous;
						previous.next    = event;
						current.previous = event;
				}
				break;
			} else {
				previous = current;
				current = current.next;
			}
		}
    }

	public function now() {
		return Timer.stamp();
	}

	public function run() {
		final currentTime = now();

		var current = events;
		while (current != null) {
			if (current.runTime <= currentTime) {
				current.func();
				current = current.next;
			} else {
				events = current;

				return;
			}
		}
	}

	public function toString() {
		return '[EventLoopScheduler]';
	}
}