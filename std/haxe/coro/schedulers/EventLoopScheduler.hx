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
	var first : Null<ScheduledEvent>;
	var last : Null<ScheduledEvent>;

	public function new() {
		super();

		first = null;
		last = null;
	}

    public function schedule(func:()->Void, ms:Int) {
		if (ms < 0) {
			throw new ArgumentException("Time must be greater or equal to zero");
		}

		final event = new ScheduledEvent(func, now() + (ms / 1000));
		if (first == null) {
			first = event;
			last = event;
			return;
		}

		var current = last;
		while (true) {
			if (current == null) {
				event.next = first;
				first = event;
				break;
			} else if (event.runTime >= current.runTime) {
				final next = current.next;
				current.next = event;
				event.previous = current;
				if (next != null) {
					event.next = next;
					next.previous = event;
				} else {
					last = event;
				}
				break;
			} else {
				current = current.previous;
			}
		}
    }

	public function now() {
		return Timer.stamp();
	}

	public function run() {
		final currentTime = now();

		while (true) {
			if (first == null) {
				last = null;
				break;
			}
			if (first.runTime <= currentTime) {
				final func = first.func;
				first = first.next;
				if (first != null) {
					first.previous = null;
				}
				func();
			} else {
				break;
			}
		}
	}

	public function toString() {
		return '[EventLoopScheduler]';
	}
}