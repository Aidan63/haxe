package haxe.coro.schedulers;

import haxe.exceptions.ArgumentException;

private typedef Lambda<T> = (scheduler:Scheduler, state:T)->Void;
private typedef CloseClosure = (handle:ISchedulerHandle)->Void;

private class ScheduledEvent<T> implements ISchedulerHandle {
	final closure : CloseClosure;
	final func : Lambda<T>;
	final state : T;
	var closed : Bool;
	public final runTime : Int64;
	public var next : Null<ScheduledEvent<Any>>;
	public var previous : Null<ScheduledEvent<Any>>;

	public function new(closure, func, state, runTime) {
		this.closure = closure;
		this.state   = state;
		this.func    = func;
		this.runTime = runTime;

		closed   = false;
		next     = null;
		previous = null;
	}

	public inline function run(scheduler:Scheduler) {
		func(scheduler, state);

		closed = true;
	}

	public function close() {
		if (closed) {
			return;
		}

		closure(this);

		closed = true;
	}
}

private class ZeroEvent<T> {
	final func : Lambda<T>;
	final state : T;

	public function new(func:Lambda<T>, state:T) {
		this.func = func;
		this.state = state;
	}

	public inline function run(scheduler:Scheduler) {
		func(scheduler, state);
	}
}

private class NoOpHandle implements ISchedulerHandle {
	public function new() {}
	public function close() {}
}

private class DoubleBuffer {
	final a : Array<ZeroEvent<Any>>;
	final b : Array<ZeroEvent<Any>>;

	var current : Array<ZeroEvent<Any>>;

	public function new() {
		a       = [];
		b       = [];
		current = a;
	}

	public function flip() {
		final returning = current;

		current = if (current == a) b else a;
		current.resize(0);

		return returning;
	}

	public function push<T>(l : Lambda<T>, state : T) {
		current.push(new ZeroEvent(l, state));
	}

	public function empty() {
		return current.length == 0;
	}
}

class EventLoopScheduler extends Scheduler {
	var first : Null<ScheduledEvent<Any>>;
	var last : Null<ScheduledEvent<Any>>;

	final noOpHandle : NoOpHandle;
	final zeroEvents : DoubleBuffer;
	final zeroMutex : Mutex;
	final futureMutex : Mutex;
	final closeClosure : CloseClosure;

	public function new() {
		super();

		first        = null;
		last         = null;
		noOpHandle   = new NoOpHandle();
		zeroEvents   = new DoubleBuffer();
		zeroMutex    = new Mutex();
		futureMutex  = new Mutex();
		closeClosure = close;
	}

    public function schedule<T>(ms:Int64, state:T, func:(scheduler:Scheduler, state:T)->Void):ISchedulerHandle {
		if (ms < 0) {
			throw new ArgumentException("Time must be greater or equal to zero");
		} else if (ms == 0) {
			zeroMutex.acquire();
			zeroEvents.push(func, state);
			zeroMutex.release();
			return noOpHandle;
		}

		final event = new ScheduledEvent(closeClosure, func, state, now() + ms);

		futureMutex.acquire();
		if (first == null) {
			first = event;
			last = event;
			futureMutex.release();
			return event;
		}

		var currentLast = last;
		var currentFirst = first;
		while (true) {
			if (event.runTime >= currentLast.runTime) {
				final next = currentLast.next;
				currentLast.next = event;
				event.previous = currentLast;
				if (next != null) {
					event.next = next;
					next.previous = event;
				} else {
					last = event;
				}
				futureMutex.release();
				return event;
			}
			else if (event.runTime < currentFirst.runTime) {
				final previous = currentFirst.previous;
				currentFirst.previous = event;
				event.next = currentFirst;
				if (previous != null) {
					event.previous = previous;
					previous.next = event;
				} else {
					first = event;
				}
				futureMutex.release();
				return event;
			} else {
				currentFirst = currentLast.next;
				currentLast = currentLast.previous;
				// if one of them is null, set to the other so the next iteration will definitely
				// hit one of the two branches above
				if (currentFirst == null) {
					currentFirst = currentLast;
				} else if (currentLast == null) {
					currentLast = currentFirst;
				}
			}
		}
    }

	public function now() {
		return Timer.milliseconds();
	}

	public function run() {
		zeroMutex.acquire();
		final events = zeroEvents.flip();
		// no need to hold onto the mutex because it's a double buffer and run itself is single-threaded
		zeroMutex.release();
		for (event in events) {
			event.run(this);
		}

		final currentTime = now();

		futureMutex.acquire();
		while (true) {
			if (first == null) {
				last = null;
				break;
			}
			if (first.runTime <= currentTime) {
				final toRun = first;
				first = first.next;
				if (first != null) {
					first.previous = null;
				}
				futureMutex.release();
				toRun.run(this);
				futureMutex.acquire();
			} else {
				break;
			}
		}
		futureMutex.release();
	}

	public function toString() {
		return '[EventLoopScheduler]';
	}

	function close(handle : ISchedulerHandle) {
		var current = first;
		while (true) {
			if (null == current) {
				return;
			}

			if (current == handle) {
				if (first == current) {
					first = current.next;
				} else {
					final a = current.previous;
					final b = current.next;

					a.next = b;
					b?.previous = a;
				}

				return;
			} else {
				current = current.next;
			}
		}
	}
}