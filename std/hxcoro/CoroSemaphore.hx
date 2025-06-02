package hxcoro;

import haxe.coro.Mutex;
import hxcoro.Coro.*;
import hxcoro.task.CoroTask;
import hxcoro.ds.PagedDeque;
import haxe.coro.IContinuation;
import haxe.coro.cancellation.ICancellationHandle;
import haxe.exceptions.CancellationException;
import haxe.coro.cancellation.CancellationToken;

private class AtomicIntData {
	public final mutex:Mutex;
	public var value:Int;

	public function new(value:Int) {
		this.value = value;
		mutex = new Mutex();
	}
}

abstract AtomicInt(AtomicIntData) {
	public function new(v:Int) {
		this = new AtomicIntData(v);
	}

	public function get() {
		return this.value;
	}

	public function compareAndSet(compare:Int, set:Int) {
		this.mutex.acquire();
		if (this.value == compare) {
			this.value = set;
			this.mutex.release();
			return true;
		} else {
			this.mutex.release();
			return false;
		}
	}

	public function getAndDecrement() {
		this.mutex.acquire();
		final value = this.value;
		--this.value;
		this.mutex.release();
		return value;
	}

	public function increment() {
		this.mutex.acquire();
		++this.value;
		this.mutex.release();
	}
}

@:structInit
private class PendingAcquire<T> {
	public final cont:IContinuation<T>;
	public final cancelHandle:ICancellationHandle;
}

class CoroSemaphore {
	final maxFree:Int;
	final deque:PagedDeque<PendingAcquire<Any>>;
	final dequeMutex:Mutex;
	var free:AtomicInt;

	public function new(free:Int) {
		maxFree = free;
		deque = new PagedDeque<PendingAcquire<Any>>();
		dequeMutex = new Mutex();
		this.free = new AtomicInt(free);
	}

	@:coroutine public function acquire() {
		if (free.getAndDecrement() > 0) {
			return;
		}
		suspend(cont -> {
			final f = () -> cont.resume(null, new CancellationException());
			final task = cont.context.get(CoroTask.key);
			dequeMutex.acquire();
			deque.push({cont: cont, cancelHandle: task.onCancellationRequested(f)});
			dequeMutex.release();
		});
	}

	public function tryAcquire() {
		var free = free.get();
		if (free <= 0) {
			return false;
		}
		return this.free.compareAndSet(free, free - 1);
	}

	public function release() {
		free.increment();
		dequeMutex.acquire();
		while (true) {
			if (deque.isEmpty()) {
				// nobody else wants it right now, return
				dequeMutex.release();
				return;
			}
			// a continuation waits for this mutex, wake it up now
			final acq = deque.pop();
			final cont = acq.cont;
			final ct = cont.context.get(CancellationToken.key);
			if (ct.isCancellationRequested) {
				// ignore, back to the loop
			} else {
				// continue normally
				dequeMutex.release();
				acq.cancelHandle.close();
				cont.resume(null, null);
				return;
			}
		}
	}
}
