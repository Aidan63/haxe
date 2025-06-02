package hxcoro.concurrent;

import haxe.coro.Mutex;

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

	public function compareExchange(expected:Int, replacement:Int) {
		this.mutex.acquire();
		if (this.value == expected) {
			this.value = replacement;
			this.mutex.release();
			return true;
		} else {
			this.mutex.release();
			return false;
		}
	}

	public function sub(b:Int) {
		this.mutex.acquire();
		final value = this.value;
		this.value -= b;
		this.mutex.release();
		return value;
	}

	public function add(b:Int) {
		this.mutex.acquire();
		this.value += b;
		this.mutex.release();
	}
}
