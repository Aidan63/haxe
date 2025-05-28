package haxe.coro.schedulers;

import haxe.exceptions.ArgumentException;

class VirtualTimeScheduler extends EventLoopScheduler {
	var currentTime : Float;

	public function new() {
		super();

		currentTime = 0;
	}

	public override function now() {
		return currentTime;
	}

	public function advanceBy(ms:Float) {
		if (ms < 0) {
			throw new ArgumentException("Time must be greater or equal to zero");
		}

		currentTime += ms;

		run();
	}

	public function advanceTo(ms:Float) {
		if (ms < 0) {
			throw new ArgumentException("Time must be greater or equal to zero");
		}
		if (ms < currentTime) {
			throw new ArgumentException("Cannot travel back in time");
		}

		currentTime = ms;

		run();
	}
}