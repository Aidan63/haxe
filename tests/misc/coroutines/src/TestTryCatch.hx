import haxe.coro.Coroutine.yield;
import Helper;

class TestTryCatch extends utest.Test {
	function testTryCatch() {
		Assert.same(["e1", "e2"], Coroutine.run(@:coroutine function run() {
			return mapCalls([ new E1(), new E2() ], tryCatch);
		}));
	}

	function testTryCatchFail() {
		Assert.raises(() -> Coroutine.run(@:coroutine function run() {
			return tryCatch(new E3());
		}), E3);
	}

	function testTryCatchNonExc() {
		Assert.same(["ne1", "ne2"], Coroutine.run(@:coroutine function run() {
			return mapCalls([ new NE1(), new NE2() ], tryCatchNonExc);
		}));
	}

	function testTryCatchNonExcFail() {
		Assert.raises(() -> Coroutine.run(@:coroutine function run() {
			return tryCatchNonExc(new NE3());
		}), NE3);
	}

	function testTryCatchMixed() {
		Assert.same(["e1", "e2", "ne1", "ne2"], Coroutine.run(@:coroutine function run() {
			return mapCalls(([ new E1(), new E2(), new NE1(), new NE2() ] : Array<Dynamic>), tryCatchMixed);
		}));
	}

	function testTryCatchMixedFail() {
		Assert.raises(() -> Coroutine.run(@:coroutine function run() {
			return tryCatchMixed("foo");
		}), String);
		Assert.raises(() -> Coroutine.run(@:coroutine function run() {
			return tryCatchMixed(new E3());
		}), E3);
		Assert.raises(() -> Coroutine.run(@:coroutine function run() {
			return tryCatchMixed(new NE3());
		}), NE3);
	}

	function testRecursion() {
		var maxIters = 3;
		var counter  = 0;

		@:coroutine function foo() {
			if (++counter < maxIters) {
				foo();
			}
		}

		Coroutine.run(foo);

		Assert.equals(counter, maxIters);
	}

	function testSuspendingRecursion() {
		var maxIters = 3;
		var counter  = 0;

		@:coroutine function foo() {
			if (++counter < maxIters) {
				yield();
				foo();
			}
		}

		Coroutine.run(foo);

		Assert.equals(counter, maxIters);
	}

	function testTryCatchNested() {
		@:coroutine function f(yield:Coroutine<Int -> Void>, throwValue:Dynamic) {
			var dummy = '1';
			try {
				try {
					dummy += '2';
					throw throwValue;
					dummy += '3';
				} catch (e:Int) {
					dummy += '4';
					yield(10);
					dummy += '5';
				}
				dummy += '6';
			} catch (e:Dynamic) {
				dummy += '7';
				yield(20);
				dummy += '8';
			}
			dummy += '9';
			return dummy;
		}
		var a = [];
		Assert.equals("124569", Coroutine.run(() -> f(i -> a.push(i), 1)));
		Assert.same([10], a);
		a = [];
		Assert.equals("12789", Coroutine.run(() -> f(i -> a.push(i), "foo")));
		Assert.same([20], a);
		a = [];
		Assert.equals("124789", Coroutine.run(() -> f(i -> i == 10 ? throw i : a.push(i), 1)));
		Assert.same([20], a);
	}

	@:coroutine function tryCatch(e:haxe.Exception) {
		try {
			throw e;
		} catch (e:E1) {
			return "e1";
		} catch (e:E2) {
			return "e2";
		}
		return "none";
	}

	@:coroutine function tryCatchNonExc(e:NE) {
		try {
			throw e;
		} catch (e:NE1) {
			return "ne1";
		} catch (e:NE2) {
			return "ne2";
		}
		return "none";
	}

	@:coroutine function tryCatchMixed(e:Any) {
		try {
			throw e;
		} catch (e:E1) {
			return "e1";
		} catch (e:E2) {
			return "e2";
		} catch (e:NE1) {
			return "ne1";
		} catch (e:NE2) {
			return "ne2";
		}
		return "none";
	}
}

private class E1 extends haxe.Exception {
	public function new() super("E1");
}
private class E2 extends haxe.Exception {
	public function new() super("E2");
}
private class E3 extends haxe.Exception {
	public function new() super("E3");
}

interface NE {}

private class NE1 implements NE {
	public function new() {};
}

private class NE2 implements NE {
	public function new() {};
}

private class NE3 implements NE {
	public function new() {};
}