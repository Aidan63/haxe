package issues.aidan;

import utest.Assert;
import haxe.Exception;

@:coroutine function foo() {
	suspend(cont -> {
		cont.resume(null, new Exception("error"));
	});
}

class Issue75 extends utest.Test {
    public function test() {
		var s = "";
		Coroutine.run(() -> {
			try {
				foo();
			} catch (_:Dynamic) {
				s += 'caught';
			}

			s += 'done';
		});
		Assert.equals("caughtdone", s);
    }
}