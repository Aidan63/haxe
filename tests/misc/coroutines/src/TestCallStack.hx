import callstack.CallStackInspector;

class TestCallStack extends utest.Test {
	function test() {
		try {
			callstack.Bottom.entry();
			Assert.fail("Exception expected");
		} catch(e:haxe.exceptions.NotImplementedException) {
			var inspector = new CallStackInspector(e.stack.asArray());
			var r = inspector.inspect([
				File("src/callstack/Top.hx"),
					Line(4),
					Line(8),
					Line(12),
				File("src/callstack/CoroUpper.hx"),
					Line(10),
					Line(8),
					Line(8),
					Line(8),
					Line(8),
					Line(17),
				Skip("src/callstack/SyncMiddle.hx"),
					Line(4),
					Line(8),
				File("src/callstack/CoroLower.hx"),
					Line(8),
				Skip("src/callstack/Bottom.hx"),
					Line(4)

			]);
			if (r == null) {
				Assert.pass();
			} else {
				Assert.fail(r.toString());
			}
		}
	}
}