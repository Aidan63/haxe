import haxe.CallStack;

typedef ExpectedStackElement = {
	var file:String;
	var line:Int;
}

class TestCallStack extends utest.Test {

	function compare(offset:Int, expected:Array<ExpectedStackElement>, stack:Array<StackItem>) {
		for (expected in expected) {
			switch (stack[offset++]) {
				case FilePos(_, file, line):
					Assert.equals(expected.file, file);
					Assert.equals(expected.line, line);
				case _:
					Assert.fail("Expected FilePos");
			}
		}
		return offset;
	}

	function skipUntilFile(offset:Int, file:String, stack:Array<StackItem>) {
		while (true) {
			Assert.isTrue(offset < stack.length);
			switch (stack[offset]) {
				case FilePos(_, file2, _) if (file == file2):
					return offset;
				case _:
					offset++;
			}
		}
	}

	function test() {
		try {
			callstack.Bottom.entry();
			Assert.fail("Exception expected");
		} catch(e:haxe.exceptions.NotImplementedException) {
			var offset = 0;
			var stack = e.stack.asArray();
			var expected = [
				{file: "src/callstack/Top.hx", line: 4 },
				{file: "src/callstack/Top.hx", line: 8 },
				{file: "src/callstack/Top.hx", line: 12 },
				{file: "src/callstack/CoroUpper.hx", line: 10 },
				{file: "src/callstack/CoroUpper.hx", line: 8 },
				{file: "src/callstack/CoroUpper.hx", line: 8 },
				{file: "src/callstack/CoroUpper.hx", line: 8 },
				{file: "src/callstack/CoroUpper.hx", line: 8 },
				{file: "src/callstack/CoroUpper.hx", line: 17 }
			];
			offset = compare(offset, expected, stack);

			/*
				Skip until we're in SyncMiddle because what exactly happens in Coroutine.run
				stack-wise isn't properly defined at the moment.
			*/
			offset = skipUntilFile(offset, "src/callstack/SyncMiddle.hx", stack);

			var expected = [
				{file: "src/callstack/SyncMiddle.hx", line: 4},
				{file: "src/callstack/SyncMiddle.hx", line: 8},
				{file: "src/callstack/CoroLower.hx", line: 8}
			];
			offset = compare(offset, expected, stack);

			offset = skipUntilFile(offset, "src/callstack/Bottom.hx", stack);

			var expected = [
				{file: "src/callstack/Bottom.hx", line: 4},
				{file: "src/TestCallStack.hx", line: 37}, // breaks if this file is modified
			];
			offset = compare(offset, expected, stack);
		}
	}
}