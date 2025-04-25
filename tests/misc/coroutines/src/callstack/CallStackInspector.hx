package callstack;

import haxe.CallStack;

enum CallStackInspect {
	File(file:String);
	Line(line:Int);
	Skip(file:String);
}

class CallStackInspectorFailure extends haxe.Exception {
	public function new(reason:String) {
		super(reason);
	}
}

class CallStackInspector {
	final stack:Array<StackItem>;
	var offset:Int;
	var expectedFile:Null<String>;
	var performedTests:Int;

	public function new(stack:Array<StackItem>) {
		this.stack = stack;
		offset = 0;
	}

	public function inspect(items:Array<CallStackInspect>) {
		try {
			for (item in items) {
				doInspect(item);
			}
			return null;
		} catch (e:CallStackInspectorFailure) {
			return e;
		}
	}

	function fail(reason:String) {
		throw new CallStackInspectorFailure('Failure at stack item $offset: $reason');
	}

	function doInspect(inspect:CallStackInspect) {
		switch (inspect) {
			case File(file):
				this.expectedFile = file;
			case Line(expectedLine):
				final index = offset++;
				switch (stack[index]) {
					case FilePos(_, file, line):
						if (file != expectedFile) {
							fail('file $file should be $expectedFile');
						}
						performedTests++;
						if (line != expectedLine) {
							fail('line $line should be $expectedLine');
						}
						performedTests++;
					case v:
						fail('$v should be FilePos');
				}
			case Skip(file):
				while (true) {
					if (offset == stack.length) {
						fail('$offset went out of bounds while skipping until $file');
					}
					switch (stack[offset]) {
						case FilePos(_, file2, _) if (file == file2):
							expectedFile = file;
							break;
						case _:
							offset++;
					}
				}
		}
	}
}