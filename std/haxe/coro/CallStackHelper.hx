package haxe.coro;

import haxe.CallStack;

class CallStackHelper {
	static public function cullTopStack(items:Array<StackItem>, skip = 0) {
		final topStack = [];
		for (item in items) {
			if (skip-- > 0) {
				continue;
			}
			switch (item) {
				// TODO: this needs a better check
				case FilePos(_, _, -1, _):
					break;
				// this is a hack
				case FilePos(Method(_, "invokeResume"), _):
					break;
				case _:
					topStack.push(item);
			}
		}
		return topStack;
	}

	static public function takeStackItemsUntil(items:Array<StackItem>, until:StackItem) {
		final ret = [];
		switch (until) {
			case null:
				return items;
			case FilePos(_, file, line, _):
				for (item in items) {
					switch (item) {
						case FilePos(_, file2, line2, _) if (file == file2 && line == line2):
							return ret;
						case FilePos(Method(_, "invokeResume"), _):
							return items;
						case _:
							ret.push(item);
					}
				}
				return ret;
			case _:
				return items;
		}
	}
}