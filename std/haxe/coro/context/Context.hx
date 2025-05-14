package haxe.coro.context;

abstract Context(Array<Element>) {
	public function new() {
		this = [];
	}

	public function add<T:Element>(value:T) {
		this[value.id] = value;
	}

	public function clone():Context {
		return cast this;
	}

	public function set<T:Element>(key:Key<T>, value:T):Void {
		this[key.id] = value;
	}

	public function get<T>(key:Key<T>):T {
		return cast this[key.id];
	}
}