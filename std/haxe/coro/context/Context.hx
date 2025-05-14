package haxe.coro.context;

abstract Context(Array<Any>) {
	public function new() {
		this = [];
	}

	public function set<T:Element>(key:Key<T>, value:T):Void {
		this[key.id] = value;
	}

	public function get<T>(key:Key<T>):T {
		return cast this[key.id];
	}
}