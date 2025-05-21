package haxe.coro.context;

import haxe.ds.BalancedTree;

class ElementTree extends BalancedTree<Key<Any>, IElement<Any>> {
	override function compare(k1:Key<Any>, k2:Key<Any>) {
		return k2.id - k1.id;
	}

	override function copy():ElementTree {
		var copied = new ElementTree();
		copied.root = root;
		return copied;
	}

	override function toString() {
		var buf = new StringBuf();
		var first = true;
		for (key => value in this) {
			if (!first) {
				buf.add(", ");
			} else {
				first = false;
			}
			buf.add('${key.name}: $value');
		}
		return buf.toString();
	}
}

abstract Context(ElementTree) {
	public function new(tree:ElementTree) {
		this = tree;
	}

	public function clone() {
		return new Context(this.copy());
	}

	public function with(...elements:IElement<Any>) {
		var tree = this.copy();
		for (element in elements) {
			tree.set(element.getKey(), element);
		}
		return new Context(tree);
	}

	public function get<T>(key:Key<T>):T {
		return cast this.get(key);
	}

	public function toString() {
		return this.toString();
	}

	static public function empty() {
		return new Context(new ElementTree());
	}

	static public function create(...elements:IElement<Any>) {
		return empty().with(...elements);
	}
}