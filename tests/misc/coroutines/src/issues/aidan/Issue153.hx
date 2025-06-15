package issues.aidan;

import hxcoro.ds.PagedDeque;

class Issue153 extends utest.Test {
	public function test() {
		function expect<T>(expected:Array<T>, d:Page<Any>, ?pos:haxe.PosInfos) {
			final actual = [for (x in d.data) x];
			Assert.same(expected, actual, true, null, null, pos);
		}

		var d:PagedDeque<Any> = new PagedDeque(9);
		d.push(0);
		d.push(1);
		d.push(2);
		d.push(3);
		final page = d.push(4);
		final nnull = #if cpp 0 #else null #end; // I don't get it though
		expect([0, 1, 2, 3, 4, nnull, nnull, nnull, nnull], page);
		// delete non-existing
		Assert.isFalse(page.delete(5));
		Assert.isFalse(d.isEmpty());
		expect([0, 1, 2, 3, 4, nnull, nnull, nnull, nnull], page);
		// delete first
		Assert.isTrue(page.delete(0));
		Assert.isFalse(d.isEmpty());
		expect([1, 2, 3, 4, nnull, nnull, nnull, nnull, nnull], page);
		// delete last
		Assert.isTrue(page.delete(4));
		Assert.isFalse(d.isEmpty());
		expect([1, 2, 3, nnull, nnull, nnull, nnull, nnull, nnull], page);
		// delete middle
		Assert.isTrue(page.delete(2));
		Assert.isFalse(d.isEmpty());
		expect([1, 3, nnull, nnull, nnull, nnull, nnull, nnull, nnull], page);
		// push afterwards
		d.push(5);
		Assert.isFalse(d.isEmpty());
		expect([1, 3, 5, nnull, nnull, nnull, nnull, nnull, nnull], page);
		// drain
		Assert.isTrue(page.delete(1));
		Assert.isTrue(page.delete(3));
		Assert.isTrue(page.delete(5));
		Assert.isTrue(d.isEmpty());
		// push after empty
		d.push(6);
		Assert.isFalse(d.isEmpty());
		Assert.equals(6, d.pop());
		Assert.isTrue(d.isEmpty());
	}
}