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

	function createTwoPageDeck(pageSize:Int) {
		var d:PagedDeque<Any> = new PagedDeque(pageSize);
		final pages = [
			for (i in 0...pageSize << 1) {
				d.push(i);
			}
		];
		return {
			deque: d,
			pages: pages
		}
	}

	public function testBounds1() {
		final data = createTwoPageDeck(1);
		final pages = data.pages;
		final d = data.deque;
		Assert.notEquals(pages[0], pages[1]);
		Assert.isFalse(pages[0].delete(1));
		Assert.isFalse(pages[1].delete(0));
		// delete last, then push
		Assert.isTrue(pages[1].delete(1));
		d.push(2);
		Assert.equals(0, d.pop());
		Assert.equals(2, d.pop());
		Assert.isTrue(d.isEmpty());
	}

	public function testBounds2() {
		final data = createTwoPageDeck(2);
		final pages = data.pages;
		final d = data.deque;
		Assert.equals(pages[0], pages[1]);
		Assert.equals(pages[2], pages[3]);
		Assert.notEquals(pages[0], pages[2]);
		Assert.isFalse(pages[0].delete(2));
		Assert.isFalse(pages[0].delete(3));
		Assert.isFalse(pages[2].delete(0));
		Assert.isFalse(pages[2].delete(1));
		// delete first and last
		Assert.isTrue(pages[0].delete(0));
		Assert.isTrue(pages[2].delete(3));
		Assert.equals(1, d.pop());
		Assert.equals(2, d.pop());
		Assert.isTrue(d.isEmpty());
	}

	public function testBounds3() {
		final data = createTwoPageDeck(3);
		final pages = data.pages;
		final d = data.deque;
		// delete middle
		Assert.isTrue(pages[0].delete(1));
		Assert.isTrue(pages[3].delete(4));
		Assert.equals(0, d.pop());
		Assert.equals(2, d.pop());
		Assert.equals(3, d.pop());
		Assert.equals(5, d.pop());
		Assert.isTrue(d.isEmpty());
	}

	public function testWildDeletion() {
		final data = createTwoPageDeck(100);
		final pages = data.pages;
		final page1 = pages[0];
		final page2 = pages[100];
		final d = data.deque;
		final values = [for (i in 0...200) i];
		values.sort((_, _) -> Math.random() > 0.5 ? 1 : -1);
		Assert.isFalse(d.isEmpty());
		for (i in values) {
			switch [page1.delete(i), page2.delete(i)] {
				case [true, false] | [false, true]:
				case [true, true]:
					Assert.fail('Deleted $i from two pages');
				case [false, false]:
					Assert.fail('Couldn\'t delete $i from any page');
			}
		}
		Assert.isTrue(d.isEmpty());
	}

	public function testDeleteDelete() {
		// delete + delete
		final d = new PagedDeque(1);
		final page1 = d.push(1);
		final page2 = d.push(2);
		Assert.isTrue(page1.delete(1));
		Assert.isTrue(page2.delete(2));
		Assert.isTrue(d.isEmpty());
		// again
		final page1 = d.push(1);
		final page2 = d.push(2);
		Assert.isTrue(page1.delete(1));
		Assert.isTrue(page2.delete(2));
		Assert.isTrue(d.isEmpty());
	}

	public function testDeletePop() {
		// delete + pop
		final d = new PagedDeque(1);
		final page1 = d.push(1);
		d.push(2);
		Assert.isTrue(page1.delete(1));
		Assert.equals(2, d.pop());
		Assert.isTrue(d.isEmpty());
		// again (TODO: broken)
		// final page1 = d.push(1);
		// d.push(2);
		// Assert.isTrue(page1.delete(1));
		// Assert.equals(2, d.pop());
		// Assert.isTrue(d.isEmpty());
	}

	public function testPopDelete() {
		// delete + pop
		final d = new PagedDeque(1);
		d.push(1);
		final page1 = d.push(2);
		Assert.equals(1, d.pop());
		Assert.isTrue(page1.delete(2));
		Assert.isTrue(d.isEmpty());
		// again
		d.push(1);
		final page1 = d.push(2);
		Assert.equals(1, d.pop());
		Assert.isTrue(page1.delete(2));
		Assert.isTrue(d.isEmpty());
	}
}