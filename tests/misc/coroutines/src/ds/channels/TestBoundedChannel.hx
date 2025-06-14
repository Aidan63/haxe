package ds.channels;

import hxcoro.ds.channels.Channel;
import haxe.exceptions.ArgumentException;

class TestBoundedChannel extends utest.Test {
	public function test_creating() {
		Assert.notNull(Channel.create(Bounded(3)));
	}

	public function test_invalid_size() {
		Assert.raises(() -> Channel.create(Bounded(0)), ArgumentException);
	}
}