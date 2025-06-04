package issues.aidan;

import haxe.coro.Coroutine;
import haxe.coro.context.Context;
import hxcoro.task.ICoroTask;
import hxcoro.task.CoroScopeTask;
import hxcoro.ds.Channel;

interface IReceiver<T> extends ICoroTask<haxe.Unit> {
	@:coroutine function receive():T;
}

interface ISender<T> {
	@:coroutine function send(v:T):Void;
}

class CoroChannelTask<T> extends CoroScopeTask<haxe.Unit> implements IReceiver<T> implements ISender<T> {
	final channel:Channel<T>;

	public function new(context:Context, channel:Channel<T>) {
		super(context);
		this.channel = channel;
	}

	@:coroutine public function receive() {
		return channel.read();
	}

	@:coroutine public function send(v:T) {
		return channel.write(v);
	}
}

function produce<T>(context:Context, lambda:Coroutine<ISender<T>->Void>):IReceiver<T> {
	final channel = new Channel(3);
	final task = new CoroChannelTask(context, channel);
	task.start();
	final result = lambda(task, task);
	switch result.state {
		case Pending:

		case Returned:
			task.resume(result.result, null);
		case Thrown:
			task.resume(null, result.error);
	}
	return task;
}

function produceNumbers(context:Context) {
	return produce(context, node -> {
		var i = 1;
		while (true) {
			node.send(i++);
		}
	});
}

function square(context:Context, numbers:IReceiver<Int>) {
	return produce(context, node -> {
		while (true) {
			var x = numbers.receive();
			node.send(x * x);
		}
	});
}

class Issue124 extends utest.Test {
	function test() {
		final result = CoroRun.runScoped(node -> {
			final numbers = produceNumbers(node.context);
			final squares = square(node.context, numbers);
			final result = [for (i in 1...10) {
				squares.receive();
			}];
			node.cancelChildren();
			result;
		});
		Assert.same([1, 4, 9, 16, 25, 36, 49, 64, 81], result);
	}
}