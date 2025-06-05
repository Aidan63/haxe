package hxcoro.task.node;

import haxe.Exception;
import haxe.exceptions.CancellationException;
import hxcoro.task.AbstractTask;
import hxcoro.task.CoroTask;

interface INodeStrategy<T, C> {
	function complete(task:CoroTask<T, C>):Void;
	function childrenCompleted(task:CoroTask<T, C>):Void;
	function childSucceeds(task:CoroTask<T, C>, child:AbstractTask<C>):Void;
	function childErrors(task:CoroTask<T, C>, child:AbstractTask<C>, cause:Exception):Void;
	function childCancels(task:CoroTask<T, C>, child:AbstractTask<C>, cause:CancellationException):Void;
}
