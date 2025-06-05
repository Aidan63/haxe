package hxcoro.task.node;

import haxe.Exception;
import haxe.exceptions.CancellationException;
import hxcoro.task.AbstractTask;
import hxcoro.task.CoroTask;

interface INodeStrategy {
	function complete<T, C>(task:CoroTask<T, C>):Void;
	function childrenCompleted<T, C>(task:CoroTask<T, C>):Void;
	function childSucceeds<T, C>(task:CoroTask<T, C>, child:AbstractTask<C>):Void;
	function childErrors<T, C>(task:CoroTask<T, C>, child:AbstractTask<C>, cause:Exception):Void;
	function childCancels<T, C>(task:CoroTask<T, C>, child:AbstractTask<C>, cause:CancellationException):Void;
}
