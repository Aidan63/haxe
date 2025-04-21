package haxe.coro;

import haxe.CallStack.StackItem;

interface IStackFrame {
    var _hx_stackItem : StackItem;

    function callerFrame():Null<IStackFrame>;
}