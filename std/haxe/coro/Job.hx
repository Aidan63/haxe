package haxe.coro;

import haxe.exceptions.NotImplementedException;

class Job {
    final parent : Null<Job>;

    final children : Array<Job>;

    final completionCallbacks : Array<()->Void>;

    var completedChildren : Int;

    public var completed (get, never) : Bool;

    function get_completed() {
        return completedChildren == children.length;
    }

    public function new(parent, callback) {
        this.parent = parent;
        
        children            = [];
        completionCallbacks = [ callback ];
        completedChildren   = 0;
    }

    public function create() {
        final child = new Job(this, onChildCompleted);

        children.push(child);

        return child;
    }

    public function complete<T>(v:T) {
        if (completed) {
            for (callback in completionCallbacks) {
                callback();
            }
        }
    }

    public function completeExceptionally(exn:Exception) {
        throw new NotImplementedException();
    }

    // @:coroutine public function wait() {
    //     if (completed) {
    //         return;
    //     }

    //     Coroutine.suspend(cont -> {
    //         onComplete(() -> cont.resume(null, null));
    //     });
    // }

    function onChildCompleted() {
        completedChildren++;

        if (completed) {
            for (callback in completionCallbacks) {
                callback();
            }
        }
    }
}