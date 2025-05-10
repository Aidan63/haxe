package haxe.coro;

import haxe.exceptions.NotImplementedException;

private enum abstract JobState(Int) {
    final Running;
    final AwaitingChildren;
    final Completed;
}

class Job {
    final parent : Null<Job>;

    final children : Array<Job>;

    final completionCallbacks : Array<()->Void>;

    var state : JobState;

    var completedChildren : Int;

    public var completed (get, never) : Bool;

    function get_completed() {
        return state == Completed;
    }

    public function new(parent, callback) {
        this.parent = parent;
        
        state               = Running;
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
        if (children.length == 0 || children.length == completedChildren) {
            state = Completed;

            for (callback in completionCallbacks) {
                callback();
            }
        } else {
            state = AwaitingChildren;
        }
    }

    public function completeExceptionally(exn:Exception) {
        throw new NotImplementedException();
    }

    @:coroutine public function await() {
        Coroutine.suspend(cont -> {
            if (completed) {
                cont.resume(null, null);
            } else {
                completionCallbacks.push(() -> cont.resume(null, null));
            }
        });
    }

    function onChildCompleted() {
        completedChildren++;

        if (state == AwaitingChildren && children.length == completedChildren) {
            state = Completed;

            for (callback in completionCallbacks) {
                callback();
            }
        }
    }
}