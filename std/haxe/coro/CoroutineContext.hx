package haxe.coro;

import haxe.coro.context.Key;
import haxe.coro.context.Element;

abstract CoroutineContext(Map<String, Any>) {
    public static var empty (get, never) : CoroutineContext;

    static function get_empty() {
        return new CoroutineContext();
    }

    public function get<T>(key:Key<T>):T {
        return cast this.get(key.id);
    }

    @:op(A + B)
    public function addElement<T>(rhs : Element<T>):CoroutineContext {
        final dst = this.copy();

        dst.set(rhs.id, rhs);

        return cast dst;
    }

    @:op(A + B)
    public function addCoroutineContext<T>(rhs : CoroutineContext):CoroutineContext {
        final src = (cast rhs : Map<String, Any>);
        final dst = this.copy();

        for (key => value in src) {
            dst.set(key, value);
        }

        return cast dst;
    }

    //

    public function new() {
        this = [];
    }

    function set<T>(element:Element<T>):Void {
        this.set(element.id, element);
    }
}