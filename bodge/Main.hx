package bodge;

import haxe.coro.Coroutine;
import haxe.coro.Coroutine.delay;

function main() {
    Coroutine.runScoped(scope -> {
        
        final _ = scope.start(_ -> {
            delay(500);

            trace('Hello, ');
        });

        final _ = scope.start(_ -> {
            delay(1000);

            trace('World!');
        });

    });
}