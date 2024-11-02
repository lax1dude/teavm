/*
 *  Copyright 2024 lax1dude.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.teavm.backend.wasm.intrinsics.gc;

import org.teavm.ast.InvocationExpr;
import org.teavm.backend.wasm.model.expression.WasmCall;
import org.teavm.backend.wasm.model.expression.WasmCopy;
import org.teavm.backend.wasm.model.expression.WasmExpression;
import org.teavm.backend.wasm.model.expression.WasmFill;
import org.teavm.backend.wasm.model.expression.WasmInt32Constant;
import org.teavm.backend.wasm.model.expression.WasmUnreachable;
import org.teavm.interop.Address;
import org.teavm.model.MethodReference;
import org.teavm.runtime.LaxMalloc;

public class DirectMallocIntrinsic implements WasmGCIntrinsic {
    private static final MethodReference LAX_MALLOC = new MethodReference(LaxMalloc.class, "laxMalloc", int.class,
            Address.class);
    private static final MethodReference LAX_CALLOC = new MethodReference(LaxMalloc.class, "laxCalloc", int.class,
            Address.class);
    private static final MethodReference LAX_FREE = new MethodReference(LaxMalloc.class, "laxFree", Address.class,
            void.class);

    @Override
    public WasmExpression apply(InvocationExpr invocation, WasmGCIntrinsicContext manager) {
        switch (invocation.getMethod().getName()) {
            case "malloc": {
                var function = manager.functions().forStaticMethod(LAX_MALLOC);
                var call = new WasmCall(function);
                call.getArguments().add(manager.generate(invocation.getArguments().get(0)));
                return call;
            }
            case "calloc": {
                var function = manager.functions().forStaticMethod(LAX_CALLOC);
                var call = new WasmCall(function);
                call.getArguments().add(manager.generate(invocation.getArguments().get(0)));
                return call;
            }
            case "free": {
                var function = manager.functions().forStaticMethod(LAX_FREE);
                var call = new WasmCall(function);
                call.getArguments().add(manager.generate(invocation.getArguments().get(0)));
                return call;
            }
            case "memcpy": {
                var copy = new WasmCopy();
                copy.setDestinationIndex(manager.generate(invocation.getArguments().get(0)));
                copy.setSourceIndex(manager.generate(invocation.getArguments().get(1)));
                copy.setCount(manager.generate(invocation.getArguments().get(2)));
                return copy;
            }
            case "memset": {
                var fill = new WasmFill();
                fill.setIndex(manager.generate(invocation.getArguments().get(0)));
                fill.setValue(manager.generate(invocation.getArguments().get(1)));
                fill.setCount(manager.generate(invocation.getArguments().get(2)));
                return fill;
            }
            case "zmemset": {
                var fill = new WasmFill();
                fill.setIndex(manager.generate(invocation.getArguments().get(0)));
                fill.setValue(new WasmInt32Constant(0));
                fill.setCount(manager.generate(invocation.getArguments().get(1)));
                return fill;
            }
            default:
                return new WasmUnreachable();
        }
    }

}
