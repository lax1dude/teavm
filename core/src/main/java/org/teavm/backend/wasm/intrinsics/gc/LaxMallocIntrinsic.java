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

import java.util.ArrayList;
import java.util.List;
import org.teavm.ast.InvocationExpr;
import org.teavm.backend.wasm.model.expression.WasmExpression;
import org.teavm.backend.wasm.model.expression.WasmInt32Constant;
import org.teavm.backend.wasm.model.expression.WasmIntBinary;
import org.teavm.backend.wasm.model.expression.WasmIntBinaryOperation;
import org.teavm.backend.wasm.model.expression.WasmIntType;
import org.teavm.backend.wasm.model.expression.WasmMemoryGrow;

public class LaxMallocIntrinsic implements WasmGCIntrinsic {

    private final List<LaxMallocHeapMapper> addressList = new ArrayList<>();
    private final List<WasmInt32Constant> minAddrConstants = new ArrayList<>();
    private final List<WasmInt32Constant> maxAddrConstants = new ArrayList<>();

    @Override
    public WasmExpression apply(InvocationExpr invocation, WasmGCIntrinsicContext context) {
        switch (invocation.getMethod().getName()) {
            case "addrHeap": {
                WasmExpression value = context.generate(invocation.getArguments().get(0));
                if (value instanceof WasmInt32Constant) {
                    // if addrHeap is passed a constant i32, add the heap offset at compile time
                    final int memOffset = ((WasmInt32Constant) value).getValue();
                    WasmInt32Constant ret = new WasmInt32Constant(0);
                    addressList.add(heapLoc -> {
                        ret.setValue(heapLoc + memOffset);
                    });
                    return ret;
                } else {
                    WasmInt32Constant heapLocConst = new WasmInt32Constant(0);
                    WasmExpression calcOffset = new WasmIntBinary(WasmIntType.INT32, WasmIntBinaryOperation.ADD,
                            heapLocConst, value);
                    addressList.add(heapLocConst::setValue);
                    return calcOffset;
                }
            }
            case "growHeapOuter": {
                return new WasmMemoryGrow(context.generate(invocation.getArguments().get(0)));
            }
            case "getHeapMinAddr": {
                WasmInt32Constant ret = new WasmInt32Constant(0);
                minAddrConstants.add(ret);
                return ret;
            }
            case "getHeapMaxAddr": {
                WasmInt32Constant ret = new WasmInt32Constant(0);
                maxAddrConstants.add(ret);
                return ret;
            }
            default:
                throw new IllegalArgumentException(invocation.getMethod().toString());
        }
    }

    public void setHeapLocation(int heapLoc) {
        for (LaxMallocHeapMapper mapper : addressList) {
            mapper.setHeapLocation(heapLoc);
        }
    }

    private interface LaxMallocHeapMapper {
        void setHeapLocation(int heapLoc);
    }

    public void setHeapMinAddr(int heapSegmentMinAddr) {
        for (WasmInt32Constant ct : minAddrConstants) {
            ct.setValue(heapSegmentMinAddr);
        }
    }

    public void setHeapMaxAddr(int heapSegmentMaxAddr) {
        for (WasmInt32Constant ct : maxAddrConstants) {
            ct.setValue(heapSegmentMaxAddr);
        }
    }

}
