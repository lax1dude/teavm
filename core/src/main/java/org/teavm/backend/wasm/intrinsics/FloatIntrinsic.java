/*
 *  Copyright 2018 Alexey Andreev.
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
package org.teavm.backend.wasm.intrinsics;

import org.teavm.ast.InvocationExpr;
import org.teavm.backend.wasm.model.WasmLocal;
import org.teavm.backend.wasm.model.WasmNumType;
import org.teavm.backend.wasm.model.WasmType;
import org.teavm.backend.wasm.model.expression.WasmBlock;
import org.teavm.backend.wasm.model.expression.WasmBranch;
import org.teavm.backend.wasm.model.expression.WasmConversion;
import org.teavm.backend.wasm.model.expression.WasmDrop;
import org.teavm.backend.wasm.model.expression.WasmExpression;
import org.teavm.backend.wasm.model.expression.WasmFloat32Constant;
import org.teavm.backend.wasm.model.expression.WasmGetLocal;
import org.teavm.backend.wasm.model.expression.WasmInt32Constant;
import org.teavm.backend.wasm.model.expression.WasmIntBinary;
import org.teavm.backend.wasm.model.expression.WasmIntBinaryOperation;
import org.teavm.backend.wasm.model.expression.WasmIntType;
import org.teavm.backend.wasm.model.expression.WasmSetLocal;
import org.teavm.model.MethodReference;

public class FloatIntrinsic implements WasmIntrinsic {
    private static final int EXPONENT_BITS = 0x7F800000;
    private static final int FRACTION_BITS = 0x007FFFFF;

    @Override
    public boolean isApplicable(MethodReference methodReference) {
        if (!methodReference.getClassName().equals(Float.class.getName())) {
            return false;
        }

        switch (methodReference.getName()) {
            case "getNaN":
            case "isNaN":
            case "isInfinite":
            case "isFinite":
            case "floatToRawIntBits":
            case "intBitsToFloat":
                return true;
            default:
                return false;
        }
    }

    @Override
    public WasmExpression apply(InvocationExpr invocation, WasmIntrinsicManager manager) {
        switch (invocation.getMethod().getName()) {
            case "getNaN":
                return new WasmFloat32Constant(Float.NaN);
            case "isNaN":
                return testNaN(manager.generate(invocation.getArguments().get(0)), manager);
            case "isInfinite":
                return testIsInfinite(manager.generate(invocation.getArguments().get(0)));
            case "isFinite":
                return testIsFinite(manager.generate(invocation.getArguments().get(0)));
            case "floatToRawIntBits": {
                WasmConversion conversion = new WasmConversion(WasmNumType.FLOAT32, WasmNumType.INT32, false,
                        manager.generate(invocation.getArguments().get(0)));
                conversion.setReinterpret(true);
                return conversion;
            }
            case "intBitsToFloat": {
                WasmConversion conversion = new WasmConversion(WasmNumType.INT32, WasmNumType.FLOAT32, false,
                        manager.generate(invocation.getArguments().get(0)));
                conversion.setReinterpret(true);
                return conversion;
            }
            default:
                throw new AssertionError();
        }
    }

    private WasmExpression testNaN(WasmExpression expression, WasmIntrinsicManager manager) {
        WasmLocal bitsVar = manager.getTemporary(WasmType.INT32);
        WasmBlock block = new WasmBlock(false);
        block.setType(WasmType.INT32.asBlock());

        WasmConversion conversion = new WasmConversion(WasmNumType.FLOAT32, WasmNumType.INT32, false, expression);
        conversion.setReinterpret(true);
        block.getBody().add(new WasmSetLocal(bitsVar, conversion));

        WasmExpression exponentBits = new WasmIntBinary(WasmIntType.INT32, WasmIntBinaryOperation.AND,
                new WasmGetLocal(bitsVar), new WasmInt32Constant(EXPONENT_BITS));
        WasmExpression fractionBits = new WasmIntBinary(WasmIntType.INT32, WasmIntBinaryOperation.AND,
                new WasmGetLocal(bitsVar), new WasmInt32Constant(FRACTION_BITS));
        WasmExpression testExponent = new WasmIntBinary(WasmIntType.INT32, WasmIntBinaryOperation.NE,
                exponentBits, new WasmInt32Constant(EXPONENT_BITS));
        WasmExpression testFraction = new WasmIntBinary(WasmIntType.INT32, WasmIntBinaryOperation.NE,
                fractionBits, new WasmInt32Constant(0));

        WasmBranch breakIfWrongExponent = new WasmBranch(testExponent, block);
        breakIfWrongExponent.setResult(new WasmInt32Constant(0));
        block.getBody().add(new WasmDrop(breakIfWrongExponent));

        manager.releaseTemporary(bitsVar);

        block.getBody().add(testFraction);
        return block;
    }

    private WasmExpression testIsInfinite(WasmExpression expression) {
        var conversion = new WasmConversion(WasmNumType.FLOAT32, WasmNumType.INT32, false, expression);
        conversion.setReinterpret(true);

        var result = new WasmIntBinary(WasmIntType.INT32, WasmIntBinaryOperation.AND,
                conversion, new WasmInt32Constant(EXPONENT_BITS));
        return new WasmIntBinary(WasmIntType.INT32, WasmIntBinaryOperation.EQ, result,
                new WasmInt32Constant(EXPONENT_BITS));
    }

    private WasmExpression testIsFinite(WasmExpression expression) {
        var conversion = new WasmConversion(WasmNumType.FLOAT32, WasmNumType.INT32, false, expression);
        conversion.setReinterpret(true);

        var result = new WasmIntBinary(WasmIntType.INT32, WasmIntBinaryOperation.AND,
                conversion, new WasmInt32Constant(EXPONENT_BITS));
        return new WasmIntBinary(WasmIntType.INT32, WasmIntBinaryOperation.NE, result,
                new WasmInt32Constant(EXPONENT_BITS));
    }
}
