/*
 *  Copyright 2016 Alexey Andreev.
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
package org.teavm.backend.wasm.model.expression;

public class WasmDefaultExpressionVisitor implements WasmExpressionVisitor {
    @Override
    public void visit(WasmBlock expression) {
        for (WasmExpression part : expression.getBody()) {
            part.acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmBranch expression) {
        expression.getCondition().acceptVisitor(this);
        if (expression.getResult() != null) {
            expression.getResult().acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmNullBranch expression) {
        expression.getValue().acceptVisitor(this);
        if (expression.getResult() != null) {
            expression.getResult().acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmCastBranch expression) {
        expression.getValue().acceptVisitor(this);
        if (expression.getResult() != null) {
            expression.getResult().acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmBreak expression) {
        if (expression.getResult() != null) {
            expression.getResult().acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmSwitch expression) {
        expression.getSelector().acceptVisitor(this);
    }

    @Override
    public void visit(WasmConditional expression) {
        expression.getCondition().acceptVisitor(this);
        for (WasmExpression part : expression.getThenBlock().getBody()) {
            part.acceptVisitor(this);
        }
        for (WasmExpression part : expression.getElseBlock().getBody()) {
            part.acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmReturn expression) {
        if (expression.getValue() != null) {
            expression.getValue().acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmUnreachable expression) {
    }

    @Override
    public void visit(WasmInt32Constant expression) {
    }

    @Override
    public void visit(WasmInt64Constant expression) {
    }

    @Override
    public void visit(WasmFloat32Constant expression) {
    }

    @Override
    public void visit(WasmFloat64Constant expression) {
    }

    @Override
    public void visit(WasmNullConstant expression) {
    }

    @Override
    public void visit(WasmIsNull expression) {
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmGetLocal expression) {
    }

    @Override
    public void visit(WasmSetLocal expression) {
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmGetGlobal expression) {
    }

    @Override
    public void visit(WasmSetGlobal expression) {
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmIntBinary expression) {
        expression.getFirst().acceptVisitor(this);
        expression.getSecond().acceptVisitor(this);
    }

    @Override
    public void visit(WasmFloatBinary expression) {
        expression.getFirst().acceptVisitor(this);
        expression.getSecond().acceptVisitor(this);
    }

    @Override
    public void visit(WasmIntUnary expression) {
        expression.getOperand().acceptVisitor(this);
    }

    @Override
    public void visit(WasmFloatUnary expression) {
        expression.getOperand().acceptVisitor(this);
    }

    @Override
    public void visit(WasmConversion expression) {
        expression.getOperand().acceptVisitor(this);
    }

    @Override
    public void visit(WasmCall expression) {
        for (WasmExpression argument : expression.getArguments()) {
            argument.acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmIndirectCall expression) {
        expression.getSelector().acceptVisitor(this);
        for (WasmExpression argument : expression.getArguments()) {
            argument.acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmCallReference expression) {
        expression.getFunctionReference().acceptVisitor(this);
        for (var argument : expression.getArguments()) {
            argument.acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmDrop expression) {
        expression.getOperand().acceptVisitor(this);
    }

    @Override
    public void visit(WasmLoadInt32 expression) {
        expression.getIndex().acceptVisitor(this);
    }

    @Override
    public void visit(WasmLoadInt64 expression) {
        expression.getIndex().acceptVisitor(this);
    }

    @Override
    public void visit(WasmLoadFloat32 expression) {
        expression.getIndex().acceptVisitor(this);
    }

    @Override
    public void visit(WasmLoadFloat64 expression) {
        expression.getIndex().acceptVisitor(this);
    }

    @Override
    public void visit(WasmStoreInt32 expression) {
        expression.getIndex().acceptVisitor(this);
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmStoreInt64 expression) {
        expression.getIndex().acceptVisitor(this);
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmStoreFloat32 expression) {
        expression.getIndex().acceptVisitor(this);
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmStoreFloat64 expression) {
        expression.getIndex().acceptVisitor(this);
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmMemoryGrow expression) {
        expression.getAmount().acceptVisitor(this);
    }

    @Override
    public void visit(WasmFill expression) {
        expression.getIndex().acceptVisitor(this);
        expression.getValue().acceptVisitor(this);
        expression.getCount().acceptVisitor(this);
    }

    @Override
    public void visit(WasmCopy expression) {
        expression.getDestinationIndex().acceptVisitor(this);
        expression.getSourceIndex().acceptVisitor(this);
        expression.getCount().acceptVisitor(this);
    }

    @Override
    public void visit(WasmTry expression) {
        for (var part : expression.getBody()) {
            part.acceptVisitor(this);
        }
        for (var catchClause : expression.getCatches()) {
            for (var part : catchClause.getBody()) {
                part.acceptVisitor(this);
            }
        }
    }

    @Override
    public void visit(WasmThrow expression) {
        for (var arg : expression.getArguments()) {
            arg.acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmReferencesEqual expression) {
        expression.getFirst().acceptVisitor(this);
        expression.getSecond().acceptVisitor(this);
    }

    @Override
    public void visit(WasmCast expression) {
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmTest expression) {
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmExternConversion expression) {
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmStructNew expression) {
        for (var initializer : expression.getInitializers()) {
            initializer.acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmStructNewDefault expression) {
    }

    @Override
    public void visit(WasmStructGet expression) {
        expression.getInstance().acceptVisitor(this);
    }

    @Override
    public void visit(WasmStructSet expression) {
        expression.getInstance().acceptVisitor(this);
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmArrayNewDefault expression) {
        expression.getLength().acceptVisitor(this);
    }

    @Override
    public void visit(WasmArrayNewFixed expression) {
        for (var element : expression.getElements()) {
            element.acceptVisitor(this);
        }
    }

    @Override
    public void visit(WasmArrayGet expression) {
        expression.getInstance().acceptVisitor(this);
        expression.getIndex().acceptVisitor(this);
    }

    @Override
    public void visit(WasmArraySet expression) {
        expression.getInstance().acceptVisitor(this);
        expression.getIndex().acceptVisitor(this);
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmArrayLength expression) {
        expression.getInstance().acceptVisitor(this);
    }

    @Override
    public void visit(WasmArrayCopy expression) {
        expression.getTargetArray().acceptVisitor(this);
        expression.getTargetIndex().acceptVisitor(this);
        expression.getSourceArray().acceptVisitor(this);
        expression.getSourceIndex().acceptVisitor(this);
        expression.getSize().acceptVisitor(this);
    }

    @Override
    public void visit(WasmFunctionReference expression) {
    }

    @Override
    public void visit(WasmInt31Reference expression) {
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmInt31Get expression) {
        expression.getValue().acceptVisitor(this);
    }

    @Override
    public void visit(WasmPush expression) {
        expression.getArgument().acceptVisitor(this);
    }

    @Override
    public void visit(WasmPop expression) {
    }
}
