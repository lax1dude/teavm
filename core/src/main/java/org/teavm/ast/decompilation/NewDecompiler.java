/*
 *  Copyright 2021 Alexey Andreev.
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
package org.teavm.ast.decompilation;

import com.carrotsearch.hppc.IntArrayList;
import com.carrotsearch.hppc.IntStack;
import com.carrotsearch.hppc.ObjectIntHashMap;
import com.carrotsearch.hppc.ObjectIntMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import org.teavm.ast.AssignmentStatement;
import org.teavm.ast.BinaryExpr;
import org.teavm.ast.BinaryOperation;
import org.teavm.ast.BlockStatement;
import org.teavm.ast.BreakStatement;
import org.teavm.ast.ConditionalStatement;
import org.teavm.ast.ConstantExpr;
import org.teavm.ast.Expr;
import org.teavm.ast.IdentifiedStatement;
import org.teavm.ast.InvocationExpr;
import org.teavm.ast.InvocationType;
import org.teavm.ast.OperationType;
import org.teavm.ast.ReturnStatement;
import org.teavm.ast.SequentialStatement;
import org.teavm.ast.Statement;
import org.teavm.ast.UnaryExpr;
import org.teavm.ast.UnaryOperation;
import org.teavm.ast.WhileStatement;
import org.teavm.common.DominatorTree;
import org.teavm.common.Graph;
import org.teavm.common.GraphUtils;
import org.teavm.model.BasicBlock;
import org.teavm.model.Instruction;
import org.teavm.model.InvokeDynamicInstruction;
import org.teavm.model.Program;
import org.teavm.model.ValueType;
import org.teavm.model.Variable;
import org.teavm.model.instructions.ArrayLengthInstruction;
import org.teavm.model.instructions.AssignInstruction;
import org.teavm.model.instructions.BinaryBranchingInstruction;
import org.teavm.model.instructions.BinaryInstruction;
import org.teavm.model.instructions.BoundCheckInstruction;
import org.teavm.model.instructions.BranchingInstruction;
import org.teavm.model.instructions.CastInstruction;
import org.teavm.model.instructions.CastIntegerInstruction;
import org.teavm.model.instructions.CastNumberInstruction;
import org.teavm.model.instructions.ClassConstantInstruction;
import org.teavm.model.instructions.CloneArrayInstruction;
import org.teavm.model.instructions.ConstructArrayInstruction;
import org.teavm.model.instructions.ConstructInstruction;
import org.teavm.model.instructions.ConstructMultiArrayInstruction;
import org.teavm.model.instructions.DoubleConstantInstruction;
import org.teavm.model.instructions.EmptyInstruction;
import org.teavm.model.instructions.ExitInstruction;
import org.teavm.model.instructions.FloatConstantInstruction;
import org.teavm.model.instructions.GetElementInstruction;
import org.teavm.model.instructions.GetFieldInstruction;
import org.teavm.model.instructions.InitClassInstruction;
import org.teavm.model.instructions.InstructionVisitor;
import org.teavm.model.instructions.IntegerConstantInstruction;
import org.teavm.model.instructions.InvokeInstruction;
import org.teavm.model.instructions.IsInstanceInstruction;
import org.teavm.model.instructions.JumpInstruction;
import org.teavm.model.instructions.LongConstantInstruction;
import org.teavm.model.instructions.MonitorEnterInstruction;
import org.teavm.model.instructions.MonitorExitInstruction;
import org.teavm.model.instructions.NegateInstruction;
import org.teavm.model.instructions.NullCheckInstruction;
import org.teavm.model.instructions.NullConstantInstruction;
import org.teavm.model.instructions.NumericOperandType;
import org.teavm.model.instructions.PutElementInstruction;
import org.teavm.model.instructions.PutFieldInstruction;
import org.teavm.model.instructions.RaiseInstruction;
import org.teavm.model.instructions.StringConstantInstruction;
import org.teavm.model.instructions.SwitchInstruction;
import org.teavm.model.instructions.UnwrapArrayInstruction;
import org.teavm.model.util.DefinitionExtractor;
import org.teavm.model.util.ProgramUtils;
import org.teavm.model.util.UsageExtractor;

public class NewDecompiler {
    private Program program;
    private Graph cfg;
    private DominatorTree dom;
    private Graph domGraph;
    private UsageExtractor usageExtractor = new UsageExtractor();
    private DefinitionExtractor definitionExtractor = new DefinitionExtractor();
    private int[] dfs;
    private int[] varUsageCount;
    private int[] varDefinitionCount;
    private boolean[] varUsedOnce;
    private List<ExprStackElement> exprStack = new ArrayList<>();
    private Expr[] relocatableVars;
    private List<Statement> statements;
    private BasicBlock currentBlock;
    private boolean returnedVariableRelocatable;
    private IdentifiedStatement[] jumpTargets;
    private BasicBlock nextBlock;
    private WhileStatement[] loopExits;
    private ObjectIntMap<IdentifiedStatement> identifiedStatementUseCount = new ObjectIntHashMap<>();
    private boolean[] processingLoops;
    private boolean[] loopNodes;

    public Statement decompile(Program program) {
        this.program = program;
        prepare();
        currentBlock = program.basicBlockAt(0);
        statements = new ArrayList<>();
        nextBlock = null;
        calculateResult();
        Statement result;
        if (statements.size() != 1) {
            SequentialStatement seq = new SequentialStatement();
            seq.getSequence().addAll(statements);
            result = seq;
        } else {
            result = statements.get(0);
        }
        cleanup();
        return result;
    }

    private static int blockEnterNode(BasicBlock block) {
        return block.getIndex() * 2;
    }

    private static int blockExitNode(BasicBlock block) {
        return block.getIndex() * 2 + 1;
    }

    private int enteringBlockCount(BasicBlock block) {
        return cfg.incomingEdgesCount(block.getIndex() * 2);
    }

    private void prepare() {
        cfg = ProgramUtils.buildControlFlowGraph2(program);
        dfs = GraphUtils.dfs(cfg);
        dom = GraphUtils.buildDominatorTree(cfg);
        domGraph = GraphUtils.buildDominatorGraph(dom, cfg.size());
        relocatableVars = new Expr[program.variableCount()];
        jumpTargets = new IdentifiedStatement[program.basicBlockCount()];
        processingLoops = new boolean[program.basicBlockCount()];
        loopNodes = new boolean[program.basicBlockCount()];
        loopExits = new WhileStatement[program.basicBlockCount()];
        calculateVarInfo();
    }

    private void calculateVarInfo() {
        varUsageCount = new int[program.variableCount()];
        varDefinitionCount = new int[program.variableCount()];
        for (int i = 0; i < program.basicBlockCount(); ++i) {
            BasicBlock block = program.basicBlockAt(i);
            for (Instruction instruction : block) {
                instruction.acceptVisitor(usageExtractor);
                instruction.acceptVisitor(definitionExtractor);
                Variable[] usedVars = usageExtractor.getUsedVariables();
                if (usedVars != null) {
                    for (Variable usedVar : usedVars) {
                        varUsageCount[usedVar.getIndex()]++;
                    }
                }
                Variable[] defVars = definitionExtractor.getDefinedVariables();
                if (defVars != null) {
                    for (Variable defVar : defVars) {
                        varDefinitionCount[defVar.getIndex()]++;
                    }
                }
            }
            if (block.getExceptionVariable() != null) {
                varDefinitionCount[block.getExceptionVariable().getIndex()]++;
            }
        }
    }

    private void cleanup() {
        program = null;
        dom = null;
        cfg = null;
        dfs = null;
        statements = null;
        relocatableVars = null;
        jumpTargets = null;
        loopNodes = null;
        loopExits = null;
    }

    private void calculateResult() {
        while (currentBlock != null) {
            if (!processingLoops[currentBlock.getIndex()] && isLoopHead()) {
                processLoop();
            } else {
                for (Instruction instruction : currentBlock) {
                    instruction.acceptVisitor(instructionDecompiler);
                }
            }
        }
    }

    private void processLoop() {
        flushStack();
        List<Statement> statementsBackup = statements;
        BasicBlock nextBlockBackup = nextBlock;

        WhileStatement loop = new WhileStatement();
        BasicBlock loopExit = getBestLoopExit();
        if (loopExits[loopExit.getIndex()] != null) {
            loopExit = null;
        } else {
            loopExits[loopExit.getIndex()] = loop;
        }
        nextBlock = currentBlock;
        statements.add(loop);
        statements = loop.getBody();
        jumpTargets[currentBlock.getIndex()] = loop;
        processingLoops[currentBlock.getIndex()] = true;
        calculateResult();
        currentBlock = loopExit;
        exprStack.clear();
        optimizeLoop(loop);

        statements = statementsBackup;
        nextBlock = nextBlockBackup;
        if (loopExit != null) {
            loopExits[loopExit.getIndex()] = null;
        }
    }

    private void optimizeLoop(WhileStatement loop) {
        if (loop.getCondition() != null || loop.getBody().isEmpty()) {
            return;
        }
        Statement first = loop.getBody().get(0);
        if (!(first instanceof ConditionalStatement)) {
            return;
        }
        ConditionalStatement firstIf = (ConditionalStatement) first;
        if (!firstIf.getAlternative().isEmpty() || firstIf.getConsequent().size() != 1) {
            return;
        }
        Statement firstIfThen = firstIf.getConsequent().get(0);
        if (!(firstIfThen instanceof BreakStatement)) {
            return;
        }
        BreakStatement firstBreak = (BreakStatement) firstIfThen;
        if (firstBreak.getTarget() != loop) {
            return;
        }
        loop.getBody().remove(0);
        loop.setCondition(not(firstIf.getCondition()));
    }

    private BasicBlock getBestLoopExit() {
        fillLoopNodes();
        IntStack stack = new IntStack();
        stack.push(currentBlock.getIndex());
        IntArrayList nonLoopTargets = new IntArrayList();
        IntArrayList candidates = new IntArrayList();
        BasicBlock bestExit = null;
        int bestExitScore = 0;

        while (!stack.isEmpty()) {
            int node = stack.pop();
            int[] targets = domGraph.outgoingEdges(node * 2 + 1);

            int nonLoopTargetsIndex = 0;
            for (int target : targets) {
                if (!loopNodes[target / 2]) {
                    nonLoopTargets.add(target / 2);
                }
            }

            if (!nonLoopTargets.isEmpty()) {
                int bestNonLoopTarget = nonLoopTargets.get(0);
                for (int i = 1; i < nonLoopTargets.size(); ++i) {
                    int candidate = nonLoopTargets.get(i);
                    if (dfs[bestNonLoopTarget * 2] < dfs[candidate * 2]) {
                        bestNonLoopTarget = candidate;
                    }
                }
                nonLoopTargets.clear();
                int score = getComplexity(bestNonLoopTarget);
                if (score > bestExitScore) {
                    bestExitScore = score;
                    bestExit = program.basicBlockAt(bestNonLoopTarget);
                }
            }

            for (int target : targets) {
                if (loopNodes[target / 2]) {
                    stack.push(target / 2);
                }
            }
        }

        return bestExit;
    }

    private int getComplexity(int blockIndex) {
        int complexity = 0;
        IntStack stack = new IntStack();
        stack.push(blockIndex);
        boolean[] visited = new boolean[program.basicBlockCount()];
        while (!stack.isEmpty()) {
            blockIndex = stack.pop();
            if (visited[blockIndex]) {
                continue;
            }
            visited[blockIndex] = true;
            complexity += program.basicBlockAt(blockIndex).instructionCount();
            for (int successor : cfg.outgoingEdges(blockIndex * 2)) {
                int successorIndex = successor / 2;
                if (!visited[successorIndex]) {
                    stack.push(successorIndex);
                }
            }
            for (int successor : cfg.outgoingEdges(blockIndex * 2 + 1)) {
                int successorIndex = successor / 2;
                if (!visited[successorIndex]) {
                    stack.push(successorIndex);
                }
            }
        }
        return complexity;
    }

    private void fillLoopNodes() {
        Arrays.fill(loopNodes, false);
        int[] stack = new int[cfg.size()];
        int stackPtr = 0;
        stack[stackPtr++] = currentBlock.getIndex();

        while (stackPtr > 0) {
            int node = stack[--stackPtr];
            if (loopNodes[node]) {
                continue;
            }
            loopNodes[node] = true;
            for (int source : cfg.incomingEdges(node * 2)) {
                int sourceIndex = source / 2;
                if (!loopNodes[sourceIndex] && dom.dominates(blockEnterNode(currentBlock), source)) {
                    stack[stackPtr++] = sourceIndex;
                }
            }
        }
    }

    private boolean isLoopHead() {
        int enterNode = blockEnterNode(currentBlock);
        for (int source : cfg.incomingEdges(enterNode)) {
            if (dom.dominates(enterNode, source)) {
                return true;
            }
        }
        return false;
    }

    private void processBlock(BasicBlock block, BasicBlock next, List<Statement> statements) {
        BasicBlock currentBlockBackup = currentBlock;
        BasicBlock nextBlockBackup = nextBlock;
        List<ExprStackElement> stackBackup = exprStack;
        List<Statement> statementsBackup = this.statements;

        currentBlock = block;
        nextBlock = next;
        exprStack = new ArrayList<>();
        this.statements = statements;
        calculateResult();

        currentBlock = currentBlockBackup;
        nextBlock = nextBlockBackup;
        exprStack = stackBackup;
        this.statements = statementsBackup;
    }

    private void assignVariable(int variable, Expr value, boolean relocatable) {
        if (varUsageCount[variable] <= 1 && varDefinitionCount[variable] == 1) {
            if (relocatable) {
                relocatableVars[variable] = value;
            } else {
                exprStack.add(new ExprStackElement(variable, value));
            }
        } else {
            if (!relocatable) {
                flushStack();
            }
            AssignmentStatement statement = Statement.assign(Expr.var(variable), value);
            statements.add(statement);
        }
    }

    private void assignConstant(int variable, Expr value) {
        if (varDefinitionCount[variable] == 1) {
            relocatableVars[variable] = value;
        } else {
            AssignmentStatement statement = Statement.assign(Expr.var(variable), value);
            statements.add(statement);
        }
    }

    private Expr getVariable(int variable) {
        int usageCount = varUsageCount[variable];
        Expr relocatable = relocatableVars[variable];
        if (relocatable != null) {
            returnedVariableRelocatable = true;
            return relocatable;
        }

        int index = 0;
        if (usageCount == 1 && !exprStack.isEmpty()) {
            index = exprStack.size() - 1;
            ExprStackElement element = exprStack.get(index);
            if (exprStack.get(index).variable == variable) {
                exprStack.remove(index);
                returnedVariableRelocatable = false;
                return element.value;
            }
        }

        returnedVariableRelocatable = true;
        return Expr.var(variable);
    }

    private void flushStack() {
        int j = 0;
        for (int i = 0; i < exprStack.size(); ++i) {
            ExprStackElement element = exprStack.get(i);
            AssignmentStatement statement = Statement.assign(Expr.var(element.variable), element.value);
            statements.add(statement);
        }
        exprStack.subList(j, exprStack.size()).clear();
    }

    private Expr and(Expr a, Expr b) {
        if (a instanceof UnaryExpr && b instanceof UnaryExpr) {
            if (((UnaryExpr) a).getOperation() == UnaryOperation.NOT
                    && ((UnaryExpr) b).getOperation() == UnaryOperation.NOT) {
                return Expr.invert(Expr.or(((UnaryExpr) a).getOperand(), ((UnaryExpr) b).getOperand()));
            }
        }
        return Expr.and(a, b);
    }

    private Expr not(Expr expr) {
        if (expr instanceof UnaryExpr) {
            UnaryExpr unary = (UnaryExpr) expr;
            if (unary.getOperation() == UnaryOperation.NOT) {
                return unary.getOperand();
            }
        }
        return Expr.invert(expr);
    }

    private InstructionVisitor instructionDecompiler = new InstructionVisitor() {
        private List<Expr> arguments = new ArrayList<>();

        @Override
        public void visit(EmptyInstruction insn) {
        }

        @Override
        public void visit(ClassConstantInstruction insn) {
            assignConstant(insn.getReceiver().getIndex(), Expr.constant(insn.getConstant()));
        }

        @Override
        public void visit(NullConstantInstruction insn) {
            assignConstant(insn.getReceiver().getIndex(), Expr.constant(null));
        }

        @Override
        public void visit(IntegerConstantInstruction insn) {
            assignConstant(insn.getReceiver().getIndex(), Expr.constant(insn.getConstant()));
        }

        @Override
        public void visit(LongConstantInstruction insn) {
            assignConstant(insn.getReceiver().getIndex(), Expr.constant(insn.getConstant()));
        }

        @Override
        public void visit(FloatConstantInstruction insn) {
            assignConstant(insn.getReceiver().getIndex(), Expr.constant(insn.getConstant()));
        }

        @Override
        public void visit(DoubleConstantInstruction insn) {
            assignConstant(insn.getReceiver().getIndex(), Expr.constant(insn.getConstant()));
        }

        @Override
        public void visit(StringConstantInstruction insn) {
            assignConstant(insn.getReceiver().getIndex(), Expr.constant(insn.getConstant()));
        }

        @Override
        public void visit(BinaryInstruction insn) {
            switch (insn.getOperation()) {
                case ADD:
                    binary(BinaryOperation.ADD, insn.getOperandType(), insn, true);
                    break;
                case SUBTRACT:
                    binary(BinaryOperation.SUBTRACT, insn.getOperandType(), insn, true);
                    break;
                case MULTIPLY:
                    binary(BinaryOperation.MULTIPLY, insn.getOperandType(), insn, true);
                    break;
                case DIVIDE:
                    binary(BinaryOperation.DIVIDE, insn.getOperandType(), insn, !isIntegerType(insn.getOperandType()));
                    break;
                case MODULO:
                    binary(BinaryOperation.MODULO, insn.getOperandType(), insn, !isIntegerType(insn.getOperandType()));
                    break;
                case COMPARE:
                    binary(BinaryOperation.COMPARE, insn.getOperandType(), insn, true);
                    break;
                case AND:
                    binary(BinaryOperation.BITWISE_AND, insn.getOperandType(), insn, true);
                    break;
                case OR:
                    binary(BinaryOperation.BITWISE_OR, insn.getOperandType(), insn, true);
                    break;
                case XOR:
                    binary(BinaryOperation.BITWISE_XOR, insn.getOperandType(), insn, true);
                    break;
                case SHIFT_LEFT:
                    binary(BinaryOperation.LEFT_SHIFT, insn.getOperandType(), insn, true);
                    break;
                case SHIFT_RIGHT:
                    binary(BinaryOperation.RIGHT_SHIFT, insn.getOperandType(), insn, true);
                    break;
                case SHIFT_RIGHT_UNSIGNED:
                    binary(BinaryOperation.UNSIGNED_RIGHT_SHIFT, insn.getOperandType(), insn, true);
                    break;
            }
        }

        private void binary(BinaryOperation op, NumericOperandType opType, BinaryInstruction insn,
                boolean relocatable) {
            Expr second = getVariable(insn.getSecondOperand().getIndex());
            relocatable &= returnedVariableRelocatable;
            Expr first = getVariable(insn.getFirstOperand().getIndex());
            relocatable &= returnedVariableRelocatable;
            Expr result = Expr.binary(op, mapNumericType(opType), first, second);
            assignVariable(insn.getReceiver().getIndex(), result, relocatable);
        }

        private boolean isIntegerType(NumericOperandType operandType) {
            switch (operandType) {
                case INT:
                case LONG:
                    return true;
                default:
                    return false;
            }
        }

        private OperationType mapNumericType(NumericOperandType operandType) {
            if (operandType == null) {
                return null;
            }
            switch (operandType) {
                case INT:
                    return OperationType.INT;
                case LONG:
                    return OperationType.LONG;
                case FLOAT:
                    return OperationType.FLOAT;
                case DOUBLE:
                    return OperationType.DOUBLE;
                default:
                    throw new IllegalArgumentException();
            }
        }

        @Override
        public void visit(NegateInstruction insn) {
            Expr operand = getVariable(insn.getOperand().getIndex());
            boolean relocatable = returnedVariableRelocatable;
            Expr result = Expr.unary(UnaryOperation.NEGATE, mapNumericType(insn.getOperandType()), operand);
            assignVariable(insn.getReceiver().getIndex(), result, relocatable);
        }

        private void unary() {

        }

        @Override
        public void visit(AssignInstruction insn) {

        }

        @Override
        public void visit(CastInstruction insn) {

        }

        @Override
        public void visit(CastNumberInstruction insn) {

        }

        @Override
        public void visit(CastIntegerInstruction insn) {

        }

        @Override
        public void visit(BranchingInstruction insn) {
            Expr condition;
            switch (insn.getCondition()) {
                case NULL:
                    condition = cond(BinaryOperation.EQUALS, null, insn.getOperand(), Expr.constant(null));
                    break;
                case NOT_NULL:
                    condition = cond(BinaryOperation.NOT_EQUALS, null, insn.getOperand(), Expr.constant(null));
                    break;
                case EQUAL:
                    condition = cond(BinaryOperation.EQUALS, NumericOperandType.INT, insn.getOperand(),
                            Expr.constant(0));
                    break;
                case NOT_EQUAL:
                    condition = cond(BinaryOperation.NOT_EQUALS, NumericOperandType.INT, insn.getOperand(),
                            Expr.constant(0));
                    break;
                case LESS:
                    condition = cond(BinaryOperation.LESS, NumericOperandType.INT, insn.getOperand(), Expr.constant(0));
                    break;
                case LESS_OR_EQUAL:
                    condition = cond(BinaryOperation.LESS_OR_EQUALS, NumericOperandType.INT, insn.getOperand(),
                            Expr.constant(0));
                    break;
                case GREATER:
                    condition = cond(BinaryOperation.GREATER, NumericOperandType.INT, insn.getOperand(),
                            Expr.constant(0));
                    break;
                case GREATER_OR_EQUAL:
                    condition = cond(BinaryOperation.GREATER_OR_EQUALS, NumericOperandType.INT, insn.getOperand(),
                            Expr.constant(0));
                    break;
                default:
                    throw new IllegalArgumentException();
            }

            branch(condition, insn.getConsequent(), insn.getAlternative());
        }

        @Override
        public void visit(BinaryBranchingInstruction insn) {
            Expr condition;
            switch (insn.getCondition()) {
                case REFERENCE_EQUAL:
                    condition = cond(BinaryOperation.EQUALS, null, insn.getFirstOperand(), insn.getSecondOperand());
                    break;
                case REFERENCE_NOT_EQUAL:
                    condition = cond(BinaryOperation.NOT_EQUALS, null, insn.getFirstOperand(),
                            insn.getSecondOperand());
                    break;
                case EQUAL:
                    condition = cond(BinaryOperation.EQUALS, NumericOperandType.INT, insn.getFirstOperand(),
                            insn.getSecondOperand());
                    break;
                case NOT_EQUAL:
                    condition = cond(BinaryOperation.NOT_EQUALS, NumericOperandType.INT, insn.getFirstOperand(),
                            insn.getSecondOperand());
                    break;
                default:
                    throw new IllegalArgumentException();
            }

            branch(condition, insn.getConsequent(), insn.getAlternative());
        }

        private Expr cond(BinaryOperation op, NumericOperandType opType, Variable firstOp, Expr second) {
            Expr first = getVariable(firstOp.getIndex());
            if (opType == NumericOperandType.INT && isIntZero(second)) {
                if (first instanceof BinaryExpr) {
                    BinaryExpr firstBinary = (BinaryExpr) first;
                    if (firstBinary.getOperation() == BinaryOperation.SUBTRACT
                            || firstBinary.getOperation() == BinaryOperation.COMPARE) {
                        return Expr.binary(op, firstBinary.getType(), firstBinary.getFirstOperand(),
                                firstBinary.getSecondOperand());
                    }
                }
            }
            return Expr.binary(op, mapNumericType(opType), first, second);
        }

        private boolean isIntZero(Expr expr) {
            if (!(expr instanceof ConstantExpr)) {
                return false;
            }
            Object value = ((ConstantExpr) expr).getValue();
            return Integer.valueOf(0).equals(value);
        }

        private Expr cond(BinaryOperation op, NumericOperandType opType, Variable firstOp, Variable secondOp) {
            Expr second = getVariable(secondOp.getIndex());
            Expr first = getVariable(firstOp.getIndex());
            return Expr.binary(op, mapNumericType(opType), first, second);
        }

        private void branch(Expr condition, BasicBlock ifTrue, BasicBlock ifFalse) {
            if (loopExits[ifTrue.getIndex()] != null) {
                loopExitBranch(condition, ifTrue, ifTrue);
                return;
            } else if (loopExits[ifFalse.getIndex()] != null) {
                loopExitBranch(not(condition), ifFalse, ifTrue);
                return;
            }

            int sourceNode = blockExitNode(currentBlock);
            int[] immediatelyDominatedNodes = domGraph.outgoingEdges(sourceNode);
            boolean ownsTrueBranch = ownsBranch(currentBlock, ifTrue);
            boolean ownsFalseBranch = ownsBranch(currentBlock, ifFalse);

            int childBlockCount = immediatelyDominatedNodes.length;
            if (ownsTrueBranch) {
                childBlockCount--;
            }
            if (ownsFalseBranch) {
                childBlockCount--;
            }
            BasicBlock[] childBlocks = new BasicBlock[childBlockCount];
            int j = 0;
            for (int i = 0; i < immediatelyDominatedNodes.length; ++i) {
                BasicBlock childBlock = program.basicBlockAt(immediatelyDominatedNodes[i] / 2);
                if (ownsTrueBranch && childBlock == ifTrue
                        || ownsFalseBranch && childBlock == ifFalse) {
                    continue;
                }
                childBlocks[j++] = childBlock;
            }
            Arrays.sort(childBlocks, Comparator.comparing(b -> dfs[b.getIndex()]));

            BlockStatement[] blockStatements = new BlockStatement[childBlockCount];
            for (int i = 0; i < childBlocks.length; i++) {
                BasicBlock childBlock = childBlocks[i];
                BlockStatement blockStatement = new BlockStatement();
                jumpTargets[childBlock.getIndex()] = blockStatement;
                blockStatements[i] = blockStatement;
            }

            BasicBlock blockAfterIf = childBlocks.length > 0 ? childBlocks[0] : nextBlock;
            ConditionalStatement ifStatement = new ConditionalStatement();
            ifStatement.setCondition(condition);

            if (ownsTrueBranch) {
                processBlock(ifTrue, blockAfterIf, ifStatement.getConsequent());
            } else {
                Statement jump = getJumpStatement(ifTrue, blockAfterIf);
                if (jump != null) {
                    ifStatement.getConsequent().add(jump);
                }
            }

            if (ownsFalseBranch) {
                processBlock(ifFalse, blockAfterIf, ifStatement.getAlternative());
            } else {
                Statement jump = getJumpStatement(ifFalse, blockAfterIf);
                if (jump != null) {
                    ifStatement.getAlternative().add(jump);
                }
            }

            optimizeIf(ifStatement);

            if (blockStatements.length > 0) {
                blockStatements[0].getBody().add(ifStatement);
                for (int i = 0; i < childBlocks.length - 1; ++i) {
                    BlockStatement prevBlockStatement = blockStatements[i];
                    optimizeConditionalBlock(prevBlockStatement);
                    BlockStatement blockStatement = blockStatements[i + 1];
                    addChildBlock(prevBlockStatement, blockStatement.getBody());
                    BasicBlock childBlock = childBlocks[i];
                    processBlock(childBlock, childBlocks[i + 1], blockStatement.getBody());
                }
                BlockStatement lastBlockStatement = blockStatements[blockStatements.length - 1];
                optimizeConditionalBlock(lastBlockStatement);
                addChildBlock(lastBlockStatement, statements);
            } else {
                statements.add(ifStatement);
            }

            currentBlock = childBlocks.length > 0 ? childBlocks[childBlocks.length - 1] : null;
        }

        private void loopExitBranch(Expr expr, BasicBlock loopExit, BasicBlock next) {
            ConditionalStatement ifStatement = new ConditionalStatement();
            ifStatement.setCondition(expr);
            BreakStatement breakStatement = new BreakStatement();
            breakStatement.setTarget(loopExits[loopExit.getIndex()]);
            ifStatement.getConsequent().add(breakStatement);
            statements.add(ifStatement);
            currentBlock = next;
        }

        private void addChildBlock(BlockStatement blockStatement, List<Statement> containingList) {
            if (identifiedStatementUseCount.get(blockStatement) > 0) {
                containingList.add(blockStatement);
            } else {
                containingList.addAll(blockStatement.getBody());
            }
        }

        private boolean ownsBranch(BasicBlock condition, BasicBlock branch) {
            return dom.immediateDominatorOf(blockEnterNode(branch)) == blockExitNode(currentBlock)
                    && enteringBlockCount(branch) == 1;
        }

        private void optimizeConditionalBlock(BlockStatement statement) {
            while (optimizeFirstIfWithLastBreak(statement)) {
                // repeat
            }
        }

        private boolean optimizeFirstIfWithLastBreak(BlockStatement statement) {
            if (statement.getBody().isEmpty()) {
                return false;
            }
            Statement firstStatement = statement.getBody().get(0);
            if (!(firstStatement instanceof ConditionalStatement)) {
                return false;
            }
            ConditionalStatement nestedIf = (ConditionalStatement) firstStatement;
            if (nestedIf.getConsequent().isEmpty()) {
                return false;
            }
            Statement last = nestedIf.getConsequent().get(nestedIf.getConsequent().size() - 1);
            if (!(last instanceof BreakStatement)) {
                return false;
            }
            if (((BreakStatement) last).getTarget() != statement) {
                return false;
            }
            nestedIf.getConsequent().remove(nestedIf.getConsequent().size() - 1);
            List<Statement> statementsToMove = statement.getBody().subList(1, statement.getBody().size());
            nestedIf.getAlternative().addAll(statementsToMove);
            statementsToMove.clear();
            identifiedStatementUseCount.put(statement, identifiedStatementUseCount.get(statement) - 1);
            optimizeIf(nestedIf);
            return true;
        }

        private boolean optimizeIf(ConditionalStatement statement) {
            return invertIf(statement) | mergeNestedIfs(statement) | invertNotCondition(statement);
        }

        private boolean invertIf(ConditionalStatement statement) {
            if (statement.getAlternative().isEmpty() || !statement.getConsequent().isEmpty()) {
                return false;
            }
            statement.setCondition(not(statement.getCondition()));
            statement.getConsequent().addAll(statement.getAlternative());
            statement.getAlternative().clear();
            return true;
        }

        private boolean mergeNestedIfs(ConditionalStatement statement) {
            if (!statement.getAlternative().isEmpty() || statement.getConsequent().size() != 1) {
                return false;
            }
            Statement firstNested = statement.getConsequent().get(0);
            if (!(firstNested instanceof ConditionalStatement)) {
                return false;
            }
            ConditionalStatement nestedIf = (ConditionalStatement) firstNested;
            if (!nestedIf.getAlternative().isEmpty()) {
                return false;
            }
            statement.getConsequent().clear();
            statement.getConsequent().addAll(nestedIf.getConsequent());
            statement.setCondition(and(statement.getCondition(), nestedIf.getCondition()));
            invertNotCondition(statement);
            return true;
        }

        private boolean invertNotCondition(ConditionalStatement statement) {
            if (!statement.getConsequent().isEmpty() && !statement.getAlternative().isEmpty()
                    && statement.getCondition() instanceof UnaryExpr
                    && ((UnaryExpr) statement.getCondition()).getOperation() == UnaryOperation.NOT) {
                statement.setCondition(((UnaryExpr) statement.getCondition()).getOperand());
                List<Statement> tmp = new ArrayList<>(statement.getAlternative());
                statement.getAlternative().clear();
                statement.getAlternative().addAll(statement.getConsequent());
                statement.getConsequent().clear();
                statement.getConsequent().addAll(tmp);
                return true;
            }
            return false;
        }

        @Override
        public void visit(JumpInstruction insn) {
            int sourceNode = blockExitNode(currentBlock);
            int targetNode = blockEnterNode(insn.getTarget());
            if (dom.immediateDominatorOf(targetNode) == sourceNode) {
                currentBlock = insn.getTarget();
            } else {
                flushStack();
                exitCurrentDominator(insn.getTarget());
            }
        }

        private void exitCurrentDominator(BasicBlock target) {
            Statement jump = getJumpStatement(target, nextBlock);
            if (jump != null) {
                statements.add(jump);
            }
            currentBlock = null;
        }

        private Statement getJumpStatement(BasicBlock target, BasicBlock nextBlock) {
            if (target == nextBlock) {
                return null;
            }
            IdentifiedStatement targetStatement = getJumpTarget(target);
            BreakStatement breakStatement = new BreakStatement();
            breakStatement.setTarget(targetStatement);
            return breakStatement;
        }

        private IdentifiedStatement getJumpTarget(BasicBlock target) {
            IdentifiedStatement targetStatement = jumpTargets[target.getIndex()];
            int count = identifiedStatementUseCount.get(targetStatement);
            identifiedStatementUseCount.put(targetStatement, count + 1);
            return targetStatement;
        }

        @Override
        public void visit(SwitchInstruction insn) {

        }

        @Override
        public void visit(ExitInstruction insn) {
            Expr returnValue;
            if (insn.getValueToReturn() != null) {
                returnValue = getVariable(insn.getValueToReturn().getIndex());
            } else {
                returnValue = null;
            }
            flushStack();
            if (nextBlock != null || returnValue != null) {
                ReturnStatement statement = new ReturnStatement();
                statement.setResult(returnValue);
                statements.add(statement);
            }
            currentBlock = null;
        }

        @Override
        public void visit(RaiseInstruction insn) {

        }

        @Override
        public void visit(ConstructArrayInstruction insn) {

        }

        @Override
        public void visit(ConstructInstruction insn) {

        }

        @Override
        public void visit(ConstructMultiArrayInstruction insn) {

        }

        @Override
        public void visit(GetFieldInstruction insn) {

        }

        @Override
        public void visit(PutFieldInstruction insn) {

        }

        @Override
        public void visit(ArrayLengthInstruction insn) {

        }

        @Override
        public void visit(CloneArrayInstruction insn) {

        }

        @Override
        public void visit(UnwrapArrayInstruction insn) {

        }

        @Override
        public void visit(GetElementInstruction insn) {

        }

        @Override
        public void visit(PutElementInstruction insn) {

        }

        @Override
        public void visit(InvokeInstruction insn) {
            for (int i = insn.getArguments().size() - 1; i >= 0; --i) {
                arguments.add(getVariable(insn.getArguments().get(i).getIndex()));
            }
            if (insn.getInstance() != null) {
                arguments.add(getVariable(insn.getInstance().getIndex()));
            }
            Collections.reverse(arguments);

            InvocationExpr expr = new InvocationExpr();
            expr.setMethod(insn.getMethod());
            if (insn.getInstance() == null) {
                expr.setType(InvocationType.STATIC);
            } else {
                switch (insn.getType()) {
                    case SPECIAL:
                        expr.setType(InvocationType.SPECIAL);
                        break;
                    case VIRTUAL:
                        expr.setType(InvocationType.DYNAMIC);
                        break;
                }
            }
            expr.getArguments().addAll(arguments);
            arguments.clear();
            if (insn.getReceiver() != null) {
                assignVariable(insn.getReceiver().getIndex(), expr, false);
            } else {
                flushStack();
                AssignmentStatement statement = new AssignmentStatement();
                statement.setRightValue(expr);
                statements.add(statement);
            }
        }

        @Override
        public void visit(InvokeDynamicInstruction insn) {
        }

        @Override
        public void visit(IsInstanceInstruction insn) {

        }

        @Override
        public void visit(InitClassInstruction insn) {

        }

        @Override
        public void visit(NullCheckInstruction insn) {

        }

        @Override
        public void visit(MonitorEnterInstruction insn) {

        }

        @Override
        public void visit(MonitorExitInstruction insn) {

        }

        @Override
        public void visit(BoundCheckInstruction insn) {

        }
    };

    static class ExprStackElement {
        int variable;
        Expr value;

        ExprStackElement(int variable, Expr value) {
            this.variable = variable;
            this.value = value;
        }
    }
}
