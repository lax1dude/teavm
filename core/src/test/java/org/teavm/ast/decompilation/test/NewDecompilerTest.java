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
package org.teavm.ast.decompilation.test;

import static org.junit.Assert.assertEquals;
import static org.teavm.ast.Expr.*;
import static org.teavm.ast.Statement.*;
import static org.teavm.model.builder.ProgramBuilder.*;
import java.util.Arrays;
import org.junit.Test;
import org.teavm.ast.Statement;
import org.teavm.ast.decompilation.NewDecompiler;
import org.teavm.ast.util.AstPrinter;
import org.teavm.model.MethodReference;
import org.teavm.model.Program;
import org.teavm.model.text.ListingBuilder;

public class NewDecompilerTest {
    private static final MethodReference PRINT = new MethodReference(NewDecompilerTest.class, "print", void.class);
    private static final MethodReference PRINT_2 = new MethodReference(NewDecompilerTest.class, "print2", void.class);
    private static final MethodReference PRINT_3 = new MethodReference(NewDecompilerTest.class, "print3", void.class);
    private static final MethodReference SUPPLY_INT_1 = new MethodReference(NewDecompilerTest.class,
            "supplyInt1", int.class);
    private static final MethodReference SUPPLY_INT_2 = new MethodReference(NewDecompilerTest.class,
            "supplyInt2", int.class);
    private AstPrinter astPrinter = new AstPrinter();
    private ListingBuilder listingBuilder = new ListingBuilder();
    private NewDecompiler decompiler = new NewDecompiler();
    private Program program;
    private Statement statement;

    @Test
    public void simple() {
        decompile(() -> {
            set(var("a")).constant(23);
            exit(var("a"));
        });
        expect(exitFunction(constant(23)));
    }

    @Test
    public void expression() {
        decompile(() -> {
            set(var("a")).constant(2);
            set(var("b")).constant(3);
            set(var("c")).add(intNum(), var("a"), var("b"));
            exit(var("c"));
        });
        expect(exitFunction(addInt(constant(2), constant(3))));
    }

    @Test
    public void complexExpression() {
        decompile(() -> {
            set(var("a")).constant(2);
            set(var("b")).constant(3);
            set(var("c")).constant(4);
            set(var("d")).add(intNum(), var("a"), var("b"));
            set(var("e")).add(intNum(), var("d"), var("c"));
            exit(var("e"));
        });
        expect(exitFunction(
                addInt(
                    addInt(constant(2), constant(3)),
                    constant(4)
                )
        ));
    }

    @Test
    public void sharedNonConstant() {
        decompile(() -> {
            set(var("a")).constant(2);
            set(var("b")).constant(3);
            set(var("c")).add(intNum(), var("a"), var("b"));
            set(var("d")).add(intNum(), var("c"), var("c"));
            exit(var("d"));
        });
        expect(sequence(
                assign(var(2), addInt(constant(2), constant(3))),
                exitFunction(addInt(var(2), var(2)))
        ));
    }

    @Test
    public void sharedConstant() {
        decompile(() -> {
            set(var("a")).constant(2);
            set(var("b")).add(intNum(), var("a"), var("a"));
            exit(var("b"));
        });
        expect(exitFunction(addInt(constant(2), constant(2))));
    }

    @Test
    public void relocatableOperationWithBarrier() {
        decompile(() -> {
            set(var("a")).constant(2);
            set(var("b")).constant(3);
            set(var("c")).add(intNum(), var("a"), var("b"));
            invokeStaticMethod(PRINT);
            exit(var("c"));
        });
        expect(sequence(
                statementExpr(invokeStatic(PRINT)),
                exitFunction(addInt(constant(2), constant(3)))
        ));
    }

    @Test
    public void nonRelocatableOperationWithBarrier() {
        decompile(() -> {
            set(var("a")).constant(2);
            set(var("b")).constant(3);
            set(var("c")).div(intNum(), var("a"), var("b"));
            invokeStaticMethod(PRINT);
            exit(var("c"));
        });
        expect(sequence(
                assign(var(2), divInt(constant(2), constant(3))),
                statementExpr(invokeStatic(PRINT)),
                exitFunction(var(2))
        ));
    }

    @Test
    public void properOrderOfArguments() {
        decompile(() -> {
            set(var("a")).invokeStatic(SUPPLY_INT_1);
            set(var("b")).invokeStatic(SUPPLY_INT_2);
            set(var("c")).add(intNum(), var("a"), var("b"));
            exit(var("c"));
        });
        expect(exitFunction(addInt(invokeStatic(SUPPLY_INT_1), invokeStatic(SUPPLY_INT_2))));
    }

    @Test
    public void wrongOrderOfArguments() {
        decompile(() -> {
            set(var("a")).invokeStatic(SUPPLY_INT_1);
            set(var("b")).invokeStatic(SUPPLY_INT_2);
            set(var("c")).add(intNum(), var("b"), var("a"));
            exit(var("c"));
        });
        expect(sequence(
                assign(var(0), invokeStatic(SUPPLY_INT_1)),
                exitFunction(addInt(invokeStatic(SUPPLY_INT_2), var(0)))
        ));
    }

    @Test
    public void simpleCondition() {
        decompile(() -> {
            set(var("a")).constant(2);
            ifLessThanZero(var("a"), label("less"), label("greater"));

            put(label("less"));
            invokeStaticMethod(PRINT);
            jump(label("join"));

            put(label("greater"));
            invokeStaticMethod(PRINT_2);
            jump(label("join"));

            put(label("join"));
            exit();
        });

        expect(cond(
                less(constant(2), constant(0)),
                Arrays.asList(
                        statementExpr(invokeStatic(PRINT))
                ),
                Arrays.asList(
                        statementExpr(invokeStatic(PRINT_2))
                )
        ));
    }

    @Test
    public void simpleConditionWithOneBranch() {
        decompile(() -> {
            set(var("a")).constant(2);
            ifLessThanZero(var("a"), label("less"), label("join"));

            put(label("less"));
            invokeStaticMethod(PRINT);
            jump(label("join"));

            put(label("join"));
            exit();
        });

        expect(cond(
                less(constant(2), constant(0)),
                Arrays.asList(
                        statementExpr(invokeStatic(PRINT))
                )
        ));
    }

    @Test
    public void simpleConditionWithEachBranchReturning() {
        decompile(() -> {
            set(var("a")).constant(2);
            ifLessThanZero(var("a"), label("less"), label("greater"));

            put(label("less"));
            invokeStaticMethod(PRINT);
            exit();

            put(label("greater"));
            invokeStaticMethod(PRINT_2);
            exit();
        });

        expect(cond(
                less(constant(2), constant(0)),
                Arrays.asList(
                        statementExpr(invokeStatic(PRINT))
                ),
                Arrays.asList(
                        statementExpr(invokeStatic(PRINT_2))
                )
        ));
    }

    @Test
    public void shortCircuit() {
        decompile(() -> {
            set(var("a")).constant(2);
            ifLessThanZero(var("a"), label("next"), label("false"));

            put(label("next"));
            set(var("b")).constant(3);
            ifLessThanZero(var("b"), label("true"), label("false"));

            put(label("true"));
            invokeStaticMethod(PRINT);
            jump(label("joint"));

            put(label("false"));
            invokeStaticMethod(PRINT_2);
            jump(label("joint"));

            put(label("joint"));
            invokeStaticMethod(PRINT_3);
            exit();
        });

        expect(cond(
                less(constant(2), constant(0)),
                Arrays.asList(
                        statementExpr(invokeStatic(PRINT))
                ),
                Arrays.asList(
                        statementExpr(invokeStatic(PRINT_2))
                )
        ));
    }

    private void decompile(Runnable r) {
        program = build(r);
        statement = decompiler.decompile(program);
    }

    private void expect(Statement statement) {
        assertEquals(
                "Wrong result for program:\n" + listingBuilder.buildListing(program, "  "),
                astPrinter.print(statement),
                astPrinter.print(this.statement)
        );
    }
}
