/*
 *  Copyright 2024 Alexey Andreev.
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
package org.teavm.backend.wasm.gc;

import java.util.Collection;
import java.util.function.Supplier;
import org.teavm.backend.wasm.generate.gc.classes.WasmGCCustomTypeMapperFactory;
import org.teavm.backend.wasm.generators.gc.WasmGCCustomGenerator;
import org.teavm.backend.wasm.generators.gc.WasmGCCustomGeneratorFactory;
import org.teavm.backend.wasm.intrinsics.gc.WasmGCIntrinsic;
import org.teavm.backend.wasm.intrinsics.gc.WasmGCIntrinsicFactory;
import org.teavm.model.MethodReference;
import org.teavm.vm.spi.TeaVMHostExtension;

public interface TeaVMWasmGCHost extends TeaVMHostExtension {
    void addIntrinsicFactory(WasmGCIntrinsicFactory intrinsicFactory);

    void addIntrinsic(MethodReference method, WasmGCIntrinsic intrinsic);

    void addGeneratorFactory(WasmGCCustomGeneratorFactory factory);

    void addGenerator(MethodReference method, WasmGCCustomGenerator generator);

    void addCustomTypeMapperFactory(WasmGCCustomTypeMapperFactory customTypeMapperFactory);

    void addClassConsumer(WasmGCClassConsumer consumer);

    void addMethodsOnCallSites(Supplier<Collection<MethodReference>> methodsOnCallSites);
}
