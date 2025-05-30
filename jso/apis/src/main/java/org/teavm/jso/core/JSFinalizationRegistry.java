/*
 *  Copyright 2023 Alexey Andreev.
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
package org.teavm.jso.core;

import org.teavm.interop.NoSideEffects;
import org.teavm.jso.JSBody;
import org.teavm.jso.JSClass;
import org.teavm.jso.JSObject;

@JSClass(name = "FinalizationRegistry")
public class JSFinalizationRegistry implements JSObject {
    public JSFinalizationRegistry(JSFinalizationRegistryConsumer consumer) {
    }

    public native void register(Object obj, Object token);

    public native void register(Object obj, Object token, Object unregisterToken);

    public native boolean unregister(Object obj);

    @JSBody(params = "consumer", script = "return new FinalizationRegistry(consumer);")
    @Deprecated
    public static native JSFinalizationRegistry create(JSFinalizationRegistryConsumer consumer);

    @JSBody(script = "return typeof FinalizationRegistry !== 'undefined';")
    @NoSideEffects
    public static native boolean isSupported();
}
