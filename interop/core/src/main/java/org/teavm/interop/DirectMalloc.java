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
package org.teavm.interop;

/**
 * Linear memory allocator for creating "direct buffers" in WASM GC<br><br>
 * 
 * DO NOT USE IN LEGACY WASM BACKEND!!! Make a regular byte array, and use Address.ofData()<br><br>
 * 
 * Similar to dlmalloc and emmalloc (emscripten's malloc)<br><br>
 * 
 * bad things will happen if you free an address that was never allocated
 * 
 * @author lax1dude
 */
public final class DirectMalloc {

    private DirectMalloc() {
    }

    @UnsupportedOn({Platforms.JAVASCRIPT, Platforms.WEBASSEMBLY, Platforms.C})
    public static native Address malloc(int sizeBytes);

    @UnsupportedOn({Platforms.JAVASCRIPT, Platforms.WEBASSEMBLY, Platforms.C})
    public static native Address calloc(int sizeBytes);

    @UnsupportedOn({Platforms.JAVASCRIPT, Platforms.WEBASSEMBLY, Platforms.C})
    public static native void free(Address ptr);

    @UnsupportedOn({Platforms.JAVASCRIPT, Platforms.WEBASSEMBLY, Platforms.C})
    public static native void memcpy(Address dst, Address src, int count);

    @UnsupportedOn({Platforms.JAVASCRIPT, Platforms.WEBASSEMBLY, Platforms.C})
    public static native void memset(Address ptr, int val, int count);

    @UnsupportedOn({Platforms.JAVASCRIPT, Platforms.WEBASSEMBLY, Platforms.C})
    public static native void zmemset(Address ptr, int count);

}
