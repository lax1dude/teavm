/*
 *  Copyright 2014 Alexey Andreev.
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
package org.teavm.classlib.java.nio;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.sameInstance;
import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.fail;
import java.nio.BufferOverflowException;
import java.nio.BufferUnderflowException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.FloatBuffer;
import java.nio.InvalidMarkException;
import java.nio.ReadOnlyBufferException;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.teavm.junit.SkipPlatform;
import org.teavm.junit.TeaVMTestRunner;
import org.teavm.junit.TestPlatform;

@RunWith(TeaVMTestRunner.class)
public class FloatBufferTest {
    @Test
    public void allocatesSimple() {
        FloatBuffer buffer = FloatBuffer.allocate(100);
        assertThat(buffer.isDirect(), is(false));
        assertThat(buffer.isReadOnly(), is(false));
        assertThat(buffer.hasArray(), is(true));
        assertThat(buffer.capacity(), is(100));
        assertThat(buffer.position(), is(0));
        assertThat(buffer.limit(), is(100));
        try {
            buffer.reset();
            fail("Mark is expected to be undefined");
        } catch (InvalidMarkException e) {
            // ok
        }
    }

    @Test
    @SkipPlatform({ TestPlatform.WASI, TestPlatform.WEBASSEMBLY })
    public void bulkTransferDirect() {
        var buffer = ByteBuffer.allocateDirect(40).asFloatBuffer();
        var floats = new float[] { 1, 2, 3 };
        buffer.put(0, floats);
        var floatsCopy = new float[floats.length];
        buffer.get(0, floatsCopy);
        assertArrayEquals(floats, floatsCopy, 0.1f);
    }

    @Test(expected = IllegalArgumentException.class)
    public void errorIfAllocatingBufferOfNegativeSize() {
        FloatBuffer.allocate(-1);
    }

    @Test
    public void wrapsArray() {
        float[] array = new float[100];
        FloatBuffer buffer = FloatBuffer.wrap(array, 10, 70);
        assertThat(buffer.isDirect(), is(false));
        assertThat(buffer.isReadOnly(), is(false));
        assertThat(buffer.hasArray(), is(true));
        assertThat(buffer.array(), is(array));
        assertThat(buffer.arrayOffset(), is(0));
        assertThat(buffer.capacity(), is(100));
        assertThat(buffer.position(), is(10));
        assertThat(buffer.limit(), is(80));
        try {
            buffer.reset();
            fail("Mark is expected to be undefined");
        } catch (InvalidMarkException e) {
            // ok
        }
        array[0] = 23;
        assertThat(buffer.get(0), is((float) 23));
        buffer.put(1, 24);
        assertThat(array[1], is((float) 24));
    }

    @Test
    public void errorWhenWrappingWithWrongParameters() {
        float[] array = new float[100];
        try {
            FloatBuffer.wrap(array, -1, 10);
        } catch (IndexOutOfBoundsException e) {
            // ok
        }
        try {
            FloatBuffer.wrap(array, 101, 10);
        } catch (IndexOutOfBoundsException e) {
            // ok
        }
        try {
            FloatBuffer.wrap(array, 98, 3);
        } catch (IndexOutOfBoundsException e) {
            // ok
        }
        try {
            FloatBuffer.wrap(array, 98, -1);
        } catch (IndexOutOfBoundsException e) {
            // ok
        }
    }

    @Test
    public void wrapsArrayWithoutOffset() {
        float[] array = new float[100];
        FloatBuffer buffer = FloatBuffer.wrap(array);
        assertThat(buffer.position(), is(0));
        assertThat(buffer.limit(), is(100));
    }

    @Test
    public void createsSlice() {
        FloatBuffer buffer = FloatBuffer.allocate(100);
        buffer.put(new float[60]);
        buffer.flip();
        buffer.put(new float[15]);
        FloatBuffer slice = buffer.slice();
        assertThat(slice.array(), is(buffer.array()));
        assertThat(slice.position(), is(0));
        assertThat(slice.capacity(), is(45));
        assertThat(slice.limit(), is(45));
        assertThat(slice.isDirect(), is(false));
        assertThat(slice.isReadOnly(), is(false));
        slice.put(3, 23);
        assertThat(buffer.get(18), is((float) 23));
        slice.put(24);
        assertThat(buffer.get(15), is((float) 24));
        buffer.put(16, 25);
        assertThat(slice.get(1), is((float) 25));
    }

    @Test
    public void slicePropertiesSameWithOriginal() {
        FloatBuffer buffer = FloatBuffer.allocate(100).asReadOnlyBuffer().slice();
        assertThat(buffer.isReadOnly(), is(true));
    }

    @Test
    public void createsDuplicate() {
        FloatBuffer buffer = FloatBuffer.allocate(100);
        buffer.put(new float[60]);
        buffer.flip();
        buffer.put(new float[15]);
        FloatBuffer duplicate = buffer.duplicate();
        assertThat(duplicate.array(), is(buffer.array()));
        assertThat(duplicate.position(), is(15));
        assertThat(duplicate.capacity(), is(100));
        assertThat(duplicate.limit(), is(60));
        assertThat(duplicate.isDirect(), is(false));
        assertThat(duplicate.isReadOnly(), is(false));
        duplicate.put(3, 23);
        assertThat(buffer.get(3), is((float) 23));
        duplicate.put(24);
        assertThat(buffer.get(15), is((float) 24));
        buffer.put(1, 25);
        assertThat(duplicate.get(1), is((float) 25));
        assertThat(duplicate.array(), is(sameInstance(buffer.array())));
    }

    @Test
    public void getsFloat() {
        float[] array = { 2, 3, 5, 7 };
        FloatBuffer buffer = FloatBuffer.wrap(array);
        assertThat(buffer.get(), is((float) 2));
        assertThat(buffer.get(), is((float) 3));
        buffer = buffer.slice();
        assertThat(buffer.get(), is((float) 5));
        assertThat(buffer.get(), is((float) 7));
    }

    @Test
    public void gettingFloatFromEmptyBufferCausesError() {
        float[] array = { 2, 3, 5, 7 };
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.limit(2);
        buffer.get();
        buffer.get();
        try {
            buffer.get();
            fail("Should have thrown error");
        } catch (BufferUnderflowException e) {
            // ok
        }
    }

    @Test
    public void putsFloat() {
        float[] array = new float[4];
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.put(2).put(3).put(5).put(7);
        assertThat(array, is(new float[] { 2, 3, 5, 7 }));
    }

    @Test
    public void puttingFloatToEmptyBufferCausesError() {
        float[] array = new float[4];
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.limit(2);
        buffer.put(2).put(3);
        try {
            buffer.put(5);
            fail("Should have thrown error");
        } catch (BufferOverflowException e) {
            assertThat(array[2], is((float) 0));
        }
    }

    @Test(expected = ReadOnlyBufferException.class)
    public void puttingFloatToReadOnlyBufferCausesError() {
        float[] array = new float[4];
        FloatBuffer buffer = FloatBuffer.wrap(array).asReadOnlyBuffer();
        buffer.put(2);
    }

    @Test
    public void getsFloatFromGivenLocation() {
        float[] array = { 2, 3, 5, 7 };
        FloatBuffer buffer = FloatBuffer.wrap(array);
        assertThat(buffer.get(0), is((float) 2));
        assertThat(buffer.get(1), is((float) 3));
        buffer.get();
        buffer = buffer.slice();
        assertThat(buffer.get(1), is((float) 5));
        assertThat(buffer.get(2), is((float) 7));
    }

    @Test
    public void gettingFloatFromWrongLocationCausesError() {
        float[] array = { 2, 3, 5, 7 };
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.limit(3);
        try {
            buffer.get(-1);
        } catch (IndexOutOfBoundsException e) {
            // ok
        }
        try {
            buffer.get(3);
        } catch (IndexOutOfBoundsException e) {
            // ok
        }
    }

    @Test
    public void putsFloatToGivenLocation() {
        float[] array = new float[4];
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.put(0, 2);
        buffer.put(1, 3);
        buffer.get();
        buffer = buffer.slice();
        buffer.put(1, 5);
        buffer.put(2, 7);
        assertThat(array, is(new float[] { 2, 3, 5, 7 }));
    }

    @Test
    public void puttingFloatToWrongLocationCausesError() {
        float[] array = new float[4];
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.limit(3);
        try {
            buffer.put(-1, 2);
        } catch (IndexOutOfBoundsException e) {
            // ok
        }
        try {
            buffer.put(3, 2);
        } catch (IndexOutOfBoundsException e) {
            // ok
        }
    }

    @Test(expected = ReadOnlyBufferException.class)
    public void puttingFloatToGivenLocationOfReadOnlyBufferCausesError() {
        float[] array = new float[4];
        FloatBuffer buffer = FloatBuffer.wrap(array).asReadOnlyBuffer();
        buffer.put(0, 2);
    }

    @Test
    public void getsFloats() {
        float[] array = { 2, 3, 5, 7 };
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.get();
        float[] receiver = new float[2];
        buffer.get(receiver, 0, 2);
        assertThat(buffer.position(), is(3));
        assertThat(receiver, is(new float[] { 3, 5 }));
    }

    @Test
    public void gettingFloatsFromEmptyBufferCausesError() {
        float[] array = { 2, 3, 5, 7 };
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.limit(3);
        float[] receiver = new float[4];
        try {
            buffer.get(receiver, 0, 4);
            fail("Error expected");
        } catch (BufferUnderflowException e) {
            assertThat(receiver, is(new float[4]));
            assertThat(buffer.position(), is(0));
        }
    }

    @Test
    public void gettingFloatsWithIllegalArgumentsCausesError() {
        float[] array = { 2, 3, 5, 7 };
        FloatBuffer buffer = FloatBuffer.wrap(array);
        float[] receiver = new float[4];
        try {
            buffer.get(receiver, 0, 5);
        } catch (IndexOutOfBoundsException e) {
            assertThat(receiver, is(new float[4]));
            assertThat(buffer.position(), is(0));
        }
        try {
            buffer.get(receiver, -1, 3);
        } catch (IndexOutOfBoundsException e) {
            assertThat(receiver, is(new float[4]));
            assertThat(buffer.position(), is(0));
        }
        try {
            buffer.get(receiver, 6, 3);
        } catch (IndexOutOfBoundsException e) {
            assertThat(receiver, is(new float[4]));
            assertThat(buffer.position(), is(0));
        }
    }

    @Test
    public void putsFloats() {
        float[] array = new float[4];
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.get();
        float[] data = { 2, 3 };
        buffer.put(data, 0, 2);
        assertThat(buffer.position(), is(3));
        assertThat(array, is(new float[] { 0, 2, 3, 0 }));
    }

    @Test
    public void compacts() {
        float[] array = { 2, 3, 5, 7 };
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.get();
        buffer.mark();
        buffer.compact();
        assertThat(array, is(new float[] { 3, 5, 7, 7 }));
        assertThat(buffer.position(), is(3));
        assertThat(buffer.limit(), is(4));
        assertThat(buffer.capacity(), is(4));
        try {
            buffer.reset();
            fail("Exception expected");
        } catch (InvalidMarkException e) {
            // ok
        }
    }

    @Test
    public void marksPosition() {
        float[] array = { 2, 3, 5, 7 };
        FloatBuffer buffer = FloatBuffer.wrap(array);
        buffer.position(1);
        buffer.mark();
        buffer.position(2);
        buffer.reset();
        assertThat(buffer.position(), is(1));
    }

    @Test
    public void putEmptyArray() {
        FloatBuffer fb = FloatBuffer.allocate(0);
        fb.put(new float[0]);
        fb.get(new float[0]);
    }

    @Test
    public void bulkPut() {
        var buffer = FloatBuffer.allocate(100);
        buffer.put(new float[] { 1, 2, 3 });
        assertEquals(3, buffer.position());
        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(2, buffer.get(1), 0.1f);
        assertEquals(3, buffer.get(2), 0.1f);

        buffer.put(1, new float[] { 4, 5, 6 });
        assertEquals(3, buffer.position());
        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(4, buffer.get(1), 0.1f);
        assertEquals(5, buffer.get(2), 0.1f);
        assertEquals(6, buffer.get(3), 0.1f);

        buffer.put(0, new float[] { 7, 8, 9, 10 }, 1, 2);
        assertEquals(8, buffer.get(0), 0.1f);
        assertEquals(9, buffer.get(1), 0.1f);
        assertEquals(5, buffer.get(2), 0.1f);
        assertEquals(6, buffer.get(3), 0.1f);
    }

    @Test
    public void bulkPutWrapper() {
        var byteBuffer = ByteBuffer.allocate(100);
        byteBuffer.order(ByteOrder.BIG_ENDIAN);
        var buffer = byteBuffer.asFloatBuffer();

        buffer.put(new float[] { 1, 2, 3 });
        assertEquals(3, buffer.position());
        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(2, buffer.get(1), 0.1f);
        assertEquals(3, buffer.get(2), 0.1f);

        buffer.put(1, new float[] { 4, 5, 6 });
        assertEquals(3, buffer.position());
        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(4, buffer.get(1), 0.1f);
        assertEquals(5, buffer.get(2), 0.1f);
        assertEquals(6, buffer.get(3), 0.1f);
        assertEquals((byte) 0x3f, byteBuffer.get(0));
        assertEquals((byte) 0x80, byteBuffer.get(1));
        assertEquals(0, byteBuffer.get(2));
        assertEquals(0, byteBuffer.get(3));

        buffer.put(0, new float[] { 7, 8, 9, 10 }, 1, 2);
        assertEquals(8, buffer.get(0), 0.1f);
        assertEquals(9, buffer.get(1), 0.1f);
        assertEquals(5, buffer.get(2), 0.1f);
        assertEquals(6, buffer.get(3), 0.1f);

        byteBuffer.order(ByteOrder.LITTLE_ENDIAN);
        buffer = byteBuffer.asFloatBuffer();

        buffer.put(new float[] { 1, 2, 3 });
        assertEquals(3, buffer.position());
        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(2, buffer.get(1), 0.1f);
        assertEquals(3, buffer.get(2), 0.1f);

        buffer.put(1, new float[] { 4, 5, 6 });
        assertEquals(3, buffer.position());
        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(4, buffer.get(1), 0.1f);
        assertEquals(5, buffer.get(2), 0.1f);
        assertEquals(6, buffer.get(3), 0.1f);
        assertEquals(0, byteBuffer.get(0));
        assertEquals(0, byteBuffer.get(1));
        assertEquals((byte) 0x80, byteBuffer.get(2));
        assertEquals((byte) 0x3f, byteBuffer.get(3));

        buffer.put(0, new float[] { 7, 8, 9, 10 }, 1, 2);
        assertEquals(8, buffer.get(0), 0.1f);
        assertEquals(9, buffer.get(1), 0.1f);
        assertEquals(5, buffer.get(2), 0.1f);
        assertEquals(6, buffer.get(3), 0.1f);
    }

    @Test
    public void bulkPutBuffer() {
        var buffer = FloatBuffer.allocate(100);
        buffer.put(FloatBuffer.wrap(new float[] { 1, 2, 3 }));

        assertEquals(3, buffer.position());
        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(2, buffer.get(1), 0.1f);
        assertEquals(3, buffer.get(2), 0.1f);

        buffer.put(1, FloatBuffer.wrap(new float[] { 4, 5, 6 }), 1, 2);
        assertEquals(3, buffer.position());
        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(5, buffer.get(1), 0.1f);
        assertEquals(6, buffer.get(2), 0.1f);
    }

    @Test
    public void bulkPutBufferWrapper() {
        var buffer = ByteBuffer.allocate(100).order(ByteOrder.BIG_ENDIAN).asFloatBuffer();
        buffer.put(ByteBuffer.wrap(new byte[] {
                        0x3f, (byte) 0x80, 0x00, 0x00,
                        0x40, 0x00, 0x00, 0x00,
                        0x40, 0x40, 0x00, 0x00
                })
                .order(ByteOrder.BIG_ENDIAN)
                .asFloatBuffer());

        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(2, buffer.get(1), 0.1f);
        assertEquals(3, buffer.get(2), 0.1f);

        buffer = ByteBuffer.allocate(100).order(ByteOrder.LITTLE_ENDIAN).asFloatBuffer();
        buffer.put(ByteBuffer.wrap(new byte[] {
                        0x3f, (byte) 0x80, 0x00, 0x00,
                        0x40, 0x00, 0x00, 0x00,
                        0x40, 0x40, 0x00, 0x00
                })
                .order(ByteOrder.BIG_ENDIAN)
                .asFloatBuffer());

        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(2, buffer.get(1), 0.1f);
        assertEquals(3, buffer.get(2), 0.1f);

        buffer = ByteBuffer.allocate(100).order(ByteOrder.BIG_ENDIAN).asFloatBuffer();
        buffer.put(ByteBuffer.wrap(new byte[] {
                        0x00, 0x00, (byte) 0x80, 0x3f,
                        0x00, 0x00, 0x00, 0x40,
                        0x00, 0x00, 0x40, 0x40
                })
                .order(ByteOrder.LITTLE_ENDIAN)
                .asFloatBuffer());

        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(2, buffer.get(1), 0.1f);
        assertEquals(3, buffer.get(2), 0.1f);

        buffer = ByteBuffer.allocate(100).order(ByteOrder.LITTLE_ENDIAN).asFloatBuffer();
        buffer.put(ByteBuffer.wrap(new byte[] {
                        0x00, 0x00, (byte) 0x80, 0x3f,
                        0x00, 0x00, 0x00, 0x40,
                        0x00, 0x00, 0x40, 0x40
                })
                .order(ByteOrder.LITTLE_ENDIAN)
                .asFloatBuffer());

        assertEquals(1, buffer.get(0), 0.1f);
        assertEquals(2, buffer.get(1), 0.1f);
        assertEquals(3, buffer.get(2), 0.1f);
    }

    @Test
    public void bulkGet() {
        var buffer = FloatBuffer.wrap(new float[] { 1, 2, 3, 4, 5, 6 });
        var arr = new float[3];

        buffer.get(arr);
        assertArrayEquals(new float[] { 1, 2, 3 }, arr, 0.1f);
        assertEquals(3, buffer.position());

        buffer.get(1, arr);
        assertArrayEquals(new float[] { 2, 3, 4 }, arr, 0.1f);
        assertEquals(3, buffer.position());

        buffer.get(4, arr, 1, 2);
        assertArrayEquals(new float[] { 2, 5, 6 }, arr, 0.1f);
        assertEquals(3, buffer.position());
    }

    @Test
    public void bulkGetWrapper() {
        var buffer = ByteBuffer.wrap(new byte[] {
                        0x00, 0x00, (byte) 0x80, 0x3f,
                        0x00, 0x00, 0x00, 0x40,
                        0x00, 0x00, 0x40, 0x40,
                        0x00, 0x00, (byte) 0x80, 0x40,
                        0x00, 0x00, (byte) 0xA0, 0x40,
                        0x00, 0x00, (byte) 0xC0, 0x40
                })
                .order(ByteOrder.LITTLE_ENDIAN)
                .asFloatBuffer();
        var arr = new float[3];

        buffer.get(arr);
        assertArrayEquals(new float[] { 1, 2, 3 }, arr, 0.1f);
        assertEquals(3, buffer.position());

        buffer.get(1, arr);
        assertArrayEquals(new float[] { 2, 3, 4 }, arr, 0.1f);
        assertEquals(3, buffer.position());

        buffer.get(4, arr, 1, 2);
        assertArrayEquals(new float[] { 2, 5, 6 }, arr, 0.1f);
        assertEquals(3, buffer.position());

        buffer = ByteBuffer.wrap(new byte[] {
                        0x3f, (byte) 0x80, 0x00, 0x00,
                        0x40, 0x00, 0x00, 0x00,
                        0x40, 0x40, 0x00, 0x00,
                        0x40, (byte) 0x80, 0x00, 0x00,
                        0x40, (byte) 0xA0, 0x00, 0x00,
                        0x40, (byte) 0xC0, 0x00, 0x00
                })
                .order(ByteOrder.BIG_ENDIAN)
                .asFloatBuffer();

        buffer.get(arr);
        assertArrayEquals(new float[] { 1, 2, 3 }, arr, 0.1f);
        assertEquals(3, buffer.position());

        buffer.get(1, arr);
        assertArrayEquals(new float[] { 2, 3, 4 }, arr, 0.1f);
        assertEquals(3, buffer.position());

        buffer.get(4, arr, 1, 2);
        assertArrayEquals(new float[] { 2, 5, 6 }, arr, 0.1f);
        assertEquals(3, buffer.position());
    }
}
