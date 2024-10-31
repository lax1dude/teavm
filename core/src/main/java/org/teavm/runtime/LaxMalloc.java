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
package org.teavm.runtime;

import org.teavm.interop.Address;
import org.teavm.interop.StaticInit;
import org.teavm.interop.Unmanaged;

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
@Unmanaged
@StaticInit
public final class LaxMalloc {

	private LaxMalloc() {
	}

	private static final int SIZEOF_PTR = 4;
	private static final int SIZEOF_PTR_SH = 2;

	private static final int MIN_ALLOC_SIZE = 8;

	private static final int ADDR_HEAP_LIMIT = 4; // Address where we store the current heap limit (32 bit int)
	private static final int ADDR_HEAP_BUCKETS_FREE_MASK = 8; // Address where we store the bitmask of free chunk lists (64 bit int)
	private static final int ADDR_HEAP_BUCKETS_START = 16; // Address to the list of 64 pointers to the beginnings of the 64 buckets
	private static final int ADDR_HEAP_DATA_START = 272; // Beginning of the first chunk of the heap

	static {
		// zero out the control region
		Allocator.fillZero(Address.fromInt(0), ADDR_HEAP_DATA_START);
		// initialize heap limit
		Address.fromInt(ADDR_HEAP_LIMIT).putInt(ADDR_HEAP_DATA_START);
	}

	/**
	 * malloc implementation
	 */
	public static Address laxMalloc(int sizeBytes) {
		return laxAlloc(sizeBytes, false);
	}

	/**
	 * calloc implementation (zeroed malloc)
	 */
	public static Address laxCalloc(int sizeBytes) {
		return laxAlloc(sizeBytes, true);
	}

	private static Address laxAlloc(int sizeBytes, boolean cleared) {
		if(sizeBytes <= 0) {
			// Produce a null pointer if 0 or invalid size is requested
			return Address.fromInt(0);
		}
		
		// Allocation must be large enough to hold the two list pointers when the chunk becomes free again
		if(sizeBytes < MIN_ALLOC_SIZE) {
			sizeBytes = MIN_ALLOC_SIZE;
		}
		
		// always between 0-63
		int bucket = getListBucket(sizeBytes);
		
		if(bucket == 63) {
			// special bucket for the huge allocations
			// uses a different function
			return laxHugeAlloc(sizeBytes, cleared);
		}
		
		long bucketMask = Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).getLong();
		
		// test the bucket mask if the bucket has any free chunks
		if((bucketMask & (1L << bucket)) == 0l) {
			// no more free chunks, let us first check if there are any
			// chunks in the larger buckets we can split
			long largerBucketsMask = (bucketMask & (0xFFFFFFFFFFFFFFFFL << (bucket + 1)));
			if(largerBucketsMask != 0l) {
				// at least one larger chunk exists
				// we can quickly find it using the bitmask
				int largerBucket = numberOfTrailingZerosL(largerBucketsMask);
				
				Address bucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(largerBucket << SIZEOF_PTR_SH);
				Address chunkPtr = bucketStartAddr.getAddress();
				int chunkSize = readChunkSize(chunkPtr);
				
				int chunkNewSize = chunkSize - sizeBytes - 8; // -size - 2 ints - 2 more ints
				
				// if the other half of the new chunk is too small, check an even larger bucket
				// we should only need to look at an even larger bucket one more time before giving up
				if(chunkNewSize - 8 < MIN_ALLOC_SIZE) {
					//TODO
				}
				
				// remove the large chunk from its bucket 
				unlinkChunkFromFreeList(chunkPtr, chunkSize);
				
				// provision the part of the large chunk we want
				int sizePlusInts = sizeBytes + 8; // size + 2 ints
				chunkPtr.putInt(sizePlusInts | 0x80000000); // size + in use flag
				chunkPtr.add(sizeBytes + 4).putInt(sizePlusInts); // size integer at the end
				
				// provision the other part of the chunk that we want to return to the free list
				Address otherChunkPtr = chunkPtr.add(sizePlusInts);
				otherChunkPtr.putInt(chunkNewSize); // size
				otherChunkPtr.add(chunkNewSize - 4).putInt(chunkNewSize); // size (end)
				
				// return the other part of the chunk to the free chunks list
				linkChunkInFreeList(otherChunkPtr, chunkNewSize);

				// +4 bytes to skip size
				Address ret = chunkPtr.add(4);
				
				// clear if requested
				if(cleared) {
					Allocator.fillZero(ret, sizeBytes);
				}
				
				return ret;
			}else {
				// No larger chunks already exist that we can split,
				// time to sbrk
				int sizePlusInts = sizeBytes + 8; // size + 2 ints
				Address newChunk = growHeap(sizePlusInts);
				
				// Out of memory
				if(newChunk.toInt() == 0) {
					return Address.fromInt(0); //TODO
				}
				
				// provision the new chunk
				newChunk.putInt(sizePlusInts | 0x80000000); // size + in use flag
				newChunk.add(sizeBytes + 4).putInt(sizePlusInts); // size integer at the end
				
				// return the chunk, +4 bytes to skip size int
				// we don't need to clear it because its new memory
				return newChunk.add(4);
			}
		}else {
			// At least one free chunk is available, get it from the bucket
			Address bucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(bucket << SIZEOF_PTR_SH);
			Address chunkPtr = bucketStartAddr.getAddress();
			
			Address nextStart = readChunkNextFreeAddr(chunkPtr);
			if(nextStart.toInt() != 0) {
				// there is another free chunk in the bucket that comes after this chunk,
				// make the next free chunk in the list the first free chunk
				bucketStartAddr.putAddress(nextStart);
				writeChunkPrevFreeAddr(nextStart, Address.fromInt(0));
			}else {
				// there are no remaining free chunks in the bucket
				// clear the bit in the bucket bitmask
				bucketMask = (bucketMask ^ (1L << bucket));
				Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).putLong(bucketMask);
				
				// set bucket start chunk pointer to null
				bucketStartAddr.putAddress(Address.fromInt(0));
			}
			
			// mark the chunk in use
			setChunkInUse(chunkPtr, true);
			
			// return the chunk we just removed from the list, +4 bytes to skip size
			Address ret = chunkPtr.add(4);
			
			// clear if requested
			if(cleared) {
				Allocator.fillZero(ret, sizeBytes);
			}
			
			return ret;
		}
	}

	private static Address laxHugeAlloc(int sizeBytes, boolean cleared) {
		return null; //TODO: bucket number 63
	}

	/**
	 * free implementation<br><br>
	 * 
	 * bad things will happen if you free an address that was never allocated
	 */
	public static void laxFree(Address address) {
		if(address.toInt() == 0) {
			return;
		}
		
		// chunk actually starts 4 bytes before
		Address chunkPtr = address.add(-4);
		
		// set the chunk no longer in use
		setChunkInUse(chunkPtr, false);
		
		// bring the size of the chunk into the stack
		int chunkSize = chunkPtr.getInt();
		
		if(Address.fromInt(ADDR_HEAP_DATA_START).isLessThan(chunkPtr)) {
			// check if we can merge with the previous chunk, and move it to another bucket
			Address prevChunkPtr = chunkPtr.add(-(chunkPtr.add(-4).getInt()));
			int prevChunkSize = readChunkSizeStatus(prevChunkPtr);
			if((prevChunkSize & 0x80000000) == 0) {
				// previous chunk is not in use, merge!
				
				// remove the previous chunk from its list
				unlinkChunkFromFreeList(prevChunkPtr, prevChunkSize);
				
				// resize the current chunk to also contain the previous chunk
				chunkPtr = prevChunkPtr;
				chunkSize += prevChunkSize;
				chunkPtr.putInt(chunkSize);
				chunkPtr.add(chunkSize).putInt(chunkSize);
			}
		}
		
		Address nextChunkPtr = chunkPtr.add(chunkSize);
		if(Address.fromInt(ADDR_HEAP_LIMIT).getAddress().isLessThan(nextChunkPtr)) {
			// check if we can merge with the next chunk as well
			int nextChunkSize = readChunkSizeStatus(nextChunkPtr);
			if((nextChunkSize & 0x80000000) == 0) {
				// next chunk is not in use, merge!

				// remove the next chunk from its list
				unlinkChunkFromFreeList(nextChunkPtr, nextChunkSize);
				
				// resize the current chunk to also contain the next chunk
				chunkSize += nextChunkSize;
				chunkPtr.putInt(chunkSize);
				chunkPtr.add(chunkSize).putInt(chunkSize);
			}
		}
		
		// add the final chunk to the free chunks list
		linkChunkInFreeList(chunkPtr, chunkSize);
	}

	private static void linkChunkInFreeList(Address chunkPtr, int chunkSize) {
		int bucket = getListBucket(chunkSize - 8); // size - 2 ints
		
		long bucketMask = Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).getLong();
		Address bucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(bucket << SIZEOF_PTR_SH);
		
		// test the bucket mask if the bucket is empty
		if((bucketMask & (1L << bucket)) == 0l) {
			// bucket is empty, add the free chunk to the list
			bucketStartAddr.putAddress(chunkPtr);
			writeChunkPrevFreeAddr(chunkPtr, Address.fromInt(0));
			writeChunkNextFreeAddr(chunkPtr, Address.fromInt(0));
			// set the free bit in bucket mask
			bucketMask |= (1L << bucket);
			Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).putLong(bucketMask);
		}else {
			// bucket is not empty, append to the bucket's existing free chunks list
			Address otherBucketStart = bucketStartAddr.getAddress();
			writeChunkPrevFreeAddr(otherBucketStart, chunkPtr);
			writeChunkNextFreeAddr(chunkPtr, otherBucketStart);
			writeChunkPrevFreeAddr(chunkPtr, Address.fromInt(0));
			bucketStartAddr.putAddress(chunkPtr);
		}
	}

	private static void unlinkChunkFromFreeList(Address chunkPtr, int chunkSize) {
		Address prevChunkPtr = readChunkPrevFreeAddr(chunkPtr);
		Address nextChunkPtr = readChunkNextFreeAddr(chunkPtr);
		if((prevChunkPtr.toInt() | nextChunkPtr.toInt()) == 0) {
			// chunk is the only one currently in its bucket
			
			int chunkBucket = getListBucket(chunkSize - 8); // size - 2 ints
			
			Address bucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(chunkBucket << SIZEOF_PTR_SH);
			bucketStartAddr.putAddress(Address.fromInt(0)); // remove chunk from the bucket
			
			// clear the bit in the free buckets bitmask
			long bucketsFreeMask = Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).getLong();
			bucketsFreeMask &= ~(1L << chunkBucket);
			Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).putLong(bucketsFreeMask);
			
		}else {
			// there are other chunks in this bucket
			
			if(prevChunkPtr.toInt() != 0) {
				// previous chunk exists
				
				if(nextChunkPtr.toInt() != 0) {
					// next chunk exits, link it to the previous chunk
					writeChunkNextFreeAddr(prevChunkPtr, nextChunkPtr);
					writeChunkPrevFreeAddr(nextChunkPtr, prevChunkPtr);
				}else {
					// there is no next chunk
					writeChunkNextFreeAddr(prevChunkPtr, Address.fromInt(0));
				}
				
			}else {
				// no previous chunk, this must be the first chunk in the bucket
				
				int chunkBucket = getListBucket(chunkSize - 8); // size - 2 ints
				Address bucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(chunkBucket << SIZEOF_PTR_SH);
				
				// we already know the next chunk exists
				// make the next chunk the first chunk in the bucket
				bucketStartAddr.putAddress(nextChunkPtr);
				
				// unlink the next chunk from the current chunk
				writeChunkPrevFreeAddr(nextChunkPtr, Address.fromInt(0));
			}
		}
	}

	private static final int NUM_FREE_BUCKETS = 64;

	/**
	 * https://github.com/emscripten-core/emscripten/blob/16a0bf174cb85f88b6d9dcc8ee7fbca59390185b/system/lib/emmalloc.c#L241
	 * (MIT License)
	 */
	private static int getListBucket(int allocSize) {
		if (allocSize < 128)
			return (allocSize >> 3) - 1;
		
		int clz = numberOfLeadingZerosI(allocSize);
		int bucketIndex = (clz > 19) ? 110 - (clz << 2) + ((allocSize >> (29 - clz)) ^ 4)
				: min(71 - (clz << 1) + ((allocSize >> (30 - clz)) ^ 2), NUM_FREE_BUCKETS - 1);

		return bucketIndex;
	}

	/**
	 * This is our sbrk
	 */
	private static Address growHeap(int amount) {
		Address heapLimit = Address.fromInt(ADDR_HEAP_LIMIT).getAddress();
		Address.fromInt(ADDR_HEAP_LIMIT).putAddress(heapLimit.add(amount));
		//TODO: expand WebAssembly Memory
		return heapLimit;
	}

	private static int readChunkSizeStatus(Address chunkAddr) {
		return chunkAddr.getInt();
	}

	private static int readChunkSize(Address chunkAddr) {
		return chunkAddr.getInt() & 0x7FFFFFFF;
	}

	private static boolean readChunkInUse(Address chunkAddr) {
		return (chunkAddr.getInt() & 0x80000000) != 0;
	}

	private static void writeChunkSizeStatus(Address chunkAddr, int sizeStatus) {
		chunkAddr.putInt(sizeStatus);
	}

	private static void setChunkInUse(Address chunkAddr, boolean inUse) {
		int i = chunkAddr.getInt();
		chunkAddr.putInt(inUse ? (i | 0x80000000) : (i & 0x7FFFFFFF));
	}

	private static Address readChunkPrevFreeAddr(Address chunkAddr) {
		return chunkAddr.add(4).getAddress();
	}

	private static void writeChunkPrevFreeAddr(Address chunkAddr, Address prevFree) {
		chunkAddr.add(4).putAddress(prevFree);
	}

	private static Address readChunkNextFreeAddr(Address chunkAddr) {
		return chunkAddr.add(4 + (1 << SIZEOF_PTR_SH)).getAddress();
	}

	private static void writeChunkNextFreeAddr(Address chunkAddr, Address nextFree) {
		chunkAddr.add(4 + (1 << SIZEOF_PTR_SH)).putAddress(nextFree);
	}

	private static int min(int a, int b) {
		return a < b ? a : b;
	}

	private static int numberOfTrailingZerosL(long i) {
    	//TODO: Intrinsify this, WASM has dedicated instructions for this operation!!!
    	return Long.numberOfTrailingZeros(i);
    }

	private static int numberOfLeadingZerosI(int i) {
    	//TODO: Intrinsify this, WASM has dedicated instructions for this operation!!!
    	return Integer.numberOfLeadingZeros(i);
    }

}
