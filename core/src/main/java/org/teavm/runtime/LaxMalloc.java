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
			// uses a different slower function
			return laxHugeAlloc(sizeBytes, cleared);
		}
		
		// load bitmask of buckets with free chunks
		long bucketMask = Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).getLong();
		
		// mask away the buckets that we know are too small for this allocation
		bucketMask = (bucketMask & (0xFFFFFFFFFFFFFFFFL << bucket));
		
		// there are no more buckets with free chunks
		// need to sbrk
		if(bucketMask == 0l) {
			int sizePlusInts = sizeBytes + 8; // size + 2 ints
			Address newChunk = growHeap(sizePlusInts); // sbrk
			
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
		
		// at least one bucket exists containing a free chunk,
		// quickly determine which bucket it is with bit hacks
		int availableBucket = numberOfTrailingZerosL(bucketMask);
		
		Address bucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(availableBucket << SIZEOF_PTR_SH);
		Address chunkPtr = bucketStartAddr.getAddress();
		int chunkSize = readChunkSize(chunkPtr);
		boolean bucketHasMultipleChunks = false;
		
		// check if the first chunk in the bucket is large enough
		if(chunkSize - 8 < sizeBytes) { // size - 2 ints
			
			// the chunk is not large enough, move the first chunk to the end of the list
			// and then check in the next bucket (where the chunks are definitely large enough)
			// this functionality is present in emmalloc (emscripten)
			
			Address chunkNextPtr = readChunkNextFreeAddr(chunkPtr);
			if(chunkNextPtr.getInt() != chunkPtr.getInt()) {
				bucketStartAddr.putAddress(chunkNextPtr);
				chunkPtr = chunkNextPtr;
				bucketHasMultipleChunks = true;
			}
			
			// extend mask to the next bucket
			bucketMask = (bucketMask & (0xFFFFFFFFFFFFFFFFL << (bucket + 1)));
			
			if(bucketMask != 0l) {
				// there is a bucket with a larger chunk
				int availableLargerBucket = numberOfTrailingZerosL(bucketMask);
				Address largerBucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(availableLargerBucket << SIZEOF_PTR_SH);
				Address largerChunkPtr = largerBucketStartAddr.getAddress();
				int largerChunkSize = readChunkSize(largerChunkPtr);
				
				// this will remove the chunk from the free list
				allocateMemoryFromChunk(largerChunkPtr, largerChunkSize, sizeBytes);
				
				// +4 bytes to skip size int
				Address ret = largerChunkPtr.add(4);
				
				// clear if requested
				if(cleared) {
					Allocator.fillZero(ret, sizeBytes);
				}
				
				return ret;
			}
		}else {
			// the first chunk in the bucket is large enough
			// this will remove the chunk from the free list
			allocateMemoryFromChunk(chunkPtr, chunkSize, sizeBytes);
			
			// +4 bytes to skip size int
			Address ret = chunkPtr.add(4);
			
			// clear if requested
			if(cleared) {
				Allocator.fillZero(ret, sizeBytes);
			}
			
			return ret;
		}
		
		if(bucketHasMultipleChunks) {
			
			// if we've reached this point, it means the first chunk in the bucket wasn't large enough
			// and there weren't any chunks in the larger buckets we could split up
			// so we need to look closer
			
			// iterate the (only) bucket of possibly large enough chunks
			Address addrIterator = chunkPtr;
			while((addrIterator = readChunkNextFreeAddr(addrIterator)).getInt() != chunkPtr.getInt()) {
				chunkSize = readChunkSize(addrIterator);
				
				// check if the chunk is large enough
				if(chunkSize - 8 >= sizeBytes) { // size - 2 ints
					// we've found a large enough chunk
					// this will remove the chunk from the free list
					allocateMemoryFromChunk(addrIterator, chunkSize, sizeBytes);
					
					// +4 bytes to skip size int
					Address ret = chunkPtr.add(4);
					
					// clear if requested
					if(cleared) {
						Allocator.fillZero(ret, sizeBytes);
					}
					
					return ret;
				}
			}
		}
		
		// no other options, time to sbrk
		
		int sizePlusInts = sizeBytes + 8; // size + 2 ints
		Address newChunk = growHeap(sizePlusInts); // sbrk
		
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

	private static Address laxHugeAlloc(int sizeBytes, boolean cleared) {
		
		// check the bucket mask if bucket 63 has any chunks
		if((Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).getLong() & 0x8000000000000000L) != 0) {

			// bucket 63 address
			Address bucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(63 << SIZEOF_PTR_SH);
			Address chunkPtr = bucketStartAddr.getAddress();
			
			// iterate all free huge chunks
			Address addrIterator = chunkPtr;
			while((addrIterator = readChunkNextFreeAddr(addrIterator)).getInt() != chunkPtr.getInt()) {
				int chunkSize = readChunkSize(addrIterator);
				
				if(chunkSize - 8 >= sizeBytes) { // size - 2 ints
					// we've found a large enough chunk
					// this will remove the chunk from the free list
					allocateMemoryFromChunk(addrIterator, chunkSize, sizeBytes);
					
					// +4 bytes to skip size int
					Address ret = chunkPtr.add(4);
					
					// clear if requested
					if(cleared) {
						Allocator.fillZero(ret, sizeBytes);
					}
					
					return ret;
				}
			}
		}
		
		// no free huge chunks found, time to sbrk
		
		int sizePlusInts = sizeBytes + 8; // size + 2 ints
		Address newChunk = growHeap(sizePlusInts); // sbrk
		
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
				chunkPtr.add(chunkSize - 4).putInt(chunkSize);
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
				chunkPtr.add(chunkSize - 4).putInt(chunkSize);
			}
		}
		
		// add the final chunk to the free chunks list
		linkChunkInFreeList(chunkPtr, chunkSize);
	}

	/**
	 * Allocates memory from a free chunk, if the allocSize is smaller than the chunkSize by
	 * enough of a margin then the chunk is split into two smaller chunks, and the upper part
	 * of the chunk is returned to a bucket of free chunks
	 */
	private static void allocateMemoryFromChunk(Address chunkPtr, int chunkSize, int allocSize) {
		// remove the chunk from its bucket 
		unlinkChunkFromFreeList(chunkPtr, chunkSize);
		
		int otherHalfSize = chunkSize - allocSize - 8; // -size - 2 ints
		
		// check if we can split the chunk into two smaller chunks
		// chunk must be large enough to hold the 2 list pointers
		if(otherHalfSize - (2 << SIZEOF_PTR_SH) >= MIN_ALLOC_SIZE) {
			// chunk is large enough to split
			
			// provision the lower part of the chunk, the part we want to use
			int sizePlusInts = allocSize + 8; // size + 2 ints
			chunkPtr.putInt(sizePlusInts | 0x80000000); // size + in use flag
			chunkPtr.add(allocSize + 4).putInt(sizePlusInts); // size integer at the end
			
			// provision the upper part of the chunk that we want to return to the free list
			Address otherChunkPtr = chunkPtr.add(sizePlusInts);
			otherChunkPtr.putInt(otherHalfSize); // size
			otherChunkPtr.add(otherHalfSize - 4).putInt(otherHalfSize); // size (end)

			// return the upper part of the chunk to the free chunks list
			linkChunkInFreeList(otherChunkPtr, otherHalfSize);

		}else {
			// not large enough to split, just take the entire chunk
			setChunkInUse(chunkPtr, true);
		}
	}

	/**
	 * Adds a free chunk to its corresponding bucket
	 */
	private static void linkChunkInFreeList(Address chunkPtr, int chunkSize) {
		int bucket = getListBucket(chunkSize - 8); // size - 2 ints
		
		long bucketMask = Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).getLong();
		Address bucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(bucket << SIZEOF_PTR_SH);
		
		// test the bucket mask if the bucket is empty
		if((bucketMask & (1L << bucket)) == 0l) {
			
			// bucket is empty, add the free chunk to the list
			bucketStartAddr.putAddress(chunkPtr);
			writeChunkPrevFreeAddr(chunkPtr, chunkPtr);
			writeChunkNextFreeAddr(chunkPtr, chunkPtr);
			
			// set the free bit in bucket mask
			bucketMask |= (1L << bucket);
			Address.fromInt(ADDR_HEAP_BUCKETS_FREE_MASK).putLong(bucketMask);
			
		}else {
			
			// bucket is not empty, append to the bucket's existing free chunks list
			Address otherBucketStart = bucketStartAddr.getAddress();
			Address otherBucketPrev = readChunkPrevFreeAddr(otherBucketStart);
			
			// link new chunk to the existing chunks in the bucket
			writeChunkPrevFreeAddr(chunkPtr, otherBucketPrev);
			writeChunkNextFreeAddr(chunkPtr, otherBucketStart);
			
			// link the existing chunks in the bucket to the new chunk
			writeChunkPrevFreeAddr(otherBucketStart, chunkPtr);
			writeChunkNextFreeAddr(otherBucketPrev, chunkPtr);
			
			// put the chunk in the bucket
			bucketStartAddr.putAddress(chunkPtr);
			
		}
	}

	/**
	 * Removes a free chunk from its corresponding bucket
	 */
	private static void unlinkChunkFromFreeList(Address chunkPtr, int chunkSize) {
		Address prevChunkPtr = readChunkPrevFreeAddr(chunkPtr);
		Address nextChunkPtr = readChunkNextFreeAddr(chunkPtr);
		if(prevChunkPtr.toInt() == nextChunkPtr.toInt()) {
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
			
			// link the next chunk to the previous chunk
			writeChunkNextFreeAddr(prevChunkPtr, nextChunkPtr);
			writeChunkPrevFreeAddr(nextChunkPtr, prevChunkPtr);
			
			int chunkBucket = getListBucket(chunkSize - 8); // size - 2 ints
			Address bucketStartAddr = Address.fromInt(ADDR_HEAP_BUCKETS_START).add(chunkBucket << SIZEOF_PTR_SH);
			Address bucketStartChunk = bucketStartAddr.getAddress();
			
			// chunk is the first in the bucket, so we also need to
			// update the bucket to point to the next chunk instead
			if(bucketStartChunk.toInt() == chunkPtr.toInt()) {
				bucketStartAddr.putAddress(nextChunkPtr);
			}
		}
	}

	/**
	 * https://github.com/emscripten-core/emscripten/blob/16a0bf174cb85f88b6d9dcc8ee7fbca59390185b/system/lib/emmalloc.c#L241
	 * (MIT License)
	 */
	private static int getListBucket(int allocSize) {
		if (allocSize < 128)
			return (allocSize >> 3) - 1;
		
		int clz = numberOfLeadingZerosI(allocSize);
		int bucketIndex = (clz > 19) ? 110 - (clz << 2) + ((allocSize >> (29 - clz)) ^ 4)
				: min(71 - (clz << 1) + ((allocSize >> (30 - clz)) ^ 2), 63);

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
