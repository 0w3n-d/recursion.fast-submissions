//! Minimal data parallelism on `std::thread::scope` (no dependencies, so the build is offline).

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::OnceLock;

static THREADS: OnceLock<usize> = OnceLock::new();

pub fn threads() -> usize {
    *THREADS.get_or_init(|| {
        std::env::var("SPARTAN_THREADS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1))
            .max(1)
    })
}

/// Run `f(lo, hi)` over `[0, n)` split into chunks of at least `min_chunk`, in parallel, and
/// return the per-chunk results in order.
pub fn map_chunks<R: Send, F: Fn(usize, usize) -> R + Sync>(n: usize, min_chunk: usize, f: F) -> Vec<R> {
    let t = threads();
    let nchunks = if n == 0 { 0 } else { (n / min_chunk.max(1)).clamp(1, 4 * t) };
    if nchunks <= 1 || t == 1 {
        return if n == 0 { vec![] } else { vec![f(0, n)] };
    }
    let bounds: Vec<(usize, usize)> =
        (0..nchunks).map(|c| (c * n / nchunks, (c + 1) * n / nchunks)).collect();
    let next = AtomicUsize::new(0);
    let mut out: Vec<Option<R>> = (0..nchunks).map(|_| None).collect();
    let slots: Vec<std::sync::Mutex<&mut Option<R>>> =
        out.iter_mut().map(std::sync::Mutex::new).collect();
    std::thread::scope(|s| {
        for _ in 0..t.min(nchunks) {
            s.spawn(|| loop {
                let c = next.fetch_add(1, Ordering::Relaxed);
                if c >= nchunks {
                    break;
                }
                let r = f(bounds[c].0, bounds[c].1);
                **slots[c].lock().unwrap() = Some(r);
            });
        }
    });
    drop(slots);
    out.into_iter().map(|r| r.unwrap()).collect()
}

/// Fill `out[i] = f(i)` in parallel.
pub fn fill<T: Send, F: Fn(usize) -> T + Sync>(out: &mut [T], min_chunk: usize, f: F) {
    for_each_chunk_mut(out, min_chunk, |base, chunk| {
        for (i, o) in chunk.iter_mut().enumerate() {
            *o = f(base + i);
        }
    });
}

/// Call `f(offset, chunk)` on disjoint mutable chunks of `out`, in parallel.
pub fn for_each_chunk_mut<T: Send, F: Fn(usize, &mut [T]) + Sync>(out: &mut [T], min_chunk: usize, f: F) {
    let n = out.len();
    let t = threads();
    let nchunks = if n == 0 { 0 } else { (n / min_chunk.max(1)).clamp(1, 4 * t) };
    if nchunks <= 1 || t == 1 {
        f(0, out);
        return;
    }
    let size = n.div_ceil(nchunks);
    let chunks: Vec<(usize, &mut [T])> =
        out.chunks_mut(size).enumerate().map(|(i, c)| (i * size, c)).collect();
    let queue = std::sync::Mutex::new(chunks);
    std::thread::scope(|s| {
        for _ in 0..t {
            s.spawn(|| loop {
                let item = queue.lock().unwrap().pop();
                match item {
                    Some((off, c)) => f(off, c),
                    None => break,
                }
            });
        }
    });
}

/// `(0..n).map(f).collect()` in parallel, without a serial initialisation pass.
pub fn collect_vec<T: Send, F: Fn(usize) -> T + Sync>(n: usize, min_chunk: usize, f: F) -> Vec<T> {
    let mut v: Vec<T> = Vec::with_capacity(n);
    for_each_chunk_mut(&mut v.spare_capacity_mut()[..n], min_chunk, |off, chunk| {
        for (i, slot) in chunk.iter_mut().enumerate() {
            slot.write(f(off + i));
        }
    });
    // SAFETY: every slot in `[0, n)` was written exactly once above.
    unsafe { v.set_len(n) };
    v
}
