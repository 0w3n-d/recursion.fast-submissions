# Provenance: submissions/baseline/extractor.S at commit 91b3a56 (itself the core's tests/asm/proofwords.S); the image of RecursionFast.Library.WitnessSending.img.
# The witness-sending extractor (Library/WitnessSending.lean, Controls/Extractor.lean): output the
# proof's packed words in place. Input tape (Contract/Extractor.lean): words 0-3 the statement,
# word 4 the proof's byte length |pi|, words 5 .. 5 + ceil(|pi|/8) - 1 its packed bytes.
  addi t1, x0, 1
  slli t1, t1, 63      # t1 = TAPE_BASE
  ld   a1, 32(t1)      # a1 = |pi| (tape word 4)
  addi a1, a1, 7
  srli a1, a1, 3       # a1 = ceil(|pi| / 8), the number of output words
  addi a0, t1, 40      # a0 = address of tape word 5
  addi t0, x0, 0       # HALT
  ecall
