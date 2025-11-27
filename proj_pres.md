---
theme:
  name: dark
title: Towards a Verified CDCL SAT Solver in Lean
author: Arjun S. Bhamra and Cameron C. Hoechst
---

Verifying SAT Solvers; why care?
---

<!--
This is a multi-line comment.
use pause command for two-step slides
-->

On this slide, discuss the why of SAT solvers (lean towards mission critical applications), then discuss how verification is important

<!-- end_slide -->

How can we verify SAT solvers?
---
Talk about the two possible ways:
+ Trust-but-verify
+ Full formal verification

<!-- end_slide -->

Our Contribution: CDCL in Lean (with some proofs!)
---
- Data Structures
- Our implementation of overall flow/structure of CDCL in Lean (what we added that makes it CDCL vs DPLL)
- What proofs we did, where we focused our efforts!

## Split the above over a couple of slides

<!-- end_slide -->

Current Progress
---
Describe where we are currently at w.r.t progress, what we have and haven't proved!

## Also split this over a few slides

<!-- end_slide -->

Experimental Evaluation
---
Lack of experimental eval should be noted

<!-- end_slide -->

Related work
---
Describe wealth of work by Fleury, etc. for properly verified SAT solvers

Also explain the cool work done by CreuSAT, etc., for fast and effective trust-but-verify style sat solvers that are practical!

As well as verified proof chcekers, LRAT/DRAT formats, etc.

<!-- end_slide -->

Conclusions
---
Restate contributions, describe stuff again, why is worth it?
(tapping into Lean ecosystem is hugely valuable)

<!-- end_slide -->

Future Work
---
Explain future plans, what else to prove, overarching goal of the no-relearning theorem, building up to it

<!-- end_slide -->

Where to find our work?
---
<!-- jump_to_middle -->
---
Our solver and proofs can be found at [](https://github.com/abhamra/verified-CDCL-datastructures); feedback is appreciated!

---

<!-- end_slide -->


References
---
List all our refs fr fr

<!-- end_slide -->


<!-- jump_to_middle -->

The end (questions?)
---
