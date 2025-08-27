# A Hyperlocal Proof of the Riemann Hypothesis

This repository contains the manuscript and a one-page summary of a proof of the Riemann Hypothesis.

## Versioning Information

**Version 3.3 (Latest):** hyperlocal_RH_proof_ACs_v3.3_09082025.pdf available at GitHub.

* *Change remark:* This significant update within the v3 algebraic track solidifies the proof's claim to full generality by extending the computational verification to cover multiple zeros. The previous verification was limited to simple zeros (k=1). This version overcomes that obstacle using a sophisticated analytical shortcut based on Faà di Bruno's formula, enabling the successful verification for the foundational double zero case (k=2). This demonstrated the same pattern of immediate and stable algebraic overdetermination, closing a key theoretical gap. To further enhance clarity, this version also introduces a new 'Boundary of Stability' analysis—which is strategically placed as a post-proof discussion to preserve the minimalist focus of the main argument—and adds a comprehensive summary table for the proof's core algebraic engine.

* **Version 3.2:** hyperlocal_RH_proof_ACs_v3.2_24072025.pdf available at GitHub.

* *Change remark:* This version corrects a logical gap in the final contradiction argument of v3.1. The previous numerical verification in Appendix D relied on placeholder constraints to achieve an overdetermined system. This version replaces that heuristic with a rigorous, formal derivation of the necessary additional constraints using a Taylor series truncation and null space analysis. The updated appendix now presents a complete and computationally verifiable proof that the full system of symmetry constraints is of rank 6, forcing the contradiction. The verification has also been strengthened by including additional test cases (e.g., near-degenerate points) to demonstrate the robustness of the result. This closes the gap in the algebraic proof.

* **Version 3.1:** hyperlocal_RH_proof_ACs_v3.1_18072025.pdf available at GitHub.

* *Change remark:* This version enhances the rigor of the final proof. The computational verification appendix has been restructured into two parts: it now begins with a more elegant and efficient symbolic proof that formally demonstrates the initial system of equations is always underdetermined. This is followed by the numerical verification, which confirms the final, augmented system has full rank for generic cases and forces the contradiction. Additionally, a new remark on "Constructive Impossibility" has been added to the methodology section to better connect the proof's minimalist framework to its philosophical underpinnings.

* **Version 3.0:** hyperlocal_RH_proof_ACs_v3.0_17072025.pdf available at GitHub.

* *Change remark:* This major revision corrects a flaw in the previous proof framework. The "Affine Forcing Engine" and other arguments based on complex growth conditions were found to be insufficient to produce a contradiction. This version works out fully the existing algebraic track, which is more aligned with the proof's hyperlocal spirit. The asymptotic proof of the recurrence's universal instability is a main part of the argument. The final logical gap—the possibility of a "fine-tuned cancellation"—is now closed with a rigorous algebraic proof. It demonstrates that the function's symmetries impose an overdetermined system of linear equations on the initial Taylor coefficients, leading to an inescapable contradiction. This final step is supported by a new appendix containing a verifiable computational proof of the system's rank.

* **Version 2.1.1:** '`hyperlocal_RH_proof_ACs_v2.1.1_07072025.pdf`' [GitHub](https://github.com/attila-ac/hyperlocal).
    * *Change remark:* A minor textual refinement to further improve logical transparency. The justification for the function's order in the 'Growth Properties' section has been expanded to explicitly include the role of the Hadamard Factorization Theorem, making the non-circular nature of the argument more direct.

* **Version 2.1 (Latest):** `hyperlocal_RH_proof_ACs_v2.1_06072025.pdf` available at [GitHub](https://github.com/attila-ac/hyperlocal).
    * *Change remark:* A minor update focused on improving clarity and logical rigor. The justifications for the growth properties have been enriched and their logical placement in the manuscript improved. Additionally, new explanatory remarks have been added to the Affine Forcing Engine to clarify its mechanism and robustness.

* **Version 2:** `hyperlocal_RH_proof_ACs_v2_04072025.pdf` available at [GitHub](https://github.com/attila-ac/hyperlocal).
    * *Change remark:* This version introduces major structural and conceptual revisions. A flaw in the original "Line-To-Line Mapping Theorem" has been addressed by replacing it with a more rigorous *Affine Forcing Engine*, built upon a fully justified Boundedness Lemma. Furthermore, the paper has been substantially restructured: the "Clash of Natures" argument is now presented as the primary, unified proof in the main text, while the "Pure Algebraic" refutation has been moved to an appendix as a complete, alternative track. This reflects a key conceptual refinement: the minimal model polynomial is not subject to the conclusions of the Affine Forcing Engine, because as a polynomial, it inherently fails to satisfy the required growth properties (specifically, the vertical decay condition). This refined understanding clarifies the model's role as a purely algebraic diagnostic tool and has led to the removal of the previous "Ultimate Supporting Evidence" section.

* **Version 1:** `hyperlocal_RH_proof_ACs_v1_26062025.pdf` available at [GitHub](https://github.com/attila-ac/hyperlocal).

---

* **`hyperlocal_RH_proof_ACs_v2.1.1_07072025.pdf`**: The full manuscript (latest version).
* **`hyperlocal_one_pager_ACs_v2_04072025.pdf`**: A one-page summary of the proof's logical flow (based on v2).

## Build the formalisation

1. Install `elan` (Lean version manager).
2. Clone this repo and open it at the repo root.
3. Run:
lake update
lake build
4. Open `formalisation/Hyperlocal.lean` in VS Code and restart the Lean file.

## Author

**Attila Csordas** AgeCurve Limited, Cambridge, UK  
Email: `attila@agecurve.xyz`

## Feedback and Discussion

All comments and questions on the proof are welcome. To maintain the focus and standards of scholarly communication, comments on this repository have been disabled. Please feel free to reach out directly via email. For those in Cambridge, an in-person chalkboard presentation and discussion at our office can be arranged to follow up on substantive email correspondence.

License:$
This work is licensed under the **CC-BY-NC 4.0 International License**, allowing others to share and adapt the material for non-commercial purposes, provided proper attribution is given.$
