import PoincareLib.Geometry.RicciFlow.Surgery.Volume.FinitePrefixTheory
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Finiteness.Observed
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Finiteness.Compact

/-!
Adapted from Mapher `PoincareMT/Proofs/M50.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Finite surgery counts and no finite accumulation

Natural-language theorem: a raw changing-carrier flow with its exact M49
volume-loss certificate has finite surgery sets on compact time intervals and no finite
accumulation on that same flow. M48 owns finite epoch continuation. This
milestone adds no generic extension, global schedule or terminal-time claim.
Its input is the produced certificate on that flow, not a whole M49 theory
whose freshly chosen cutoff might be unavailable for the given flow.

Source: Morgan--Tian, Theorem 15.9, pp. 363--366, and Section 17.2,
especially Lemma 17.12, MT2007.txt pp. 410--411 (arXiv V2 pp. 395--397).
The corrected M49 volume scaling is recorded in
`reviews/errata/2026-09-10-surgery-extinction-audit.md`.

The finite-subset argument is recorded in
`reviews/contracts/2026-09-20-m50-finite-subsets.md`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The exact volume-loss certificate gives compact-set finiteness and no
finite accumulation (Morgan-Tian Lemma 17.12 and Section 17.2, pp. 410-411). -/
theorem repairedFinitePrefix : RepairedFinitePrefixTheory.{u} := by
  refine ⟨?_⟩
  intro F C V
  have hlocal := SurgeryFiniteness.surgery_times_inter_compact_finite F C V
  refine ⟨⟨V, rfl, hlocal, ?_⟩⟩
  intro T
  refine ⟨1, zero_lt_one, ?_⟩
  exact (hlocal (Set.Icc (T - 1) (T + 1)) isCompact_Icc).subset
    (Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self)

end PoincareMT
