import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionEndHomotopies
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.RotatedResolutionWords

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

variable {X : Type*} [TopologicalSpace X] {Z : Set X} {τ : ((ℝ × ℝ) × ℝ) → X}
  {b : ℝ} (d0 : MarkedResolutionEndData Z τ b 0) (d1 : MarkedResolutionEndData Z τ b 1)
  {base : Z} (J : Subgroup (FundamentalGroup Z base)) [J.Normal]
  (p : Path base d0.z) (q : Path base d1.z)

theorem actual_resolution_pair_excluded_case_a
    (a : Path d0.a d1.a) (β : Path d1.r d1.l)
    (c : Path d1.c d0.c) (d : Path d0.l d0.r)
    (RU RV : Path d0.c d0.c)
    (hU : RU.Homotopic (((d0.U.symm.trans a).trans d1.U).trans c))
    (hV : RV.Homotopic (((((((d0.R.symm.trans d.symm).trans d0.L).trans a).trans
      d1.L.symm).trans β.symm).trans d1.R).trans c))
    (hout : basedPathWord (p.trans d0.ra) (q.trans d1.ra) a *
      basedPathWord (q.trans d1.rr) (q.trans d1.rl) β *
      basedPathWord (q.trans d1.rc) (p.trans d0.rc) c *
      basedPathWord (p.trans d0.rl) (p.trans d0.rr) d ∉ J) :
    (p.trans d0.rc).whiskeredLoopClass RU ∉ J ∨
      (p.trans d0.rc).whiskeredLoopClass RV ∉ J := by
  obtain ⟨hwordU, hwordV⟩ := rotated_resolution_end_words_case_a p q
    d0.ra d0.rc d0.rl d0.rr d1.ra d1.rc d1.rl d1.rr
    d0.U d0.L d0.R d1.U d1.L d1.R d0.U_homotopic d0.L_homotopic d0.R_homotopic
    d1.U_homotopic d1.L_homotopic d1.R_homotopic a β c d
  by_contra h
  push Not at h
  have hu : basedPathWord (p.trans d0.rc) (p.trans d0.rc) RU ∈ J := J.inv_mem h.1
  have hv : basedPathWord (p.trans d0.rc) (p.trans d0.rc) RV ∈ J := J.inv_mem h.2
  rw [basedPathWord_congr _ _ hU, hwordU] at hu
  rw [basedPathWord_congr _ _ hV, hwordV] at hv
  apply hout
  apply old_word_mem_of_case_a J hu
  have hrot := (Subgroup.Normal.mem_comm_iff ‹J.Normal›).mp
    (show (basedPathWord (p.trans d0.rl) (p.trans d0.rr) d)⁻¹ *
      (basedPathWord (p.trans d0.ra) (q.trans d1.ra) a *
        (basedPathWord (q.trans d1.rr) (q.trans d1.rl) β)⁻¹ *
        basedPathWord (q.trans d1.rc) (p.trans d0.rc) c) ∈ J by
      simpa only [mul_assoc] using hv)
  exact hrot

theorem actual_resolution_pair_excluded_case_b
    (a : Path d1.a d0.a) (β : Path d0.r d1.l)
    (c : Path d1.c d0.c) (d : Path d0.l d1.r)
    (RU RV : Path d0.c d0.c)
    (hU : RU.Homotopic (((d0.U.symm.trans a.symm).trans d1.U).trans c))
    (hV : RV.Homotopic (((((((d0.R.symm.trans β).trans d1.L).trans a).trans
      d0.L.symm).trans d).trans d1.R).trans c))
    (hout : basedPathWord (q.trans d1.ra) (p.trans d0.ra) a *
      basedPathWord (p.trans d0.rr) (q.trans d1.rl) β *
      basedPathWord (q.trans d1.rc) (p.trans d0.rc) c *
      basedPathWord (p.trans d0.rl) (q.trans d1.rr) d ∉ J) :
    (p.trans d0.rc).whiskeredLoopClass RU ∉ J ∨
      (p.trans d0.rc).whiskeredLoopClass RV ∉ J := by
  obtain ⟨hwordU, hwordV⟩ := rotated_resolution_end_words_case_b p q
    d0.ra d0.rc d0.rl d0.rr d1.ra d1.rc d1.rl d1.rr
    d0.U d0.L d0.R d1.U d1.L d1.R d0.U_homotopic d0.L_homotopic d0.R_homotopic
    d1.U_homotopic d1.L_homotopic d1.R_homotopic a β c d
  by_contra h
  push Not at h
  have hu : basedPathWord (p.trans d0.rc) (p.trans d0.rc) RU ∈ J := J.inv_mem h.1
  have hv : basedPathWord (p.trans d0.rc) (p.trans d0.rc) RV ∈ J := J.inv_mem h.2
  rw [basedPathWord_congr _ _ hV, hwordV] at hv
  have huInv := J.inv_mem hu
  rw [← basedPathWord_symm] at huInv
  have hUi : RU.symm.Homotopic (((c.symm.trans d1.U.symm).trans a).trans d0.U) := by
    apply hU.symm₂.trans
    apply Path.Homotopic.Quotient.eq.mp
    simp only [Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.trans_assoc]
  rw [basedPathWord_congr _ _ hUi, hwordU] at huInv
  apply hout
  apply old_word_mem_of_case_b J
  · exact (Subgroup.Normal.mem_comm_iff ‹J.Normal›).mp huInv
  · have hrot := (Subgroup.Normal.mem_comm_iff ‹J.Normal›).mp
      (show basedPathWord (p.trans d0.rr) (q.trans d1.rl) β *
        (basedPathWord (q.trans d1.ra) (p.trans d0.ra) a *
          basedPathWord (p.trans d0.rl) (q.trans d1.rr) d *
          basedPathWord (q.trans d1.rc) (p.trans d0.rc) c) ∈ J by
        simpa only [mul_assoc] using hv)
    exact hrot

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
