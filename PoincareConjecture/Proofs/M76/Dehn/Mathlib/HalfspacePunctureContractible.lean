import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspacePunctureConnected
import Mathlib.Analysis.Convex.Contractible









set_option autoImplicit false

open Set

namespace ContinuousAffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem contractibleSpace_halfspace_punctured_ball
    (ell : E →ᴬ[ℝ] ℝ) (hell : ell.toAffineMap.linear ≠ 0)
    {p : E} (hzero : ell p = 0) {ε : ℝ} (hε : 0 < ε) :
    ContractibleSpace ((Metric.ball p ε ∩ {x | 0 ≤ ell x}) \ {p} : Set E) := by
  have hopen : IsOpenMap (ell : E → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
    (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
  have hclosure : closure {x | 0 < ell x} = {x | 0 ≤ ell x} := by
    change closure ((ell : E → ℝ) ⁻¹' Ioi 0) = (ell : E → ℝ) ⁻¹' Ici 0
    rw [← hopen.preimage_closure_eq_closure_preimage ell.continuous, closure_Ioi]
  have hpclosure : p ∈ closure (Metric.ball p ε ∩ {x | 0 < ell x}) := by
    apply Metric.isOpen_ball.inter_closure
    refine ⟨Metric.mem_ball_self hε, ?_⟩
    rw [hclosure]
    change 0 ≤ ell p
    rw [hzero]
  obtain ⟨b, hbball, hbpos⟩ := (Set.nonempty_of_mem hpclosure).of_closure
  have hbpositive : 0 < ell b := hbpos
  have hb : b ∈ (Metric.ball p ε ∩ {x | 0 ≤ ell x}) \ {p} := by
    refine ⟨⟨hbball, hbpositive.le⟩, ?_⟩
    intro hbp
    have hbp' : b = p := Set.mem_singleton_iff.mp hbp
    exact (ne_of_gt hbpositive) (by simpa only [hbp'] using hzero)
  have hconv : Convex ℝ (Metric.ball p ε ∩ {x | 0 ≤ ell x}) :=
    (convex_ball p ε).inter ((convex_Ici (0 : ℝ)).affine_preimage ell.toAffineMap)
  have hstar : StarConvex ℝ b ((Metric.ball p ε ∩ {x | 0 ≤ ell x}) \ {p}) := by
    intro x hx a c ha hc hac
    refine ⟨hconv hb.1 hx.1 ha hc hac, ?_⟩
    by_cases ha0 : a = 0
    · have hc1 : c = 1 := by linarith
      simpa only [ha0, hc1, zero_smul, one_smul, zero_add] using hx.2
    · intro hmem
      have heq : a • b + c • x = p := Set.mem_singleton_iff.mp hmem
      have hac' : 1 - c = a := by linarith
      have hmap := ell.toAffineMap.apply_lineMap b x c
      rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_ring, hac'] at hmap
      have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hpos : 0 < a * ell b := mul_pos ha' hbpositive
      have hnonneg : 0 ≤ c * ell x := mul_nonneg hc hx.1.2
      have hval : ell (a • b + c • x) = 0 := by rw [heq, hzero]
      change ell (a • b + c • x) = a * ell b + c * ell x at hmap
      linarith
  exact hstar.contractibleSpace ⟨b, hb⟩

end ContinuousAffineMap
