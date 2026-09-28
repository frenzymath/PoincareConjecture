import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Connected












set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem isPathConnected_compl_closedBall_of_one_lt_rank (hdim : 1 < Module.rank ℝ E)
    (c : E) (r : ℝ) : IsPathConnected (closedBall c r)ᶜ := by
  rcases le_or_gt 0 r with hr | hr
  · let f : E × ℝ → E := fun p => c + p.2 • p.1
    have hprod : IsPathConnected (sphere (0 : E) 1 ×ˢ Ioi r) :=
      (isPathConnected_sphere hdim 0 zero_le_one).prod
        ((convex_Ioi r).isPathConnected nonempty_Ioi)
    have himage : f '' (sphere (0 : E) 1 ×ˢ Ioi r) = (closedBall c r)ᶜ := by
      apply subset_antisymm
      · rintro _ ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
        have hunit : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
        have htpos : 0 < t := hr.trans_lt ht
        simpa [f, mem_closedBall, dist_eq_norm, norm_smul, hunit, abs_of_pos htpos]
          using ht
      · intro x hx
        have ht : r < ‖x - c‖ := by
          simpa only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] using hx
        have htpos : 0 < ‖x - c‖ := hr.trans_lt ht
        refine ⟨(‖x - c‖⁻¹ • (x - c), ‖x - c‖), ⟨?_, ht⟩, ?_⟩
        · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr htpos), inv_mul_cancel₀ htpos.ne']
        · change c + ‖x - c‖ • (‖x - c‖⁻¹ • (x - c)) = x
          rw [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
          abel
    rw [← himage]
    exact hprod.image (continuous_const.add (continuous_snd.smul continuous_fst))
  · rw [closedBall_eq_empty.mpr hr, compl_empty]
    exact (convex_univ : Convex ℝ (univ : Set E)).isPathConnected ⟨0, mem_univ 0⟩



theorem isPathConnected_compl_closure_of_convex (hdim : 1 < Module.rank ℝ E)
    {s : Set E} (hc : Convex ℝ s) (hne : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) : IsPathConnected (closure s)ᶜ := by
  obtain ⟨h, _, hclosure, _⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hb
  apply h.isPathConnected_image.mp
  rw [h.image_compl, hclosure]
  exact isPathConnected_compl_closedBall_of_one_lt_rank hdim 0 1

end Poincare.Manifold.Schoenflies.Plane
