import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.ProperSpace











set_option autoImplicit false

open Set Metric unitInterval

namespace NormedSpace

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def unitSphereRadialMap : C(I × sphere (0 : E) 1, closedBall (0 : E) 1) := by
  refine ⟨fun z => ⟨(z.1 : ℝ) • (z.2 : E), ?_⟩, ?_⟩
  · rename_i z
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg z.1.property.1,
      norm_eq_of_mem_sphere z.2, mul_one]
    exact z.1.property.2
  · fun_prop



theorem norm_unitSphereRadialMap (z : I × sphere (0 : E) 1) :
    ‖(unitSphereRadialMap E z : E)‖ = (z.1 : ℝ) := by
  change ‖(z.1 : ℝ) • (z.2 : E)‖ = (z.1 : ℝ)
  rw [norm_smul, Real.norm_of_nonneg z.1.property.1, norm_eq_of_mem_sphere z.2, mul_one]




theorem unitSphereRadialMap_eq_iff (z w : I × sphere (0 : E) 1) :
    unitSphereRadialMap E z = unitSphereRadialMap E w ↔
      z.1 = w.1 ∧ (z.1 = 0 ∨ z.2 = w.2) := by
  constructor
  · intro h
    have ht : z.1 = w.1 := Subtype.ext (by
      simpa only [norm_unitSphereRadialMap] using
        congrArg (fun x : closedBall (0 : E) 1 => ‖(x : E)‖) h)
    refine ⟨ht, ?_⟩
    by_cases hz : z.1 = 0
    · exact Or.inl hz
    · apply Or.inr
      apply Subtype.ext
      have htz : (z.1 : ℝ) ≠ 0 := fun h => hz (Subtype.ext h)
      apply smul_right_injective E htz
      have hv := congrArg Subtype.val h
      change (z.1 : ℝ) • (z.2 : E) = (w.1 : ℝ) • (w.2 : E) at hv
      rwa [← ht] at hv
  · rintro ⟨ht, hz | hu⟩
    · apply Subtype.ext
      change (z.1 : ℝ) • (z.2 : E) = (w.1 : ℝ) • (w.2 : E)
      rw [← ht, hz]
      simp
    · exact congrArg (unitSphereRadialMap E) (Prod.ext ht hu)

variable [Nontrivial E]




theorem surjective_unitSphereRadialMap : Function.Surjective (unitSphereRadialMap E) := by
  intro x
  by_cases hx : (x : E) = 0
  · obtain ⟨u, hu⟩ := (sphere_nonempty (E := E) (x := 0) (r := 1)).mpr zero_le_one
    refine ⟨(0, ⟨u, hu⟩), Subtype.ext ?_⟩
    change (0 : ℝ) • u = (x : E)
    rw [zero_smul, hx]
  · have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let t : I := ⟨‖(x : E)‖, norm_nonneg _, by
      simpa only [mem_closedBall, dist_zero_right] using x.property⟩
    let u : sphere (0 : E) 1 := ⟨‖(x : E)‖⁻¹ • (x : E), by
      rw [mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]⟩
    refine ⟨(t, u), Subtype.ext ?_⟩
    change ‖(x : E)‖ • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

variable [ProperSpace E]




theorem isQuotientMap_unitSphereRadialMap : Topology.IsQuotientMap (unitSphereRadialMap E) :=
  Topology.IsQuotientMap.of_surjective_continuous (surjective_unitSphereRadialMap E)
    (unitSphereRadialMap E).continuous

end NormedSpace
