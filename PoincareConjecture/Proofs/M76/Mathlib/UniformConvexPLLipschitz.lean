import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLipschitz

set_option autoImplicit false

open Set Geometry
open scoped NNReal BigOperators

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem AffineOnFaces.exists_uniform_convex_lipschitzOnWith
    {K : SimplicialComplex ℝ E} {f : E → F}
    (hf : K.AffineOnFaces f) (hK : K.faces.Finite) :
    ∃ L : ℝ≥0, ∀ s : Set E, s ⊆ K.space → Convex ℝ s → LipschitzOnWith L f s := by
  classical
  let := hK.fintype
  choose a ha using fun s : K.faces => hf s.val s.property
  let L : ℝ≥0 := ∑ s : K.faces, ‖(a s).contLinear‖₊
  refine ⟨L, fun s hs hcv => hcv.lipschitzOnWith_of_finite_closed_cover
    ((hf.continuousOn hK).mono hs) (fun r : K.faces => convexHull ℝ (r.val : Set E))
    (fun r => r.val.finite_toSet.isClosed_convexHull ℝ) ?_ ?_⟩
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := mem_space_iff.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨r, hr⟩, hxr⟩
  · intro r
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [ha r hx.2, ha r hy.2, dist_eq_norm, dist_eq_norm]
    have heq : (a r).contLinear (x - y) = a r x - a r y :=
      (a r).contLinear_map_vsub x y
    rw [← heq]
    have hL : ‖(a r).contLinear‖ ≤ (L : ℝ) := by
      have hsum : ‖(a r).contLinear‖₊ ≤ L :=
        Finset.single_le_sum (f := fun i : K.faces => ‖(a i).contLinear‖₊)
          (fun _ _ => bot_le) (Finset.mem_univ r)
      exact_mod_cast hsum
    exact ((a r).contLinear.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

end Geometry.SimplicialComplex

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FinitePiecewiseAffineOn.exists_uniform_convex_lipschitzOnWith
    {f : E → F} {S : Set E} (hf : FinitePiecewiseAffineOn f S) :
    ∃ L : ℝ≥0, ∀ s : Set E, s ⊆ S → Convex ℝ s → LipschitzOnWith L f s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact hfaces.exists_uniform_convex_lipschitzOnWith hK

theorem FinitePiecewiseAffineOn.exists_uniform_vertical_lipschitzOnWith
    {f : E × ℝ → F} {B : Set E} {α β : ℝ}
    (hf : FinitePiecewiseAffineOn f (B ×ˢ Icc α β)) :
    ∃ L : ℝ≥0, ∀ x ∈ B, LipschitzOnWith L (fun t => f (x, t)) (Icc α β) := by
  obtain ⟨L, hL⟩ := hf.exists_uniform_convex_lipschitzOnWith
  refine ⟨L, fun x hx => LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_⟩
  have hsubset : ({x} ×ˢ Icc α β : Set (E × ℝ)) ⊆ B ×ˢ Icc α β :=
    prod_mono (singleton_subset_iff.mpr hx) subset_rfl
  have h := (hL ({x} ×ˢ Icc α β) hsubset
    ((convex_singleton x).prod (convex_Icc α β))).dist_le_mul
      (x, u) ⟨mem_singleton x, hu⟩ (x, v) ⟨mem_singleton x, hv⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist u v)] using h

end Geometry
