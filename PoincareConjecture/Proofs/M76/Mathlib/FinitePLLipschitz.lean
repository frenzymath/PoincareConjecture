import PoincareConjecture.Proofs.M76.Mathlib.FiniteClosedCoverLipschitz
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine

set_option autoImplicit false

open Set Geometry
open scoped NNReal BigOperators

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem AffineOnFaces.exists_lipschitzOnWith {K : SimplicialComplex ℝ E} {f : E → F}
    (hf : K.AffineOnFaces f) (hK : K.faces.Finite) (hcv : Convex ℝ K.space) :
    ∃ L : ℝ≥0, LipschitzOnWith L f K.space := by
  classical
  let := hK.fintype
  choose a ha using fun s : K.faces => hf s.val s.property
  let L : ℝ≥0 := ∑ s : K.faces, ‖(a s).contLinear‖₊
  refine ⟨L, hcv.lipschitzOnWith_of_finite_closed_cover (hf.continuousOn hK)
    (fun s : K.faces => convexHull ℝ (s.val : Set E))
    (fun s => s.val.finite_toSet.isClosed_convexHull ℝ) ?_ ?_⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hxs⟩
  · intro s
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [ha s hx.2, ha s hy.2, dist_eq_norm, dist_eq_norm]
    have heq : (a s).contLinear (x - y) = a s x - a s y :=
      (a s).contLinear_map_vsub x y
    rw [← heq]
    have hL : ‖(a s).contLinear‖ ≤ (L : ℝ) := by
      have hL' : ‖(a s).contLinear‖₊ ≤ L :=
        Finset.single_le_sum (f := fun i : K.faces => ‖(a i).contLinear‖₊)
          (fun _ _ => bot_le) (Finset.mem_univ s)
      exact_mod_cast hL'
    exact ((a s).contLinear.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

end Geometry.SimplicialComplex

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FinitePiecewiseAffineOn.exists_lipschitzOnWith {f : E → F} {s : Set E}
    (hf : FinitePiecewiseAffineOn f s) (hcv : Convex ℝ s) :
    ∃ L : ℝ≥0, LipschitzOnWith L f s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact hfaces.exists_lipschitzOnWith hK hcv

end Geometry
