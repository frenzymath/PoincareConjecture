import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection

set_option autoImplicit false

open Module

namespace ContinuousAffineEquiv

theorem exists_normalized_edge_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 3)
    (p q : E) (hpq : p ≠ q) :
    ∃ F : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E,
      ∀ t : ℝ, F ((0, 0), t) = AffineMap.lineMap p q t := by
  classical
  have hv : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  let Q : Submodule ℝ E := ℝ ∙ (q - p)
  let eQ : ℝ ≃ₗ[ℝ] Q := LinearEquiv.toSpanNonzeroSingleton ℝ E (q - p) hv
  have hQ : finrank ℝ Q = 1 := by simpa using eQ.symm.finrank_eq
  obtain ⟨P, hQP⟩ := Q.exists_isCompl
  let L := P.prodEquivOfIsCompl Q hQP.symm
  have hP : finrank ℝ P = 2 := by
    have hd := L.finrank_eq
    rw [finrank_prod, hQ, hdim] at hd
    omega
  let eP : (ℝ × ℝ) ≃ₗ[ℝ] P := LinearEquiv.ofFinrankEq _ _ (by
    simp [finrank_prod, hP])
  let e := (eP.prodCongr eQ).trans L
  have he (t : ℝ) : e ((0, 0), t) = t • (q - p) := by
    change (↑(eP 0) : E) + ↑(eQ t) = _
    simp only [map_zero, Submodule.coe_zero, zero_add]
    rfl
  let F := e.toAffineEquiv.toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ E p)
  have hF (z : (ℝ × ℝ) × ℝ) : F z = e z + p := add_comm _ _
  exact ⟨F, fun t => by rw [hF, he, AffineMap.lineMap_apply_module']⟩

end ContinuousAffineEquiv
