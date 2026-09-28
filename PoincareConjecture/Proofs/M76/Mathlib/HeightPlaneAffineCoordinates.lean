import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

open Set

namespace LinearMap

private theorem apply_three_coordinates (A : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ)
    (x : (ℝ × ℝ) × ℝ) :
    A x = A ((1, 0), 0) * x.1.1 + A ((0, 1), 0) * x.1.2 +
      A ((0, 0), 1) * x.2 := by
  have hx : x = x.1.1 • (((1, 0), 0) : (ℝ × ℝ) × ℝ) +
      x.1.2 • (((0, 1), 0) : (ℝ × ℝ) × ℝ) +
      x.2 • (((0, 0), 1) : (ℝ × ℝ) × ℝ) := by
    ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  change x.1.1 * A ((1, 0), 0) + x.1.2 * A ((0, 1), 0) +
    x.2 * A ((0, 0), 1) = _
  ring

private theorem exists_normalization_of_first_ne_zero
    (A : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ) (ha : A ((1, 0), 0) ≠ 0) :
    ∃ e : ((ℝ × ℝ) × ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × ℝ),
      (∀ x, A (e x) = x.1.1) ∧ ∀ x, (e x).2 = x.2 := by
  let a := A ((1, 0), 0)
  let b := A ((0, 1), 0)
  let c := A ((0, 0), 1)
  let X : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let Y : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let Z : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  let F := ((a⁻¹ • (X - b • Y - c • Z)).prod Y).prod Z
  let G := ((a • X + b • Y + c • Z).prod Y).prod Z
  have hF (x : (ℝ × ℝ) × ℝ) :
      F x = ((a⁻¹ * (x.1.1 - b * x.1.2 - c * x.2), x.1.2), x.2) := rfl
  have hG (x : (ℝ × ℝ) × ℝ) :
      G x = ((a * x.1.1 + b * x.1.2 + c * x.2, x.1.2), x.2) := rfl
  let e : ((ℝ × ℝ) × ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × ℝ) :=
    { F with
      invFun := G
      left_inv := by
        intro x
        change G (F x) = x
        rw [hG, hF]
        ext <;> dsimp
        field_simp [show a ≠ 0 from ha]
        <;> ring
      right_inv := by
        intro x
        change F (G x) = x
        rw [hF, hG]
        ext <;> dsimp
        field_simp [show a ≠ 0 from ha]
        <;> ring }
  refine ⟨e, ?_, fun _ => rfl⟩
  intro x
  rw [apply_three_coordinates]
  change a * (a⁻¹ * (x.1.1 - b * x.1.2 - c * x.2)) + b * x.1.2 + c * x.2 = x.1.1
  field_simp [show a ≠ 0 from ha]
  <;> ring

theorem exists_height_normalization_preserving_last
    (A : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ)
    (hA : ∃ x : (ℝ × ℝ) × ℝ, x.2 = 0 ∧ A x ≠ 0) :
    ∃ e : ((ℝ × ℝ) × ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × ℝ),
      (∀ x, A (e x) = x.1.1) ∧ ∀ x, (e x).2 = x.2 := by
  by_cases ha : A ((1, 0), 0) ≠ 0
  · exact exists_normalization_of_first_ne_zero A ha
  have ha0 : A ((1, 0), 0) = 0 := not_ne_iff.mp ha
  have hb : A ((0, 1), 0) ≠ 0 := by
    intro hb
    obtain ⟨x, hx, hAx⟩ := hA
    apply hAx
    rw [apply_three_coordinates, ha0, hb, hx]
    ring
  let S := (LinearEquiv.prodComm ℝ ℝ ℝ).prodCongr (LinearEquiv.refl ℝ ℝ)
  let B := A.comp S.toLinearMap
  have hB : B ((1, 0), 0) ≠ 0 := hb
  obtain ⟨e, he, hz⟩ := exists_normalization_of_first_ne_zero B hB
  exact ⟨e.trans S, he, hz⟩

end LinearMap

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_height_plane_coordinates (L : Submodule ℝ E)
    (hdim : Module.finrank ℝ E = 3) (hL : Module.finrank ℝ L = 2)
    (A : E →ₗ[ℝ] ℝ) (hA : ∃ v ∈ L, A v ≠ 0) :
    ∃ e : ((ℝ × ℝ) × ℝ) ≃L[ℝ] E,
      (∀ x, A (e x) = x.1.1) ∧ ∀ x, e x ∈ L ↔ x.2 = 0 := by
  classical
  obtain ⟨W, hLW⟩ := Submodule.exists_isCompl L
  have hW : Module.finrank ℝ W = 1 := by
    have h := Submodule.finrank_add_eq_of_isCompl hLW
    omega
  let eL : (ℝ × ℝ) ≃ₗ[ℝ] L := LinearEquiv.ofFinrankEq _ _ (by
    simp [Module.finrank_prod, hL])
  let eW : ℝ ≃ₗ[ℝ] W := LinearEquiv.ofFinrankEq _ _ (by simp [hW])
  let e0 := (eL.prodCongr eW).trans (L.prodEquivOfIsCompl W hLW)
  have he0 (x : (ℝ × ℝ) × ℝ) : e0 x ∈ L ↔ x.2 = 0 := by
    have h := (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero L W hLW
      (x := e0 x)).symm
    simpa only [e0, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply, eW.map_eq_zero_iff] using h
  let B := A.comp e0.toLinearMap
  have hB : ∃ x : (ℝ × ℝ) × ℝ, x.2 = 0 ∧ B x ≠ 0 := by
    obtain ⟨v, hv, hAv⟩ := hA
    refine ⟨e0.symm v, (he0 _).mp ?_, ?_⟩
    · simpa only [e0.apply_symm_apply] using hv
    · change A (e0 (e0.symm v)) ≠ 0
      simpa only [e0.apply_symm_apply] using hAv
  obtain ⟨e, he, hz⟩ := B.exists_height_normalization_preserving_last hB
  refine ⟨(e.trans e0).toContinuousLinearEquiv, he, ?_⟩
  intro x
  change e0 (e x) ∈ L ↔ x.2 = 0
  rw [he0, hz]

end Submodule

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_centered_height_plane_coordinates (P : AffineSubspace ℝ E)
    (hdim : Module.finrank ℝ E = 3) (hP : Module.finrank ℝ P.direction = 2)
    (A : E →ᵃ[ℝ] ℝ) (hA : ∃ u ∈ P, ∃ v ∈ P, A u ≠ A v)
    {p : E} (hp : p ∈ P) :
    ∃ f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E,
      f 0 = p ∧ (∀ x, A (f x) = A p + x.1.1) ∧
      ∀ x, f x ∈ P ↔ x.2 = 0 := by
  have hdir : ∃ v ∈ P.direction, A.linear v ≠ 0 := by
    obtain ⟨u, hu, v, hv, huv⟩ := hA
    refine ⟨u - v, P.vsub_mem_direction hu hv, ?_⟩
    have h := A.linearMap_vsub u v
    change A.linear (u - v) = A u - A v at h
    rw [h]
    exact sub_ne_zero.mpr huv
  obtain ⟨e, he, hplane⟩ := P.direction.exists_height_plane_coordinates hdim hP A.linear hdir
  let f := e.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ E p)
  have hf (x : (ℝ × ℝ) × ℝ) : f x = e x + p := add_comm _ _
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [hf, map_zero, zero_add]
  · intro x
    rw [hf]
    change A (e x +ᵥ p) = A p + x.1.1
    rw [A.map_vadd, he, add_comm]
    rfl
  · intro x
    rw [hf]
    change e x +ᵥ p ∈ P ↔ x.2 = 0
    rw [P.vadd_mem_iff_mem_direction _ hp, hplane]

end AffineSubspace
