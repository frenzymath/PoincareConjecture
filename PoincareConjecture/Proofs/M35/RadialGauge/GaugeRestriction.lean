import PoincareConjecture.Proofs.M35.RadialGauge.SmoothEuclideanGauge
import PoincareConjecture.Proofs.M35.RadialGauge.RadialSymmetry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Manifold

namespace PoincareConjecture.M35.RadialGauge

variable {m n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin m)
local notation "W" => EuclideanSpace ℝ (Fin n)

theorem orthogonal_invariant_eq_of_norm_eq {u : V → ℝ}
    (hu : ∀ (L : V ≃ₗᵢ[ℝ] V) x, u (L x) = u x) {x y : V}
    (hxy : ‖x‖ = ‖y‖) : u x = u y := by
  have h := hu (Submodule.reflection (ℝ ∙ (x - y))ᗮ) x
  rw [Submodule.reflection_sub hxy] at h
  exact h.symm

theorem orthogonal_invariant_restrict (I : V →ₗᵢ[ℝ] W) {u : W → ℝ}
    (hu : ∀ (L : W ≃ₗᵢ[ℝ] W) x, u (L x) = u x)
    (L : V ≃ₗᵢ[ℝ] V) (x : V) : u (I (L x)) = u (I x) :=
  orthogonal_invariant_eq_of_norm_eq hu (by simp only [I.norm_map, L.norm_map])

theorem norm_iteratedFDeriv_restrict_le (I : V →ₗᵢ[ℝ] W)
    {u : W → ℝ} (hu : ContDiff ℝ ∞ u) (j : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ j (fun y => u (I y)) x‖ ≤ ‖iteratedFDeriv ℝ j u (I x)‖ := by
  have h := I.toContinuousLinearMap.iteratedFDeriv_comp_right hu x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  change iteratedFDeriv ℝ j (fun y => u (I y)) x = _ at h
  rw [h]
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  change ‖iteratedFDeriv ℝ j u (I x) (fun i => I (v i))‖ ≤ _
  simpa only [I.norm_map] using (iteratedFDeriv ℝ j u (I x)).le_opNorm (fun i => I (v i))

theorem weighted_c1_restrict (I : V →ₗᵢ[ℝ] W) {u : W → ℝ} {eta : ℝ}
    (hu : ContDiff ℝ ∞ u)
    (hv : ∀ x, (1 + ‖x‖) * |u x| ≤ eta)
    (hd : ∀ x, (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ eta) (x : V) :
    (1 + ‖x‖) * |u (I x)| ≤ eta ∧
      (1 + ‖x‖) * ‖fderiv ℝ (fun y => u (I y)) x‖ ≤ eta := by
  constructor
  · simpa only [I.norm_map] using hv (I x)
  · have h := norm_iteratedFDeriv_restrict_le I hu 1 x
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at h
    have hi := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1 + ‖x‖)
    exact hi.trans (by simpa only [I.norm_map] using hd (I x))

noncomputable def threeIntoFive :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 5) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let c := EuclideanSpace.basisFun (Fin 5) ℝ
  let ι : Fin 3 → Fin 5 := Fin.castLE (by norm_num)
  let f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 5) :=
    b.toBasis.constr ℝ (fun i => c (ι i))
  have hb : Orthonormal ℝ b.toBasis := by
    simpa only [OrthonormalBasis.coe_toBasis] using b.orthonormal
  refine f.isometryOfOrthonormal (v := b.toBasis) hb ?_
  have hc := c.orthonormal.comp ι (Fin.castLE_injective _)
  have heq : f ∘ b.toBasis = c ∘ ι :=
    funext (fun i => b.toBasis.constr_basis ℝ (fun i => c (ι i)) i)
  rw [heq]
  exact hc

theorem exists_three_dimensional_gauge
    {u : EuclideanSpace ℝ (Fin 5) → ℝ} (hu : ContDiff ℝ ∞ u)
    (hv : ∀ x, (1 + ‖x‖) * |u x| ≤ 1 / 8)
    (hd : ∀ x, (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ 1 / 8) :
    ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞,
      ∀ x, Φ x = Real.exp (u (threeIntoFive x)) • x := by
  have hs : ContDiff ℝ ∞ (fun x => u (threeIntoFive x)) :=
    hu.comp threeIntoFive.toContinuousLinearMap.contDiff
  obtain ⟨Φ, hΦ⟩ := exists_euclideanGauge_diffeomorph (n := 2) hs
    (fun x => (weighted_c1_restrict threeIntoFive hu hv hd x).1)
    (fun x => (weighted_c1_restrict threeIntoFive hu hv hd x).2)
  exact ⟨Φ, fun x => congrFun hΦ x⟩

end PoincareConjecture.M35.RadialGauge
