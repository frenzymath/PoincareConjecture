import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedReaction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.QuadraticHeat
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

section Array

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma perturbed_hamiltonBlock_vector_contraction
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ)
    (M U : I → I → ℝ) (W : I → ℝ) (α ψ : ℝ)
    (hU : ∀ a b, U a b = -U b a)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2 +
        ψ * twoFormIdentity ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c)
      (fun a b => M a b + α * (if a = b then 1 else 0))).PosSemidef)
    (hnull : (∑ a, ∑ b, M a b * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d) +
      α * (∑ a, (W a) ^ 2) + ψ * (∑ a, ∑ b, (U a b) ^ 2) = 0) :
    (∑ a, ∑ b, M a b * W a * W b) +
      (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) = -α * ∑ a, (W a) ^ 2 := by
  have hM : (∑ a, ∑ b, (M a b + α * (if a = b then 1 else 0)) * W a * W b) =
      (∑ a, ∑ b, M a b * W a * W b) + α * (∑ a, (W a) ^ 2) := by
    simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, mul_assoc, pow_two]
  have hR : (∑ a, ∑ b, ∑ c, ∑ d,
      (R a b c d + ψ * twoFormIdentity a b c d) * U a b * U c d) =
      (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d) +
        ψ * (∑ a, ∑ b, (U a b) ^ 2) := by
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    congr 1
    exact congrArg (fun z : ℝ => ψ * z)
      (by simpa only [mul_assoc] using twoFormIdentity_quadratic U hU)
  have hnull' :
      (∑ a, ∑ b, (M a b + α * (if a = b then 1 else 0)) * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d,
        (R a b c d + ψ * twoFormIdentity a b c d) * U a b * U c d) = 0 := by
    rw [hM, hR]
    linarith only [hnull]
  have hz := hamiltonBlock_vector_contraction_zero
    (fun a b c d => R a b c d + ψ * twoFormIdentity a b c d) P
    (fun a b => M a b + α * (if a = b then 1 else 0)) U W hQ hnull'
  rw [hM] at hz
  linarith only [hz]

end Array

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

noncomputable def hamiltonHeatJetQuadratic
    (F : RicciFlow n M J) (T₀ t : ℝ) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) : ℝ :=
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let Ric := fun a c => D.ricci x (b a) (b c)
  let k := (2 * (t - T₀))⁻¹
  let V := fun e a c =>
    ((Ric e a + k * (if e = a then 1 else 0)) * W c -
      W a * (Ric e c + k * (if e = c then 1 else 0))) / 2
  (∑ a, ∑ c, F.tensorHeatOperator (fun s y z =>
    hamiltonM (F.connection s) (s - T₀) y (z 0) (z 1)) t x ![b a, b c] * W a * W c) +
    2 * (∑ a, ∑ c, ∑ d,
      F.tensorHeatOperator (fun s y z => hamiltonP (F.connection s) y
        (z 0) (z 1) (z 2)) t x ![b a, b c, b d] * U a c * W d) +
    (∑ a, ∑ c, ∑ d, ∑ e,
      F.tensorHeatOperator (fun s => (F.connection s).riemannEvaluation)
        t x ![b a, b c, b d, b e] * U a c * U d e) -
    4 * (∑ e, ∑ a, ∑ c, ∑ d,
      D.covariantTensorDerivative (fun y z => hamiltonP D y (z 0) (z 1) (z 2))
        x ![b e, b a, b c, b d] * V e a c * W d) -
    4 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
      D.covariantTensorDerivative D.riemannEvaluation x ![b e, b a, b c, b d, b f] *
        V e a c * U d f) -
    2 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
      D.curvatureTensor x (b a) (b c) (b d) (b f) * V e a c * V e d f)

lemma hamiltonHeatJetQuadratic_eq_reaction
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
    let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
    let Q := fun a c => hamiltonM D (t - T₀) x (b a) (b c)
    hamiltonHeatJetQuadratic F T₀ t x U W + 4 * (2 * (t - T₀))⁻¹ *
      ((∑ a, ∑ c, Q a c * W a * W c) +
        (∑ a, ∑ c, ∑ d, P a c d * U a c * W d)) =
      hamiltonCollectedReaction R P Q U W := by
  have hm := hamiltonM_heat_quadratic_cancellation hC F T₀ ht hτ x W
  have hp := hamiltonP_heat_quadratic_cancellation hC F ht ((2 * (t - T₀))⁻¹) x U W
  dsimp only [hamiltonHeatJetQuadratic, hamiltonCollectedReaction] at hm hp ⊢
  simp_rw [F.tensorHeatOperator_riemann hC ht]
  simp only [LeviCivitaData.curvatureB, mul_assoc, ← Finset.mul_sum] at hm hp ⊢
  linarith only [hm, hp]

lemma hamiltonHeatJetQuadratic_ge_perturbed_null
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (α ψ KR KP KM : ℝ) (hα : 0 ≤ α) (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1)
    (hKR : 0 ≤ KR) (hKP : 0 ≤ KP) (hKM : 0 ≤ KM)
    (hU : ∀ a c, U a c = -U c a) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
    let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
    let Q := fun a c => hamiltonM D (t - T₀) x (b a) (b c)
    (∀ a c d e, |R a c d e| ≤ KR) →
    (∀ a c d, |P a c d| ≤ KP) → (∀ a c, |Q a c| ≤ KM) →
    (Matrix.fromBlocks
      (fun ac df : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        R ac.1 ac.2 df.1 df.2 + ψ * twoFormIdentity ac.1 ac.2 df.1 df.2)
      (fun ac d => P ac.1 ac.2 d) (fun a cd => P cd.1 cd.2 a)
      (fun a c => Q a c + α * (if a = c then 1 else 0))).PosSemidef →
    (∑ a, ∑ c, Q a c * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d, P a c d * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e, R a c d e * U a c * U d e) +
      α * (∑ a, (W a) ^ 2) + ψ * (∑ a, ∑ c, (U a c) ^ 2) = 0 →
    -(2 * (n : ℝ) ^ 3 * (KR + 1) * α * (∑ a, (W a) ^ 2) +
      (2 * (n : ℝ) ^ 3 * KM + 6 * (n : ℝ) ^ 4 * KP ^ 2) * ψ * (∑ a, (W a) ^ 2) +
      (6 * (n : ℝ) ^ 3 + 8 * (n : ℝ) ^ 4 * (2 * KR + 1)) * ψ *
        (∑ a, ∑ c, (U a c) ^ 2)) +
      4 * (2 * (t - T₀))⁻¹ * α * (∑ a, (W a) ^ 2) ≤
        hamiltonHeatJetQuadratic F T₀ t x U W := by
  dsimp only
  intro hR hPb hM hQ hnull
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
  let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
  let Q := fun a c => hamiltonM D (t - T₀) x (b a) (b c)
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hfirst (a c d e) : R a c d e = -R c a d e := by
    dsimp only [R]
    rw [(hD.2.2.2.1 x _ _ _ _).2.1, (hD.2.2.2.1 x _ _ _ _).1,
      (hD.2.2.2.1 x _ _ _ _).2.1]
  have hlast (a c d e) : R a c d e = -R a c e d := (hD.2.2.2.1 x _ _ _ _).1
  have hpair (a c d e) : R a c d e = R d e a c := (hD.2.2.2.1 x _ _ _ _).2.1
  have hbianchi (a c d e) : R a c d e + R c d a e + R d a c e = 0 :=
    (hD.2.2.2.1 x _ _ _ _).2.2.1
  have hP (a c d) : P a c d = -P c a d := hamiltonP_skew D x _ _ _
  have hr := hamiltonCollectedReaction_ge_neg_replacement_error R P Q U W
    α ψ KR KP KM hα hψ hψone hKR hKP hKM hR hPb hM
    hfirst hlast hpair hbianchi hP hU hQ
  have hz := perturbed_hamiltonBlock_vector_contraction R P Q U W α ψ hU hQ hnull
  have he := hamiltonHeatJetQuadratic_eq_reaction hC F T₀ ht hτ x U W
  have hz' := congrArg (fun z : ℝ => 4 * (2 * (t - T₀))⁻¹ * z) hz
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  simp only [Fintype.card_fin, hdim] at hr
  change hamiltonHeatJetQuadratic F T₀ t x U W + 4 * (2 * (t - T₀))⁻¹ *
    ((∑ a, ∑ c, Q a c * W a * W c) +
      (∑ a, ∑ c, ∑ d, P a c d * U a c * W d)) =
      hamiltonCollectedReaction R P Q U W at he
  linarith only [hr, he, hz']

lemma abs_hamiltonM_le_curvatureDerivativeNorm
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {τ : ℝ} (hτ : 0 < τ) (x : M) (a b : TangentSpace (𝓡 n) x) :
    |hamiltonM D τ x a b| ≤
      (2 * (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x +
        3 * (n : ℝ) ^ 3 * (D.curvatureDerivativeNorm 0 x) ^ 2 +
        n * D.curvatureDerivativeNorm 0 x / (2 * τ)) *
          g.tangentNorm x a * g.tangentNorm x b := by
  have hm := abs_hamiltonM_sub_ricci_le_curvatureDerivativeNorm D hD τ x a b
  have hr := D.abs_ricci_le_curvatureDerivativeNorm_zero hD x a b
  have hrd := div_le_div_of_nonneg_right hr (show 0 ≤ 2 * τ by positivity)
  have he := abs_add_le (hamiltonM D τ x a b - D.ricci x a b / (2 * τ))
    (D.ricci x a b / (2 * τ))
  simp only [sub_add_cancel, abs_div, abs_of_pos (show 0 < 2 * τ by positivity)] at he
  calc
    _ ≤ _ := he.trans (add_le_add hm hrd)
    _ = _ := by ring

lemma hamiltonHeatJetQuadratic_ge_perturbed_null_of_curvature
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : 0 < t - T₀) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (α ψ : ℝ) (hα : 0 ≤ α) (hψ : 0 ≤ ψ) (hψone : ψ ≤ 1)
    (hU : ∀ a c, U a c = -U c a) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
    let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
    let Q := fun a c => hamiltonM D (t - T₀) x (b a) (b c)
    let KR := D.curvatureDerivativeNorm 0 x
    let KP := 2 * n * D.curvatureDerivativeNorm 1 x
    let KM := 2 * (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x +
      3 * (n : ℝ) ^ 3 * (D.curvatureDerivativeNorm 0 x) ^ 2 +
      n * D.curvatureDerivativeNorm 0 x / (2 * (t - T₀))
    (Matrix.fromBlocks
      (fun ac df : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        R ac.1 ac.2 df.1 df.2 + ψ * twoFormIdentity ac.1 ac.2 df.1 df.2)
      (fun ac d => P ac.1 ac.2 d) (fun a cd => P cd.1 cd.2 a)
      (fun a c => Q a c + α * (if a = c then 1 else 0))).PosSemidef →
    (∑ a, ∑ c, Q a c * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d, P a c d * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e, R a c d e * U a c * U d e) +
      α * (∑ a, (W a) ^ 2) + ψ * (∑ a, ∑ c, (U a c) ^ 2) = 0 →
    -(2 * (n : ℝ) ^ 3 * (KR + 1) * α * (∑ a, (W a) ^ 2) +
      (2 * (n : ℝ) ^ 3 * KM + 6 * (n : ℝ) ^ 4 * KP ^ 2) * ψ * (∑ a, (W a) ^ 2) +
      (6 * (n : ℝ) ^ 3 + 8 * (n : ℝ) ^ 4 * (2 * KR + 1)) * ψ *
        (∑ a, ∑ c, (U a c) ^ 2)) +
      4 * (2 * (t - T₀))⁻¹ * α * (∑ a, (W a) ^ 2) ≤
        hamiltonHeatJetQuadratic F T₀ t x U W := by
  dsimp only
  intro hQ hnull
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hn (j : ℕ) : 0 ≤ D.curvatureDerivativeNorm j x := Real.sqrt_nonneg _
  have hn₁ := hn 1
  have hn₂ := hn 2
  have hn₀ := hn 0
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      (F.metric t).tangentNorm x (b i) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    change Real.sqrt (inner ℝ (b i) (b i)) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  apply hamiltonHeatJetQuadratic_ge_perturbed_null hC F T₀ ht (ne_of_gt hτ) x U W
    α ψ (D.curvatureDerivativeNorm 0 x) (2 * n * D.curvatureDerivativeNorm 1 x)
    (2 * (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x +
      3 * (n : ℝ) ^ 3 * (D.curvatureDerivativeNorm 0 x) ^ 2 +
      n * D.curvatureDerivativeNorm 0 x / (2 * (t - T₀)))
    hα hψ hψone (hn 0) (by positivity) (by positivity) hU
  · intro a c d e
    simpa only [hb, mul_one] using
      D.abs_curvatureTensor_le_curvatureDerivativeNorm_zero hD x (b a) (b c) (b d) (b e)
  · intro a c d
    simpa only [hb, mul_one] using abs_hamiltonP_le_curvatureDerivativeNorm D hD x (b a) (b c) (b d)
  · intro a c
    simpa only [hb, mul_one] using abs_hamiltonM_le_curvatureDerivativeNorm D hD hτ x (b a) (b c)
  · exact hQ
  · exact hnull

end Poincare.RicciFlow.Harnack
