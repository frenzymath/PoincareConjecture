import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.Quadratic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.QuadraticReaction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.M
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Finite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

lemma hamiltonP_heat_quadratic_cancellation
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (k : ℝ) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
    let Ric := fun a c => D.ricci x (b a) (b c)
    let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
    let V := fun e a c =>
      ((Ric e a + k * (if e = a then 1 else 0)) * W c -
        W a * (Ric e c + k * (if e = c then 1 else 0))) / 2
    2 * (∑ a, ∑ c, ∑ d,
      F.tensorHeatOperator (fun s y z => hamiltonP (F.connection s) y
        (z 0) (z 1) (z 2)) t x ![b a, b c, b d] * U a c * W d) +
      4 * k * (∑ a, ∑ c, ∑ d, P a c d * U a c * W d) -
      4 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
        D.covariantTensorDerivative D.riemannEvaluation x ![b e, b a, b c, b d, b f] *
          V e a c * U d f) =
      4 * (∑ a, ∑ c, ∑ d, ∑ e, ∑ f,
        (R a e c f * P e f d + R a e d f * P e c f + R c e d f * P a e f) *
          U a c * W d) := by
  have hc := hamiltonP_geometric_prescribed_jet_cancellation (F.connection t)
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) k x U W
  dsimp only at hc ⊢
  rw [tensorHeatOperator_hamiltonP hC F ht]
  simp only [hamiltonPReaction, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc, ← Finset.mul_sum] at hc ⊢
  linarith only [hc]

lemma hamiltonM_heat_quadratic_cancellation
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0) (x : M)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
    let Ric := fun a c => D.ricci x (b a) (b c)
    let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
    let Q := fun a c => hamiltonM D (t - T₀) x (b a) (b c)
    let dP := fun e a c d => D.covariantTensorDerivative
      (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![b e, b a, b c, b d]
    let k := (2 * (t - T₀))⁻¹
    let V := fun e a c =>
      ((Ric e a + k * (if e = a then 1 else 0)) * W c -
        W a * (Ric e c + k * (if e = c then 1 else 0))) / 2
    (∑ a, ∑ c, F.tensorHeatOperator (fun s y z =>
      hamiltonM (F.connection s) (s - T₀) y (z 0) (z 1)) t x ![b a, b c] * W a * W c) +
      4 * k * (∑ a, ∑ c, Q a c * W a * W c) -
      4 * (∑ e, ∑ a, ∑ c, ∑ d, dP e a c d * V e a c * W d) -
      2 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f, R a c d f * V e a c * V e d f) =
      2 * (∑ a, ∑ c, ∑ b, ∑ d, R a c b d * Q c d * W a * W b) -
      2 * (∑ a, ∑ c, ∑ d, ∑ b, P a c d * P b d c * W a * W b) +
      (∑ a, ∑ b, ∑ c, ∑ d, P c d a * P c d b * W a * W b) := by
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
  let Ric := fun a c => D.ricci x (b a) (b c)
  let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
  let Q := fun a c => hamiltonM D (t - T₀) x (b a) (b c)
  let dP := fun e a c d => D.covariantTensorDerivative
    (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![b e, b a, b c, b d]
  have hc := hamiltonM_geometric_prescribed_jet_cancellation D
    (hC.tensor_calculus n M (F.metric t) D) (t - T₀) x W
  have hheat := congrArg (fun A : I → I → ℝ => ∑ a, ∑ c, A a c * W a * W c)
    (funext fun a => funext fun c =>
      tensorHeatOperator_hamiltonM hC F T₀ ht hτ x (b a) (b c))
  have hderiv :
      (∑ a, ∑ b, ∑ c, ∑ d, Ric c d * (dP c d a b + dP c d b a) * W a * W b) =
      ∑ e, ∑ a, ∑ c, ∑ d, Ric e a * (dP e a c d + dP e a d c) * W c * W d := by
    let σ : (I × I × I × I) ≃ (I × I × I × I) :=
      { toFun := fun (a, b, c, d) => (c, d, a, b)
        invFun := fun (a, b, c, d) => (c, d, a, b)
        left_inv := by rintro ⟨a, b, c, d⟩; rfl
        right_inv := by rintro ⟨a, b, c, d⟩; rfl }
    have he := Fintype.sum_equiv σ
      (fun (a, b, c, d) => Ric c d * (dP c d a b + dP c d b a) * W a * W b)
      (fun (e, a, c, d) => Ric e a * (dP e a c d + dP e a d c) * W c * W d)
      (by rintro ⟨a, b, c, d⟩; rfl)
    simpa only [Fintype.sum_prod_type] using he
  have hcube :
      (∑ a, ∑ b, ∑ e, ∑ c, ∑ d, Ric e c * Ric e d * R a d b c * W a * W b) =
      ∑ e, ∑ a, ∑ c, ∑ d, ∑ f, R a c d f * Ric e a * W c * Ric e d * W f := by
    let σ : (I × I × I × I × I) ≃ (I × I × I × I × I) :=
      { toFun := fun (a, b, e, c, d) => (e, d, a, c, b)
        invFun := fun (e, a, c, d, f) => (c, f, e, d, a)
        left_inv := by rintro ⟨a, b, e, c, d⟩; rfl
        right_inv := by rintro ⟨e, a, c, d, f⟩; rfl }
    have hswap (a c d f) : R a c d f = R c a f d := by
      have hs := (hC.tensor_calculus n M (F.metric t) D).2.2.2.1
      dsimp only [R]
      rw [(hs x _ _ _ _).2.1, (hs x _ _ _ _).1,
        (hs x _ _ _ _).2.1, (hs x _ _ _ _).1, neg_neg]
    have he := Fintype.sum_equiv σ
      (fun (a, b, e, c, d) => Ric e c * Ric e d * R a d b c * W a * W b)
      (fun (e, a, c, d, f) => R a c d f * Ric e a * W c * Ric e d * W f)
      (by rintro ⟨a, b, e, c, d⟩; dsimp [σ]; rw [hswap a d b c]; ring)
    simpa only [Fintype.sum_prod_type] using he
  have hlinear :
      (∑ a, ∑ b, ∑ c, ∑ d, R a c b d * Q c d * W a * W b) =
      ∑ a, ∑ c, ∑ b, ∑ d, R a c b d * Q c d * W a * W b := by
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hnegative :
      (∑ a, ∑ b, ∑ c, ∑ d, P a c d * P b d c * W a * W b) =
      ∑ a, ∑ c, ∑ d, ∑ b, P a c d * P b d c * W a * W b := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    exact Finset.sum_comm
  have htime : (2 * (t - T₀) ^ 2)⁻¹ = 2 * ((2 * (t - T₀))⁻¹) ^ 2 := by
    field_simp
  have htime_term (r w v : ℝ) : r / (2 * (t - T₀) ^ 2) * w * v =
      2 * ((2 * (t - T₀))⁻¹) ^ 2 * (r * w * v) := by
    rw [div_eq_mul_inv, htime]
    ring
  dsimp only [D, b, R, Ric, P, Q, dP] at hderiv hcube hlinear hnegative hc hheat
  dsimp only at hc hheat ⊢
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    htime_term, ← Finset.mul_sum] at hheat
  simp only [div_eq_mul_inv, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_mul, mul_assoc, ← Finset.mul_sum]
      at hc hheat hderiv hcube hlinear hnegative ⊢
  linarith only [hc, hheat, hderiv, hcube, hlinear, hnegative]

lemma hamilton_heat_quadratic_nonneg_of_block
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Set.Ioo T₀ T₁)) {t : ℝ} (ht : t ∈ Set.Ioo T₀ T₁) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a) (hQ : HamiltonBlockPos F t x (t - T₀)) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
    let Ric := fun a c => D.ricci x (b a) (b c)
    let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
    let Q := fun a c => hamiltonM D (t - T₀) x (b a) (b c)
    let dP := fun e a c d => D.covariantTensorDerivative
      (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![b e, b a, b c, b d]
    let k := (2 * (t - T₀))⁻¹
    let V := fun e a c =>
      ((Ric e a + k * (if e = a then 1 else 0)) * W c -
        W a * (Ric e c + k * (if e = c then 1 else 0))) / 2
    0 ≤ (∑ a, ∑ c, F.tensorHeatOperator (fun s y z =>
      hamiltonM (F.connection s) (s - T₀) y (z 0) (z 1)) t x ![b a, b c] * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d,
        F.tensorHeatOperator (fun s y z => hamiltonP (F.connection s) y
          (z 0) (z 1) (z 2)) t x ![b a, b c, b d] * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e,
        F.tensorHeatOperator (fun s => (F.connection s).riemannEvaluation)
          t x ![b a, b c, b d, b e] * U a c * U d e) +
      4 * k * ((∑ a, ∑ c, Q a c * W a * W c) +
        (∑ a, ∑ c, ∑ d, P a c d * U a c * W d)) -
      4 * (∑ e, ∑ a, ∑ c, ∑ d, dP e a c d * V e a c * W d) -
      4 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
        D.covariantTensorDerivative D.riemannEvaluation x ![b e, b a, b c, b d, b f] *
          V e a c * U d f) -
      2 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f, R a c d f * V e a c * V e d f) := by
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
  have hn := hamilton_reaction_collected_nonneg R P Q U W
    hfirst hlast hpair hbianchi hP hU hQ
  have ht' : t ∈ interior (Set.Ioo T₀ T₁) := by simpa only [interior_Ioo] using ht
  have hm := hamiltonM_heat_quadratic_cancellation hC F T₀ ht'
    (ne_of_gt (sub_pos.mpr ht.1)) x W
  have hp := hamiltonP_heat_quadratic_cancellation hC F ht' ((2 * (t - T₀))⁻¹) x U W
  dsimp only [R, P, Q, D, b] at hn
  dsimp only at hn hm hp ⊢
  simp_rw [F.tensorHeatOperator_riemann hC ht']
  simp only [LeviCivitaData.curvatureB, mul_assoc, ← Finset.mul_sum] at hn hm hp ⊢
  linarith only [hn, hm, hp]

lemma hamilton_heat_quadratic_nonneg_at_null
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Set.Ioo T₀ T₁)) {t : ℝ} (ht : t ∈ Set.Ioo T₀ T₁) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hU : ∀ a c, U a c = -U c a) (hQ : HamiltonBlockPos F t x (t - T₀))
    (hnull : let D := F.connection t
      let b := (F.metric t).orthonormalBasis x
      (∑ a, ∑ c, hamiltonM D (t - T₀) x (b a) (b c) * W a * W c) +
        2 * (∑ a, ∑ c, ∑ d, hamiltonP D x (b a) (b c) (b d) * U a c * W d) +
        (∑ a, ∑ c, ∑ d, ∑ e,
          D.curvatureTensor x (b a) (b c) (b d) (b e) * U a c * U d e) = 0) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let Ric := fun a c => D.ricci x (b a) (b c)
    let k := (2 * (t - T₀))⁻¹
    let V := fun e a c =>
      ((Ric e a + k * (if e = a then 1 else 0)) * W c -
        W a * (Ric e c + k * (if e = c then 1 else 0))) / 2
    0 ≤ (∑ a, ∑ c, F.tensorHeatOperator (fun s y z =>
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
        D.curvatureTensor x (b a) (b c) (b d) (b f) * V e a c * V e d f) := by
  have h := hamilton_heat_quadratic_nonneg_of_block hC F ht x U W hU hQ
  have hz := hamiltonBlock_vector_contraction_zero
    (fun a c d e => (F.connection t).curvatureTensor x
      ((F.metric t).orthonormalBasis x a) ((F.metric t).orthonormalBasis x c)
      ((F.metric t).orthonormalBasis x d) ((F.metric t).orthonormalBasis x e))
    (fun a c d => hamiltonP (F.connection t) x ((F.metric t).orthonormalBasis x a)
      ((F.metric t).orthonormalBasis x c) ((F.metric t).orthonormalBasis x d))
    (fun a c => hamiltonM (F.connection t) (t - T₀) x ((F.metric t).orthonormalBasis x a)
      ((F.metric t).orthonormalBasis x c)) U W hQ hnull
  dsimp only at h ⊢
  simpa only [hz, mul_zero, add_zero] using h

end Poincare.RicciFlow.Harnack
