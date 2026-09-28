import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.GeometricContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.BasisChange
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Divergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.ReactionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Finite







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Matrix Filter

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



lemma hamiltonM_isSmoothCovariantTensor
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (τ : ℝ) :
    IsSmoothCovariantTensor (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) =>
      hamiltonM D τ y (z 0) (z 1)) := by
  let P : CovariantTensorEvaluation n M 3 := fun y z =>
    hamiltonP D y (z 0) (z 1) (z 2)
  have hB : IsSmoothCovariantTensor (g.tensorTrace (D.covariantTensorDerivative P)) :=
    (D.covariantTensorDerivative_isSmooth (hamiltonP_isSmoothCovariantTensor D hD)).tensorTrace
  have hC := D.isSmoothCovariantTensor_curvatureRicci hD
  have hQ := hD.2.1.const_mul (2 * τ)⁻¹
  convert (hB.add hC).add hQ using 1
  funext y z
  rw [hamiltonM_eq_divergence_hamiltonP D hD]
  dsimp only [RiemannianMetric.tensorTrace, P]
  have hz : z = ![z 0, z 1] := by ext i; fin_cases i <;> rfl
  rw [hz]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hflip (a b c d : TangentSpace (𝓡 n) y) :
      D.curvatureTensor y a b c d = D.curvatureTensor y b a d c := by
    rw [(hD.2.2.2.1 y a b c d).2.1, (hD.2.2.2.1 y c d a b).1,
      (hD.2.2.2.1 y c d b a).2.1, (hD.2.2.2.1 y b a c d).1, neg_neg]
  simp_rw [hflip (g.orthonormalBasis y _) (z 0) (g.orthonormalBasis y _) (z 1)]
  simp [LeviCivitaData.ricciEvaluation, div_eq_mul_inv, mul_comm]

private def blockRank {I : Type} : ((I × I) ⊕ I) → ((I × I) ⊕ I) → ℕ
  | .inl _, .inl _ => 4
  | .inl _, .inr _ => 3
  | .inr _, .inl _ => 3
  | .inr _, .inr _ => 2

private def blockSlots {I : Type} :
    (i j : (I × I) ⊕ I) → Fin (blockRank i j) → I
  | .inl ab, .inl cd => ![ab.1, ab.2, cd.1, cd.2]
  | .inl ab, .inr c => ![ab.1, ab.2, c]
  | .inr a, .inl bc => ![bc.1, bc.2, a]
  | .inr a, .inr b => ![a, b]

private def blockTensor {I : Type}
    (R : CovariantTensorEvaluation n M 4) (P : CovariantTensorEvaluation n M 3)
    (B : CovariantTensorEvaluation n M 2) :
    (i j : (I × I) ⊕ I) → CovariantTensorEvaluation n M (blockRank i j)
  | .inl _, .inl _ => R
  | .inl _, .inr _ => P
  | .inr _, .inl _ => P
  | .inr _, .inr _ => B

private lemma map_vec_two {α β : Type*} (f : α → β) (a b : α) :
    (fun l : Fin 2 => f (![a, b] l)) = ![f a, f b] := by
  ext l; fin_cases l <;> rfl

private lemma map_vec_three {α β : Type*} (f : α → β) (a b c : α) :
    (fun l : Fin 3 => f (![a, b, c] l)) = ![f a, f b, f c] := by
  ext l; fin_cases l <;> rfl

private lemma map_vec_four {α β : Type*} (f : α → β) (a b c d : α) :
    (fun l : Fin 4 => f (![a, b, c, d] l)) = ![f a, f b, f c, f d] := by
  ext l; fin_cases l <;> rfl

omit [IsManifold (𝓡 n) ∞ M] in
private lemma blockTensor_eq {I : Type}
    (R : CovariantTensorEvaluation n M 4) (P : CovariantTensorEvaluation n M 3)
    (B : CovariantTensorEvaluation n M 2) (y : M) (e : I → TangentSpace (𝓡 n) y) :
    (fun i j => blockTensor R P B i j y (fun l => e (blockSlots i j l))) =
      Matrix.fromBlocks (fun ab cd : I × I => R y ![e ab.1, e ab.2, e cd.1, e cd.2])
        (fun ab c => P y ![e ab.1, e ab.2, e c])
        (fun a bc => P y ![e bc.1, e bc.2, e a]) (fun a b => B y ![e a, e b]) := by
  ext (ab | a) (cd | c) <;>
    simp only [blockTensor, blockSlots, blockRank,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      map_vec_two, map_vec_three, map_vec_four]



theorem tensor_block_diffusion_nonneg_at_null [T2Space M]
    {I : Type} [Fintype I] (D : LeviCivitaData g)
    {R : CovariantTensorEvaluation n M 4} {P : CovariantTensorEvaluation n M 3}
    {B : CovariantTensorEvaluation n M 2}
    (hR : IsSmoothCovariantTensor R) (hP : IsSmoothCovariantTensor P)
    (hB : IsSmoothCovariantTensor B)
    (x : M) (v : I → TangentSpace (𝓡 n) x)
    (hpos : ∀ᶠ y in 𝓝 x, ∀ e : I → TangentSpace (𝓡 n) y,
      (Matrix.fromBlocks (fun ab cd : I × I => R y ![e ab.1, e ab.2, e cd.1, e cd.2])
        (fun ab c => P y ![e ab.1, e ab.2, e c])
        (fun a bc => P y ![e bc.1, e bc.2, e a])
        (fun a b => B y ![e a, e b])).PosSemidef)
    (U : I → I → ℝ) (W : I → ℝ)
    (hnull : (∑ a, ∑ b, B x ![v a, v b] * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, P x ![v a, v b, v c] * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d, R x ![v a, v b, v c, v d] * U a b * U c d) = 0)
    (A : I → I → TangentSpace (𝓡 n) x) :
    0 ≤ (∑ a, ∑ b, D.tensorLaplacian B x ![v a, v b] * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, D.tensorLaplacian P x ![v a, v b, v c] * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d,
        D.tensorLaplacian R x ![v a, v b, v c, v d] * U a b * U c d) +
      4 * (∑ a, ∑ b, ∑ c, ∑ d,
        U a b * D.covariantTensorDerivative R x ![A c d, v a, v b, v c, v d]) +
      4 * (∑ a, ∑ b, ∑ c,
        W c * D.covariantTensorDerivative P x ![A a b, v a, v b, v c]) +
      2 * (∑ a, ∑ b, ∑ c, ∑ d,
        R x ![v a, v b, v c, v d] * g.inner x (A a b) (A c d)) := by
  let z : ((I × I) ⊕ I) → ℝ := Sum.elim (fun ab => U ab.1 ab.2) W
  let V : ((I × I) ⊕ I) → TangentSpace (𝓡 n) x :=
    Sum.elim (fun ab => A ab.1 ab.2) (fun _ => 0)
  have hT : ∀ i j : (I × I) ⊕ I, IsSmoothCovariantTensor (blockTensor R P B i j) := by
    rintro (ab | a) (cd | c)
    · exact hR
    · exact hP
    · exact hP
    · exact hB
  have hn : z ⬝ᵥ ((fun i j => blockTensor R P B i j x
      (fun l => v (blockSlots i j l))) *ᵥ z) = 0 := by
    rw [blockTensor_eq]
    exact (hamiltonBlock_quadratic_eq
      (fun a b c d => R x ![v a, v b, v c, v d])
      (fun a b c => P x ![v a, v b, v c])
      (fun a b => B x ![v a, v b]) U W).trans hnull
  have hp : ∀ᶠ y in 𝓝 x, ∀ e : I → TangentSpace (𝓡 n) y,
      Matrix.PosSemidef (fun i j => blockTensor R P B i j y
        (fun l => e (blockSlots i j l))) := by
    filter_upwards [hpos] with y hy e
    rw [blockTensor_eq]
    exact hy e
  have h := tensor_matrix_diffusion_nonneg_at_null D blockRank (blockTensor R P B)
    hT blockSlots x v hp z hn V
  have hΔ : (∑ i, ∑ j, z i * D.tensorLaplacian (blockTensor R P B i j) x
      (fun l => v (blockSlots i j l)) * z j) =
      (∑ a, ∑ b, D.tensorLaplacian B x ![v a, v b] * W a * W b) +
      2 * (∑ a, ∑ b, ∑ c, D.tensorLaplacian P x ![v a, v b, v c] * U a b * W c) +
      (∑ a, ∑ b, ∑ c, ∑ d,
        D.tensorLaplacian R x ![v a, v b, v c, v d] * U a b * U c d) := by
    have he := hamiltonBlock_quadratic_eq
      (fun a b c d => D.tensorLaplacian R x ![v a, v b, v c, v d])
      (fun a b c => D.tensorLaplacian P x ![v a, v b, v c])
      (fun a b => D.tensorLaplacian B x ![v a, v b]) U W
    convert he using 1
    simp only [dotProduct, mulVec, Fintype.sum_sum_type, Fintype.sum_prod_type,
      z, Sum.elim_inl, Sum.elim_inr, blockTensor, blockSlots, blockRank,
      map_vec_two, map_vec_three, map_vec_four,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_assoc]
  rw [hΔ] at h
  have hzero {k : ℕ} {T : CovariantTensorEvaluation n M k}
      (hT : IsSmoothCovariantTensor T) (w : Fin k → TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative T x (Matrix.vecCons 0 w) = 0 := by
    obtain ⟨L, hL⟩ := (D.covariantTensorDerivative_isSmooth hT).1 x
    change D.covariantTensorDerivative T x (Fin.cons 0 w) = 0
    rw [← Fin.update_cons_zero (x := (0 : TangentSpace (𝓡 n) x)), hL, L.map_update_zero]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, z, V,
    Sum.elim_inl, Sum.elim_inr, blockTensor, blockSlots, blockRank,
    map_vec_two, map_vec_three, map_vec_four, hzero hP, hzero hB,
    map_zero, _root_.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, Finset.sum_add_distrib, Matrix.Fin.cons_vecCons] at h
  have hporder : (∑ c, ∑ a, ∑ b,
      W c * D.covariantTensorDerivative P x ![A a b, v a, v b, v c]) =
      ∑ a, ∑ b, ∑ c,
        W c * D.covariantTensorDerivative P x ![A a b, v a, v b, v c] := by
    rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
  rw [hporder] at h
  linarith only [h]

private lemma covariantTensorDerivative_cons_sum
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (w : Fin k → TangentSpace (𝓡 n) x)
    (c : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    D.covariantTensorDerivative T x
        (Fin.cons (∑ e, c e • g.orthonormalBasis x e) w) =
      ∑ e, c e * D.covariantTensorDerivative T x
        (Fin.cons (g.orthonormalBasis x e) w) := by
  classical
  obtain ⟨L, hL⟩ := (D.covariantTensorDerivative_isSmooth hT).1 x
  rw [← Fin.update_cons_zero (x := (0 : TangentSpace (𝓡 n) x)), hL,
    L.map_update_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [L.map_update_smul]
  simp only [smul_eq_mul, Fin.update_cons_zero, ← hL]

private lemma sum_four_last {I : Type} [Fintype I] (f : I → I → I → I → ℝ) :
    (∑ a, ∑ c, ∑ d, ∑ e, f a c d e) = ∑ e, ∑ a, ∑ c, ∑ d, f a c d e := by
  calc
    _ = ∑ a, ∑ e, ∑ c, ∑ d, f a c d e := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm_cycle
    _ = _ := Finset.sum_comm

private lemma sum_five_last {I : Type} [Fintype I] (f : I → I → I → I → I → ℝ) :
    (∑ a, ∑ c, ∑ d, ∑ f', ∑ e, f a c d f' e) =
      ∑ e, ∑ a, ∑ c, ∑ d, ∑ f', f a c d f' e := by
  calc
    _ = ∑ a, ∑ e, ∑ c, ∑ d, ∑ f', f a c d f' e := by
      apply Finset.sum_congr rfl
      intro a _
      exact sum_four_last (f a)
    _ = _ := Finset.sum_comm




theorem hamilton_diffusion_quadratic_nonneg_at_null [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Set.Ioo T₀ T₁)) (t τ : ℝ) (x : M)
    (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ)
    (hQ : ∀ᶠ y in 𝓝 x, HamiltonBlockPos F t y τ)
    (hnull : let D := F.connection t
      let b := (F.metric t).orthonormalBasis x
      (∑ a, ∑ c, hamiltonM D τ x (b a) (b c) * W a * W c) +
        2 * (∑ a, ∑ c, ∑ d, hamiltonP D x (b a) (b c) (b d) * U a c * W d) +
        (∑ a, ∑ c, ∑ d, ∑ e,
          D.curvatureTensor x (b a) (b c) (b d) (b e) * U a c * U d e) = 0)
    (V : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    0 ≤ (∑ a, ∑ c, D.tensorLaplacian (fun y z =>
      hamiltonM D τ y (z 0) (z 1)) x ![b a, b c] * W a * W c) +
      2 * (∑ a, ∑ c, ∑ d,
        D.tensorLaplacian (fun y z => hamiltonP D y
          (z 0) (z 1) (z 2)) x ![b a, b c, b d] * U a c * W d) +
      (∑ a, ∑ c, ∑ d, ∑ e,
        D.tensorLaplacian D.riemannEvaluation x ![b a, b c, b d, b e] * U a c * U d e) +
      4 * (∑ e, ∑ a, ∑ c, ∑ d,
        D.covariantTensorDerivative (fun y z => hamiltonP D y (z 0) (z 1) (z 2))
          x ![b e, b a, b c, b d] * V e a c * W d) +
      4 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
        D.covariantTensorDerivative D.riemannEvaluation x ![b e, b a, b c, b d, b f] *
          V e a c * U d f) +
      2 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
        D.curvatureTensor x (b a) (b c) (b d) (b f) * V e a c * V e d f) := by
  classical
  let D := F.connection t
  let g := F.metric t
  let b := g.orthonormalBasis x
  let P : CovariantTensorEvaluation n M 3 := fun y z => hamiltonP D y (z 0) (z 1) (z 2)
  let B : CovariantTensorEvaluation n M 2 := fun y z => hamiltonM D τ y (z 0) (z 1)
  let A := fun a c => ∑ e, V e a c • b e
  have hD := hC.tensor_calculus n M g D
  have hP : IsSmoothCovariantTensor P := hamiltonP_isSmoothCovariantTensor D hD
  have hB : IsSmoothCovariantTensor B := hamiltonM_isSmoothCovariantTensor D hD τ
  have hp : ∀ᶠ y in 𝓝 x, ∀ e : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      TangentSpace (𝓡 n) y,
      (Matrix.fromBlocks (fun ab cd : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        D.riemannEvaluation y ![e ab.1, e ab.2, e cd.1, e cd.2])
        (fun ab c => P y ![e ab.1, e ab.2, e c])
        (fun a bc => P y ![e bc.1, e bc.2, e a]) (fun a c => B y ![e a, e c])).PosSemidef := by
    filter_upwards [hQ] with y hy e
    exact tensor_block_posSemidef_of_basis g hD.1 hP hB y hy e
  have h := tensor_block_diffusion_nonneg_at_null D hD.1 hP hB x b hp U W hnull A
  have hfirstP (a c d) : D.covariantTensorDerivative P x ![A a c, b a, b c, b d] =
      ∑ e, V e a c * D.covariantTensorDerivative P x ![b e, b a, b c, b d] := by
    exact covariantTensorDerivative_cons_sum D hP x ![b a, b c, b d] (fun e => V e a c)
  have hfirstR (a c d f) : D.covariantTensorDerivative D.riemannEvaluation x
      ![A d f, b a, b c, b d, b f] =
      ∑ e, V e d f * D.covariantTensorDerivative D.riemannEvaluation x
        ![b e, b d, b f, b a, b c] := by
    rw [D.covariantTensorDerivative_riemannEvaluation_pair_swap hD]
    exact covariantTensorDerivative_cons_sum D hD.1 x ![b d, b f, b a, b c]
      (fun e => V e d f)
  have hinner (a c d f) : g.inner x (A a c) (A d f) = ∑ e, V e a c * V e d f := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change inner ℝ (∑ e, V e a c • b e) (∑ e, V e d f • b e) = _
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      b.inner_eq_ite, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    apply Finset.sum_congr rfl
    intro e _
    ring
  dsimp only [g] at hinner
  simp only [hfirstP, hfirstR, hinner, Finset.mul_sum] at h
  rw [sum_four_last (fun a c d e => 4 * (W d *
    (V e a c * D.covariantTensorDerivative P x ![b e, b a, b c, b d]))),
    sum_five_last (fun a c d f e => 4 * (U a c *
      (V e d f * D.covariantTensorDerivative D.riemannEvaluation x
        ![b e, b d, b f, b a, b c]))),
    sum_five_last (fun a c d f e => 2 * (D.riemannEvaluation x ![b a, b c, b d, b f] *
      (V e a c * V e d f)))] at h
  have hRorder : (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
      4 * (U a c * (V e d f * D.covariantTensorDerivative D.riemannEvaluation x
        ![b e, b d, b f, b a, b c]))) =
      ∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
        4 * (D.covariantTensorDerivative D.riemannEvaluation x ![b e, b a, b c, b d, b f] *
          V e a c * U d f) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm_cycle]
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hRorder] at h
  have hPorder : (∑ e, ∑ a, ∑ c, ∑ d,
      4 * (W d * (V e a c * D.covariantTensorDerivative P x ![b e, b a, b c, b d]))) =
      4 * (∑ e, ∑ a, ∑ c, ∑ d,
        D.covariantTensorDerivative P x ![b e, b a, b c, b d] * V e a c * W d) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hPorder] at h
  have hVorder : (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
      2 * (D.riemannEvaluation x ![b a, b c, b d, b f] * (V e a c * V e d f))) =
      2 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
        D.curvatureTensor x (b a) (b c) (b d) (b f) * V e a c * V e d f) := by
    simp only [Finset.mul_sum, mul_assoc, LeviCivitaData.riemannEvaluation,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [hVorder] at h
  have hRcoeff : (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
      4 * (D.covariantTensorDerivative D.riemannEvaluation x ![b e, b a, b c, b d, b f] *
        V e a c * U d f)) =
      4 * (∑ e, ∑ a, ∑ c, ∑ d, ∑ f,
        D.covariantTensorDerivative D.riemannEvaluation x ![b e, b a, b c, b d, b f] *
          V e a c * U d f) := by simp only [Finset.mul_sum]
  rw [hRcoeff] at h
  have hPcoeff : (∑ a, ∑ c, ∑ d,
      2 * (D.tensorLaplacian P x ![b a, b c, b d] * U a c * W d)) =
      2 * (∑ a, ∑ c, ∑ d,
        D.tensorLaplacian P x ![b a, b c, b d] * U a c * W d) := by
    simp only [Finset.mul_sum]
  rw [hPcoeff] at h
  dsimp only at ⊢
  linarith only [h]

end Poincare.RicciFlow.Harnack
