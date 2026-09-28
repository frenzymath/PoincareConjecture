import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.BlockContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedSpatialContact







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

universe u

variable {n : ℕ} {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]



theorem tensor_block_posSemidef_of_reference_unit_tests
    {I : Type*} [Fintype I] (g : RiemannianMetric n N)
    {R : CovariantTensorEvaluation n N 4} {P : CovariantTensorEvaluation n N 3}
    {B : CovariantTensorEvaluation n N 2}
    (hR : IsSmoothCovariantTensor R) (hP : IsSmoothCovariantTensor P)
    (hB : IsSmoothCovariantTensor B) (x : N)
    (hpair : ∀ a b c d, R x ![a, b, c, d] = R x ![c, d, a, b])
    (hfirst : ∀ a b c d, R x ![a, b, c, d] = -R x ![b, a, c, d])
    (hlast : ∀ a b c d, R x ![a, b, c, d] = -R x ![a, b, d, c])
    (hskew : ∀ a b c, P x ![a, b, c] = -P x ![b, a, c])
    (hsymm : ∀ a b, B x ![a, b] = B x ![b, a])
    (hunit : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
        ⟨g.toRiemannianMetric⟩
      ∀ (e : Fin n → TangentSpace (𝓡 n) x), Orthonormal ℝ e →
      ∀ z : EuclideanSpace ℝ ((Fin n × Fin n) ⊕ Fin n), ‖z‖ = 1 →
        (∀ a b, z (Sum.inl (a, b)) = -z (Sum.inl (b, a))) →
        0 ≤ (∑ a, ∑ b, B x ![e a, e b] * z (Sum.inr a) * z (Sum.inr b)) +
          2 * (∑ a, ∑ b, ∑ c, P x ![e a, e b, e c] *
            z (Sum.inl (a, b)) * z (Sum.inr c)) +
          (∑ a, ∑ b, ∑ c, ∑ d, R x ![e a, e b, e c, e d] *
            z (Sum.inl (a, b)) * z (Sum.inl (c, d))))
    (e : I → TangentSpace (𝓡 n) x) :
    (Matrix.fromBlocks (fun ac bd : I × I => R x ![e ac.1, e ac.2, e bd.1, e bd.2])
      (fun ac d => P x ![e ac.1, e ac.2, e d])
      (fun c bd => P x ![e bd.1, e bd.2, e c])
      (fun a b => B x ![e a, e b])).PosSemidef := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
  let ι := finCongr hdim
  let b := (g.orthonormalBasis x).reindex ι
  have hp := hamiltonBlock_posSemidef_of_unit_skew_quadratic_nonneg
    (fun a c d f => R x ![b a, b c, b d, b f])
    (fun a c d => P x ![b a, b c, b d]) (fun a c => B x ![b a, b c])
    (fun _ _ _ _ => hpair _ _ _ _) (fun _ _ _ _ => hfirst _ _ _ _)
    (fun _ _ _ _ => hlast _ _ _ _) (fun _ _ _ => hskew _ _ _)
    (fun _ _ => hsymm _ _) (hunit b b.orthonormal)
  let σ := Equiv.sumCongr (Equiv.prodCongr ι ι) ι
  have hp' := hp.submatrix σ
  apply tensor_block_posSemidef_of_basis g hR hP hB x ?_ e
  convert hp' using 1
  ext (ac | a) (bd | d) <;>
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      σ, Equiv.sumCongr_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Sum.map_inl, Sum.map_inr, b, OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]



theorem perturbedHamiltonBlock_posSemidef_of_reference_unit_tests
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ}
    (F : RicciFlow n N J) (g : RiemannianMetric n N)
    {t : ℝ} (ht : t ∈ interior J) (τ : ℝ) (x : N)
    (α : N → ℝ) (hα : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ α) (ψ : ℝ)
    (hunit : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
        ⟨g.toRiemannianMetric⟩
      ∀ (e : Fin n → TangentSpace (𝓡 n) x), Orthonormal ℝ e →
      ∀ z : EuclideanSpace ℝ ((Fin n × Fin n) ⊕ Fin n), ‖z‖ = 1 →
        (∀ a b, z (Sum.inl (a, b)) = -z (Sum.inl (b, a))) →
        0 ≤ (∑ a, ∑ b,
          (hamiltonM (F.connection t) τ x (e a) (e b) +
            α x * (F.metric t).inner x (e a) (e b)) * z (Sum.inr a) * z (Sum.inr b)) +
          2 * (∑ a, ∑ b, ∑ c, hamiltonP (F.connection t) x (e a) (e b) (e c) *
            z (Sum.inl (a, b)) * z (Sum.inr c)) +
          (∑ a, ∑ b, ∑ c, ∑ d,
            ((F.connection t).curvatureTensor x (e a) (e b) (e c) (e d) +
              ψ * metricTwoFormIdentity (F.metric t) x ![e a, e b, e c, e d]) *
                z (Sum.inl (a, b)) * z (Sum.inl (c, d)))) :
    let b := (F.metric t).orthonormalBasis x
    (Matrix.fromBlocks
      (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        (F.connection t).curvatureTensor x (b ac.1) (b ac.2) (b de.1) (b de.2) +
          ψ * twoFormIdentity ac.1 ac.2 de.1 de.2)
      (fun ac d => hamiltonP (F.connection t) x (b ac.1) (b ac.2) (b d))
      (fun c de => hamiltonP (F.connection t) x (b de.1) (b de.2) (b c))
      (fun a c => hamiltonM (F.connection t) τ x (b a) (b c) +
        α x * (if a = c then 1 else 0))).PosSemidef := by
  let D := F.connection t
  have hD := hC.tensor_calculus n N (F.metric t) D
  let R : CovariantTensorEvaluation n N 4 := fun y v =>
    D.riemannEvaluation y v + ψ * metricTwoFormIdentity (F.metric t) y v
  let P : CovariantTensorEvaluation n N 3 := fun y v =>
    hamiltonP D y (v 0) (v 1) (v 2)
  let B : CovariantTensorEvaluation n N 2 := fun y v =>
    hamiltonM D τ y (v 0) (v 1) + α y * (F.metric t).inner y (v 0) (v 1)
  have hR : IsSmoothCovariantTensor R :=
    hD.1.add ((metricTwoFormIdentity_isSmooth (F.metric t)).const_mul ψ)
  have hP : IsSmoothCovariantTensor P := hamiltonP_isSmoothCovariantTensor D hD
  have hB : IsSmoothCovariantTensor B :=
    (hamiltonM_isSmoothCovariantTensor D hD τ).add
      (scalar_metric_isSmoothCovariantTensor (g := F.metric t) hα)
  have hpair (a b c d) : R x ![a, b, c, d] = R x ![c, d, a, b] := by
    change D.curvatureTensor x a b c d + ψ * metricTwoFormIdentity (F.metric t) x ![a, b, c, d] =
      D.curvatureTensor x c d a b + ψ * metricTwoFormIdentity (F.metric t) x ![c, d, a, b]
    rw [(hD.2.2.2.1 x a b c d).2.1]
    congr 1
    simp only [metricTwoFormIdentity, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [(F.metric t).symm x c a, (F.metric t).symm x d b,
      (F.metric t).symm x c b, (F.metric t).symm x d a]
    ring
  have hlast (a b c d) : R x ![a, b, c, d] = -R x ![a, b, d, c] := by
    change D.curvatureTensor x a b c d + ψ * metricTwoFormIdentity (F.metric t) x ![a, b, c, d] =
      -(D.curvatureTensor x a b d c + ψ * metricTwoFormIdentity (F.metric t) x ![a, b, d, c])
    rw [(hD.2.2.2.1 x a b c d).1]
    simp only [metricTwoFormIdentity, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hfirst (a b c d) : R x ![a, b, c, d] = -R x ![b, a, c, d] := by
    rw [hpair, hlast, hpair]
  have hp (a b c) : P x ![a, b, c] = -P x ![b, a, c] :=
    hamiltonP_skew D x a b c
  have hb (a b) : B x ![a, b] = B x ![b, a] := by
    change hamiltonM D τ x a b + α x * (F.metric t).inner x a b =
      hamiltonM D τ x b a + α x * (F.metric t).inner x b a
    rw [hamiltonM_symm_of_curvatureTheory hC J F t (interior_subset ht) τ x a b,
      (F.metric t).symm x a b]
  have h := tensor_block_posSemidef_of_reference_unit_tests g hR hP hB x
    hpair hfirst hlast hp hb hunit ((F.metric t).orthonormalBasis x)
  simpa only [R, P, B, D, LeviCivitaData.riemannEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons,
    metricTwoFormIdentity_orthonormalBasis, metric_inner_orthonormalBasis] using h



theorem hamiltonBlockPos_of_reference_unit_tests
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n N (Set.Ioo T₀ T₁))
    (g : RiemannianMetric n N) {t : ℝ} (ht : t ∈ Set.Ioo T₀ T₁) (τ : ℝ) (x : N)
    (hunit : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
        ⟨g.toRiemannianMetric⟩
      ∀ (e : Fin n → TangentSpace (𝓡 n) x), Orthonormal ℝ e →
      ∀ z : EuclideanSpace ℝ ((Fin n × Fin n) ⊕ Fin n), ‖z‖ = 1 →
        (∀ a b, z (Sum.inl (a, b)) = -z (Sum.inl (b, a))) →
        0 ≤ (∑ a, ∑ b,
          hamiltonM (F.connection t) τ x (e a) (e b) * z (Sum.inr a) * z (Sum.inr b)) +
          2 * (∑ a, ∑ b, ∑ c, hamiltonP (F.connection t) x (e a) (e b) (e c) *
            z (Sum.inl (a, b)) * z (Sum.inr c)) +
          (∑ a, ∑ b, ∑ c, ∑ d,
            (F.connection t).curvatureTensor x (e a) (e b) (e c) (e d) *
              z (Sum.inl (a, b)) * z (Sum.inl (c, d)))) :
    HamiltonBlockPos F t x τ := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let D := F.connection t
  have hD := hC.tensor_calculus n N (F.metric t) D
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
  let ι := finCongr hdim
  let b := (g.orthonormalBasis x).reindex ι
  let R := fun a c d e => D.curvatureTensor x (b a) (b c) (b d) (b e)
  let P := fun a c d => hamiltonP D x (b a) (b c) (b d)
  let B := fun a c => hamiltonM D τ x (b a) (b c)
  have hpair (a c d e) : R a c d e = R d e a c :=
    (hD.2.2.2.1 x _ _ _ _).2.1
  have hlast (a c d e) : R a c d e = -R a c e d :=
    (hD.2.2.2.1 x _ _ _ _).1
  have hfirst (a c d e) : R a c d e = -R c a d e := by
    rw [hpair, hlast, hpair]
  have hp (a c d) : P a c d = -P c a d := hamiltonP_skew D x _ _ _
  have hb (a c) : B a c = B c a :=
    hamiltonM_symm_of_curvatureTheory hC (Set.Ioo T₀ T₁) F t ht τ x _ _
  have hpos := hamiltonBlock_posSemidef_of_unit_skew_quadratic_nonneg R P B
    hpair hfirst hlast hp hb (hunit b b.orthonormal)
  let σ := Equiv.sumCongr (Equiv.prodCongr ι ι) ι
  have hpos' := hpos.submatrix σ
  have hB := hamiltonM_isSmoothCovariantTensor D hD τ
  have hP := hamiltonP_isSmoothCovariantTensor D hD
  apply tensor_block_posSemidef_of_basis g hD.1 hP hB x ?_
    ((F.metric t).orthonormalBasis x)
  convert hpos' using 1
  ext (ac | a) (bd | d) <;>
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      σ, Equiv.sumCongr_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Sum.map_inl, Sum.map_inr,
      R, P, B, b, OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply,
      LeviCivitaData.riemannEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

end Poincare.RicciFlow.Harnack
