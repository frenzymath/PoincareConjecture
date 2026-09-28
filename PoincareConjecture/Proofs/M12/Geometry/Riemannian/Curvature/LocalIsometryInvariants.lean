import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometryRicci
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.Scalar.Trace
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Curvature.Tensorial
import PoincareConjecture.Proofs.M12.Geometry.Curvature.Operator.Bounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}


theorem scalarCurvature_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.scalarCurvature x = D'.scalarCurvature (f x) := by
  let e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
      (g.mfderiv_bijective_of_pullback_eq h x (fun a b => (hmetric x hx a b).symm))
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e' := e.isometryOfInner (fun a b => (hmetric x hx a b).symm)
  rw [D'.scalarCurvature_eq_sum_orthonormalBasis (f x)
    ((g.orthonormalBasis x).map e')]
  change (∑ i, ∑ j, D.curvatureTensor x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)) =
    ∑ i, ∑ j, D'.curvatureTensor (f x)
      (e (g.orthonormalBasis x i)) (e (g.orthonormalBasis x j))
      (e (g.orthonormalBasis x i)) (e (g.orthonormalBasis x j))
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx _ _ _ _

private theorem sum_four_exchange {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ι → ι → ι → κ → κ → κ → κ → ℝ) :
    (∑ a, ∑ b, ∑ d, ∑ e, ∑ i, ∑ j, ∑ k, ∑ l, f a b d e i j k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ b, ∑ d, ∑ e, f a b d e i j k l := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a : (ι × ι) × (ι × ι) ↦
      fun i : (κ × κ) × (κ × κ) ↦
        f a.1.1 a.1.2 a.2.1 a.2.2 i.1.1 i.1.2 i.2.1 i.2.2))

private theorem sum_fin_cons {ι : Type*} [Fintype ι] {d : ℕ}
    (f : (Fin (d + 1) → ι) → ℝ) :
    (∑ p, f p) = ∑ a, ∑ q, f (Fin.cons a q) := by
  calc
    (∑ p, f p) = ∑ p : ι × (Fin d → ι), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d + 1) ↦ ι)).symm _ _
        (fun p ↦ congrArg f (Fin.cons_self_tail p).symm)
    _ = _ := Fintype.sum_prod_type _

private theorem fourTensor_expand {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] (b : Module.Basis ι ℝ E)
    (R : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (v : Fin 4 → E) :
    R v = ∑ i, ∑ j, ∑ k, ∑ l,
      (b.repr (v 0) i * b.repr (v 1) j * b.repr (v 2) k * b.repr (v 3) l) *
        R ![b i, b j, b k, b l] := by
  classical
  conv_lhs => rw [show v = (fun a ↦ ∑ i, b.repr (v a) i • b i) by
    funext a; exact (b.sum_repr (v a)).symm]
  rw [R.map_sum]
  simp only [R.map_smul_univ, smul_eq_mul, sum_fin_cons, Fin.cons_zero,
    Fintype.sum_unique, Fin.prod_univ_succ, Fin.prod_univ_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fin.cons_succ, mul_one]
  ring_nf
  congr 1
  apply congrArg R
  funext a
  fin_cases a <;> rfl



theorem curvatureOperator_nonneg_in_frame
    (D : LeviCivitaData g) (x : M) (hD : D.NonnegativeCurvatureOperator x)
    {d : ℕ} (v : Fin d → TangentSpace (𝓡 n) x)
    (A : Fin d → Fin d → ℝ) (hA : IsSkewCoefficient d A) :
    0 ≤ ∑ a, ∑ b, ∑ c, ∑ e,
      A a b * A c e * D.curvatureTensor x (v a) (v b) (v c) (v e) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := (g.orthonormalBasis x).toBasis
  let U := fun a i ↦ b.repr (v a) i
  obtain ⟨R, hR⟩ := D.curvatureTensor_multilinear x
  let B := fun i j ↦ ∑ a, ∑ c, A a c * U a i * U c j
  have hB : IsSkewCoefficient _ B := by
    intro i j
    dsimp only [B]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro a _
    rw [hA c a]
    ring
  have hexpand (a c e f) : D.curvatureTensor x (v a) (v c) (v e) (v f) =
      ∑ i, ∑ j, ∑ k, ∑ l, (U a i * U c j * U e k * U f l) *
        D.curvatureTensor x (b i) (b j) (b k) (b l) := by
    simpa [← hR, riemannEvaluation, U] using
      fourTensor_expand b R ![v a, v c, v e, v f]
  have hquad : (∑ a, ∑ c, ∑ e, ∑ f,
      A a c * A e f * D.curvatureTensor x (v a) (v c) (v e) (v f)) =
      D.curvatureOperatorQuadratic x B := by
    simp only [hexpand, Finset.mul_sum]
    rw [sum_four_exchange]
    unfold curvatureOperatorQuadratic
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    dsimp only [B]
    simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    change _ = A a c * U a i * U c j * (A e f * U e k * U f l) *
      D.curvatureTensor x (b i) (b j) (b k) (b l)
    ring
  rw [hquad]
  exact hD B hB



theorem nonnegativeCurvatureOperator_iff_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.NonnegativeCurvatureOperator x ↔ D'.NonnegativeCurvatureOperator (f x) := by
  let e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
      (g.mfderiv_bijective_of_pullback_eq h x (fun a b => (hmetric x hx a b).symm))
  have hcurv (a b c d : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a b c d =
        D'.curvatureTensor (f x) (e a) (e b) (e c) (e d) :=
    D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx a b c d
  constructor
  · intro hD A hA
    have hp := D.curvatureOperator_nonneg_in_frame x hD
      (fun i => e.symm (h.orthonormalBasis (f x) i)) A hA
    simpa only [hcurv, LinearEquiv.apply_symm_apply, curvatureOperatorQuadratic] using hp
  · intro hD' A hA
    have hp := D'.curvatureOperator_nonneg_in_frame (f x) hD'
      (fun i => e (g.orthonormalBasis x i)) A hA
    simpa only [← hcurv, curvatureOperatorQuadratic] using hp

end PoincareConjecture.LeviCivitaData
