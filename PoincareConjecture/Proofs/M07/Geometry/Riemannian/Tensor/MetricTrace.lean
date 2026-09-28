import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Contraction











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology
open Filter

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

section Matrices

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [IsManifold (𝓡 n) ∞ M] in
private lemma mdifferentiableAt_matrix_det (G : M → Matrix ι ι ℝ) (x : M)
    (hG : ∀ i j, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ G y i j) x) :
    MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ (G y).det) x := by
  simp only [Matrix.det_apply']
  have h : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (∑ σ : Equiv.Perm ι, (fun _ : M ↦ (Equiv.Perm.sign σ : ℝ)) *
        ∏ i, (fun y ↦ G y (σ i) i)) x :=
    MDifferentiableAt.sum fun σ _ ↦ mdifferentiableAt_const.mul
      (MDifferentiableAt.prod fun i _ ↦ hG (σ i) i)
  convert h using 1
  ext y
  simp

omit [IsManifold (𝓡 n) ∞ M] in
private lemma mdifferentiableAt_matrix_inv_entry (G : M → Matrix ι ι ℝ) (x : M)
    (hG : ∀ i j, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ G y i j) x)
    (hx : (G x).det ≠ 0) (i j : ι) :
    MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ (G y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply ((mdifferentiableAt_matrix_det G x hG).inv hx).mul
  apply mdifferentiableAt_matrix_det
  intro a b
  by_cases ha : a = j
  · subst a
    simpa using (mdifferentiableAt_const (I := 𝓡 n) (x := x)
      (c := (Pi.single i (1 : ℝ) : ι → ℝ) b))
  · simpa [Matrix.updateRow_apply, ha] using hG a b

private lemma mvfderiv_matrix_inv_entry_at_one (G : M → Matrix ι ι ℝ) (x : M)
    (hG : ∀ i j, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ G y i j) x)
    (hx : G x = 1) (v : TangentSpace (𝓡 n) x) (i j : ι) :
    mvfderiv (𝓡 n) (fun y ↦ (G y)⁻¹ i j) x v =
      -mvfderiv (𝓡 n) (fun y ↦ G y i j) x v := by
  have hdet : (G x).det ≠ 0 := by simp [hx]
  have hi := mdifferentiableAt_matrix_inv_entry G x hG hdet
  have hdetNear : ∀ᶠ y in 𝓝 x, (G y).det ≠ 0 :=
    (mdifferentiableAt_matrix_det G x hG).continuousAt.eventually_ne hdet
  have hprod : (fun y ↦ ∑ k, (G y)⁻¹ i k * G y k j) =ᶠ[𝓝 x]
      (fun _ ↦ (1 : Matrix ι ι ℝ) i j) := by
    filter_upwards [hdetNear] with y hy
    exact congrArg (fun A : Matrix ι ι ℝ ↦ A i j)
      (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hy))
  have hd := Filter.EventuallyEq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) hprod
  have hzero : mvfderiv (𝓡 n) (fun y ↦ ∑ k, (G y)⁻¹ i k * G y k j) x v = 0 := by
    change mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) _ x v = 0
    rw [hd]
    simp
  have hs := LeviCivitaData.mvfderiv_sum_apply
    (fun k y ↦ (G y)⁻¹ i k * G y k j) x v (fun k ↦ (hi i k).mul (hG k j))
  rw [hs] at hzero
  simp_rw [mvfderiv_fun_mul (hi _ _) (hG _ _)] at hzero
  simp only [add_apply, smul_apply, smul_eq_mul] at hzero
  simp [hx, Matrix.one_apply, Finset.sum_add_distrib] at hzero
  linarith

private lemma mvfderiv_inverse_gram_contraction (G A : M → Matrix ι ι ℝ) (x : M)
    (hG : ∀ i j, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ G y i j) x)
    (hA : ∀ i j, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ A y i j) x)
    (hx : G x = 1) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y ↦ ∑ i, ∑ j, (G y)⁻¹ i j * A y i j) x v =
      mvfderiv (𝓡 n) (fun y ↦ ∑ i, A y i i) x v -
        ∑ i, ∑ j, mvfderiv (𝓡 n) (fun y ↦ G y i j) x v * A x i j := by
  have hi := mdifferentiableAt_matrix_inv_entry G x hG (by simp [hx])
  have hm (i j : ι) : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun y ↦ (G y)⁻¹ i j * A y i j) x := (hi i j).mul (hA i j)
  have hs (i : ι) : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun y ↦ ∑ j, (G y)⁻¹ i j * A y i j) x := by
    convert (MDifferentiableAt.sum (t := Finset.univ) (fun j _ ↦ hm i j)) using 1
    ext y
    simp
  rw [LeviCivitaData.mvfderiv_sum_apply _ x v hs,
    LeviCivitaData.mvfderiv_sum_apply _ x v (fun i ↦ hA i i)]
  simp_rw [LeviCivitaData.mvfderiv_sum_apply _ x v (hm _)]
  simp_rw [mvfderiv_fun_mul (hi _ _) (hA _ _)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  simp_rw [mvfderiv_matrix_inv_entry_at_one G x hG hx]
  simp [hx, Matrix.one_apply, Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib, sub_eq_add_neg, mul_comm]

end Matrices

private lemma eventually_exists_basis_extend {ι : Type} (x : M)
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    ∀ᶠ y in 𝓝 x, ∃ c : Module.Basis ι ℝ (TangentSpace (𝓡 n) y),
      ∀ i, c i = FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i) y := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E V x
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  let L := (e.continuousLinearEquivAt ℝ x hx).trans
    (e.continuousLinearEquivAt ℝ y hy).symm
  refine ⟨b.map L.toLinearEquiv, fun i ↦ ?_⟩
  change (e.continuousLinearEquivAt ℝ y hy).symm
    ((e.continuousLinearEquivAt ℝ x hx) (b i)) = _
  rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq,
    Bundle.Trivialization.symmL_apply _ hy]
  rfl

namespace LeviCivitaData

variable {g : RiemannianMetric n M}



lemma mvfderiv_metricTrace_eq_fixed_trace_sub_gram
    (T : CovariantTensorEvaluation n M 2) (x : M)
    (hlin : ∀ᶠ y in 𝓝 x, ∃ B : TangentSpace (𝓡 n) y →ₗ[ℝ]
      TangentSpace (𝓡 n) y →ₗ[ℝ] ℝ, ∀ a b, T y ![a, b] = B a b)
    (hT : ∀ i j, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun y ↦ T y ![
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (g.orthonormalBasis x i) y,
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (g.orthonormalBasis x j) y]) x)
    (v : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let X := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    mvfderiv (𝓡 n)
      (fun y ↦ ∑ i, T y ![g.orthonormalBasis y i, g.orthonormalBasis y i]) x v =
      mvfderiv (𝓡 n) (fun y ↦ ∑ i, T y ![X i y, X i y]) x v -
        ∑ i, ∑ j, mvfderiv (𝓡 n) (fun y ↦ g.inner y (X i y) (X j y)) x v *
          T x ![b i, b j] := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  let b := g.orthonormalBasis x
  let X := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let G : M → Matrix _ _ ℝ := fun y i j ↦ g.inner y (X i y) (X j y)
  let A : M → Matrix _ _ ℝ := fun y i j ↦ T y ![X i y, X j y]
  have hG (i j) : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun y ↦ G y i j) x := by
    exact ((FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (b i)).inner_bundle
      (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) (b j))).mdifferentiableAt (by simp)
  have hx : G x = 1 := by
    ext i j
    change g.inner x (X i x) (X j x) = _
    simp only [X, FiberBundle.extend_apply_self]
    change inner ℝ (b i) (b j) = _
    exact b.inner_eq_ite i j
  have htrace : (fun y ↦ ∑ i, T y ![g.orthonormalBasis y i, g.orthonormalBasis y i])
      =ᶠ[𝓝 x] (fun y ↦ ∑ i, ∑ j, (G y)⁻¹ i j * A y i j) := by
    filter_upwards [hlin, eventually_exists_basis_extend x b.toBasis] with y hy hb
    obtain ⟨B, hB⟩ := hy
    obtain ⟨c, hc⟩ := hb
    have h := bilinear_sum_basis_eq_inverse_gram B c (g.orthonormalBasis y)
    change (∑ a, B (g.orthonormalBasis y a) (g.orthonormalBasis y a)) =
      ∑ i, ∑ j, (Matrix.of (fun i j ↦ g.inner y (c i) (c j)))⁻¹ i j *
        B (c i) (c j) at h
    simp only [← hB, hc, OrthonormalBasis.coe_toBasis] at h
    exact h
  have hd : mvfderiv (𝓡 n)
      (fun y ↦ ∑ i, T y ![g.orthonormalBasis y i, g.orthonormalBasis y i]) x v =
      mvfderiv (𝓡 n) (fun y ↦ ∑ i, ∑ j, (G y)⁻¹ i j * A y i j) x v := by
    exact DFunLike.congr_fun (htrace.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))) v
  dsimp only
  rw [hd]
  simpa only [A, G, X, b, FiberBundle.extend_apply_self] using
    mvfderiv_inverse_gram_contraction G A x hG hT hx v


lemma sum_covariantTensorDerivative_eq_mvfderiv_metricTrace
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M 2}
    (hT : IsSmoothCovariantTensor T) (x : M) (v : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative T x
      ![v, g.orthonormalBasis x i, g.orthonormalBasis x i]) =
      mvfderiv (𝓡 n)
        (fun y ↦ ∑ i, T y ![g.orthonormalBasis y i, g.orthonormalBasis y i]) x v := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [D.sum_covariantTensorDerivative_eq_fixed_trace_sub_gram hT x v]
  symm
  apply mvfderiv_metricTrace_eq_fixed_trace_sub_gram (g := g) T x
  · exact Filter.Eventually.of_forall fun y ↦ by
      obtain ⟨A, hA⟩ := hT.1 y
      refine ⟨bilinearOfTwoTensor A, ?_⟩
      intro a b
      exact hA ![a, b]
  · intro i j
    convert (hT.contMDiffAt_extend x
      ![g.orthonormalBasis x i, g.orthonormalBasis x j]).mdifferentiableAt (by simp) using 1
    ext y
    congr 1
    ext k
    fin_cases k <;> rfl


lemma sum_covariantTensorDerivative_ricci_eq_scalar_derivative
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative D.ricciEvaluation x
      ![v, g.orthonormalBasis x i, g.orthonormalBasis x i]) =
      mvfderiv (𝓡 n) D.scalarCurvature x v := by
  exact D.sum_covariantTensorDerivative_eq_mvfderiv_metricTrace hD.2.1 x v

end LeviCivitaData

end PoincareConjecture
