import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.PartialTrace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bilinear
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.SupportingLaplacian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.TimeTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.LowerContacts











noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow.Splitting

open Poincare.RicciFlow.Splitting

private lemma differentiableAt_clm_of_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
    {f : ℝ → E →L[ℝ] G} {t : ℝ}
    (hf : ∀ v, DifferentiableAt ℝ (fun s => f s v) t) :
    DifferentiableAt ℝ f t := by
  let d := Module.finrank ℝ E
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.differentiableAt.comp t (differentiableAt_pi.mpr fun i => hf _)

private lemma hasDerivAt_bilinear_moving
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (dL : E → E → ℝ)
    {t : ℝ} (hL : ∀ v w, HasDerivAt (fun s => L s v w) (dL v w) t)
    {V : ℝ → E} {V' : E} (hV : HasDerivAt V V' t) :
    HasDerivAt (fun s => L s (V s) (V s))
      (dL (V t) (V t) + L t V' (V t) + L t (V t) V') t := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  have hdiff : DifferentiableAt ℝ L t :=
    differentiableAt_clm_of_apply fun v =>
      differentiableAt_clm_of_apply fun w => (hL v w).differentiableAt
  have hd : HasDerivAt L (deriv L t) t := hdiff.hasDerivAt
  have hfixed := (hd.clm_apply (hasDerivAt_const t (V t))).clm_apply
    (hasDerivAt_const t (V t))
  have hcoeff : deriv L t (V t) (V t) = dL (V t) (V t) := by
    simpa only [map_zero, add_zero, zero_apply] using hfixed.unique (hL (V t) (V t))
  have hm := (hd.clm_apply hV).clm_apply hV
  simpa only [add_apply, hcoeff, add_comm, add_left_comm, add_assoc] using hm

private theorem bilinear_product_contraction_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j, A (b i) (b j) * B (b i) (b j)) =
      ∑ i, ∑ j, A (c i) (c j) * B (c i) (c j) := by
  have hright (v : E) :
      (∑ j, A v (b j) * B v (b j)) = ∑ j, A v (c j) * B v (c j) :=
    bilinear_sum_orthonormalBasis_eq ((A v).smulRight (B v)) b c
  simp_rw [hright]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => A (c i) (c j) * B (c i) (c j))]
  apply Finset.sum_congr rfl
  intro j _
  exact bilinear_sum_orthonormalBasis_eq
    ((A.flip (c j)).smulRight (B.flip (c j))) b c

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


def ricciBilinear (D : LeviCivitaData g) (x : M) :
    TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ :=
  ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)

@[simp] theorem ricciBilinear_apply (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) : ricciBilinear D x v w = D.ricci x v w := by
  simp [ricciBilinear, LeviCivitaData.ricci, LinearMap.sum_apply]


def metricRicciOperator (D : LeviCivitaData g) (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  (∑ i, ((ricciBilinear D x).flip (g.orthonormalBasis x i)).smulRight
    (g.orthonormalBasis x i)).toContinuousLinearMap

theorem metricRicciOperator_inner (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    g.inner x (metricRicciOperator D x v) w = D.ricci x v w := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change inner ℝ (metricRicciOperator D x v) w = _
  simp only [metricRicciOperator, LinearMap.coe_toContinuousLinearMap',
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
  rw [sum_inner]
  simp only [real_inner_smul_left]
  conv_rhs => rw [← ricciBilinear_apply D x v w, ← (g.orthonormalBasis x).sum_repr' w]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring


def ricciPartialTrace (D : LeviCivitaData g) (k : ℕ) (x : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  partialTrace k (metricRicciOperator D x)

theorem exists_ricci_minimizing_frame (D : LeviCivitaData g) (x : M)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ (TangentSpace (𝓡 n) x)) :
    ∃ v : Fin k → TangentSpace (𝓡 n) x,
      (∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) ∧
      (∑ i, D.ricci x (v i) (v i)) = ricciPartialTrace D k x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  obtain ⟨v, hv, hmin⟩ := exists_minimizing_frame hk (metricRicciOperator D x)
  refine ⟨v, orthonormal_iff_ite.mp hv, ?_⟩
  change (∑ i, g.inner x (metricRicciOperator D x (v i)) (v i)) =
    ricciPartialTrace D k x at hmin
  simpa only [metricRicciOperator_inner] using hmin

theorem ricciPartialTrace_le (D : LeviCivitaData g) (x : M) {k : ℕ}
    (v : Fin k → TangentSpace (𝓡 n) x)
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) :
    ricciPartialTrace D k x ≤ ∑ i, D.ricci x (v i) (v i) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have h := partialTrace_le_frameTrace (metricRicciOperator D x)
    (orthonormal_iff_ite.mpr hv)
  change ricciPartialTrace D k x ≤
    ∑ i, g.inner x (metricRicciOperator D x (v i)) (v i) at h
  simpa only [metricRicciOperator_inner] using h

theorem metricRicciOperator_isPositive (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (metricRicciOperator D x).IsPositive := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  constructor
  · intro v w
    change g.inner x (metricRicciOperator D x v) w =
      g.inner x v (metricRicciOperator D x w)
    rw [g.symm x v, metricRicciOperator_inner, metricRicciOperator_inner]
    exact (hD.2.2.2.1 x v w v w).2.2.2
  · intro v
    change 0 ≤ g.inner x (metricRicciOperator D x v) v
    rw [metricRicciOperator_inner]
    exact hRic v

theorem ricciPartialTrace_nonneg (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) {k : ℕ} (hk : k ≤ n)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v) :
    0 ≤ ricciPartialTrace D k x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
  exact partialTrace_nonneg (hk.trans hdim.ge) (metricRicciOperator_isPositive D hD x hRic)

theorem ricciPartialTrace_eq_zero_iff (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) {k : ℕ} (hk : k ≤ n)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v) :
    ricciPartialTrace D k x = 0 ↔ k ≤ Module.finrank ℝ (metricRicciOperator D x).ker := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
  exact partialTrace_eq_zero_iff (hk.trans hdim.ge) (metricRicciOperator_isPositive D hD x hRic)



theorem ricci_movingReaction_nonneg (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 n) x, 0 ≤ D.curvatureTensor x v w v w)
    (v : TangentSpace (𝓡 n) x) :
    0 ≤ 2 * ∑ i, ∑ j,
      D.curvatureTensor x v (g.orthonormalBasis x i) v (g.orthonormalBasis x j) *
        D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let A := metricRicciOperator D x
  have hA : A.IsPositive := metricRicciOperator_isPositive D hD x
    (fun z => Finset.sum_nonneg fun i _ => hsec z (g.orthonormalBasis x i))
  have hlin : A.toLinearMap.IsPositive := hA
  let e := hlin.isSymmetric.eigenvectorBasis rfl
  let ev := hlin.isSymmetric.eigenvalues rfl
  have hdiag (i j) : D.ricci x (e i) (e j) = ev i * (if i = j then 1 else 0) := by
    rw [← metricRicciOperator_inner]
    change inner ℝ (A.toLinearMap (e i)) (e j) = _
    rw [hlin.isSymmetric.apply_eigenvectorBasis rfl]
    rw [real_inner_smul_left]
    change ev i * inner ℝ (e i) (e j) = _
    rw [e.inner_eq_ite]
  let C := D.curvatureTensor_bilinear_first_third x v v
  have hC (y z) : C y z = D.curvatureTensor x v y v z := by
    change D.curvatureTensor x y v z v = _
    rw [(hD.2.2.2.1 x y v z v).2.1, (hD.2.2.2.1 x z v y v).1,
      (hD.2.2.2.1 x z v v y).2.1, (hD.2.2.2.1 x v y z v).1, neg_neg]
  have hchange := bilinear_product_contraction_eq C (ricciBilinear D x)
    (g.orthonormalBasis x) e
  simp only [hC, ricciBilinear_apply] at hchange
  rw [hchange]
  apply mul_nonneg (by norm_num)
  simp_rw [hdiag]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hsec v (e i))
    (hlin.nonneg_eigenvalues rfl i)



theorem exists_ricci_partialTrace_spatial_support (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ (TangentSpace (𝓡 n) x)) :
    ∃ (U : Set M) (W : Fin k → (y : M) → TangentSpace (𝓡 n) y),
      IsOpen U ∧ x ∈ U ∧
      (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (W i)) U) ∧
      (∀ y ∈ U, ∀ i j, g.inner y (W i y) (W j y) = if i = j then 1 else 0) ∧
      (∑ i, D.ricci x (W i x) (W i x)) = ricciPartialTrace D k x ∧
      (∀ y ∈ U, ricciPartialTrace D k y ≤ ∑ i, D.ricci y (W i y) (W i y)) ∧
      (∑ i, D.tensorLaplacian D.ricciEvaluation x ![W i x, W i x]) =
        D.laplacian (fun y => ∑ i, D.ricci y (W i y) (W i y)) x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨v, hv, hmin⟩ := exists_ricci_minimizing_frame D x hk
  obtain ⟨r, Y, hr, hrU, hY, hinit, hpar, hfirst, hsecond, P, hP⟩ :=
    D.exists_radialParallelIsometries_with_jets x
  let U := LeviCivitaData.radialNeighborhood (n := n) x r
  let W : Fin k → (y : M) → TangentSpace (𝓡 n) y :=
    fun i => LeviCivitaData.fieldFromCenteredCoordinates x (Y (v i))
  have hU : IsOpen U := LeviCivitaData.isOpen_radialNeighborhood x r
  have hxU : x ∈ U := LeviCivitaData.mem_radialNeighborhood x hr
  have hWs (i) : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (W i)) U := by
    intro y hy
    exact (LeviCivitaData.contMDiffAt_fieldFromCenteredCoordinates x
      (hY (v i)).contDiffAt hy.1).contMDiffWithinAt
  have hpair (y) (hy : y ∈ U) (i j) :
      g.inner y (W i y) (W j y) = if i = j then 1 else 0 := by
    have heq := (P ⟨y, hy⟩).inner_map_map (v i) (v j)
    rw [hP, hP] at heq
    exact heq.trans (hv i j)
  refine ⟨U, W, hU, hxU, hWs, hpair, ?_,
    fun y hy => ricciPartialTrace_le D y (fun i => W i y) (hpair y hy), ?_⟩
  · simpa only [W, hinit] using hmin
  · have h := D.sum_tensorLaplacian_eq_laplacian_of_zero_jets
      (J := Fin k) (k := 2) (T := D.ricciEvaluation) hD.2.1
      (fun _ : Fin k => (1 : ℝ)) (fun i => ![W i, W i]) hU
      (by intro i j; fin_cases j <;> exact hWs i) hxU
      (by intro i j a; fin_cases j <;> exact hfirst (v i) a)
      (by intro i j a; fin_cases j <;> exact hsecond (v i) a)
    have hvec (i : Fin k) (y : M) :
        (fun j => ![W i, W i] j y) = ![W i y, W i y] := by
      ext j
      fin_cases j <;> rfl
    simpa only [one_mul, hvec, LeviCivitaData.ricciEvaluation,
      Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem ricciSharp_pairing_left (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    D.ricci x (ricciSharp D x v) w =
      ∑ i, D.ricci x v (g.orthonormalBasis x i) *
        D.ricci x (g.orthonormalBasis x i) w := by
  rw [← ricciBilinear_apply]
  simp only [ricciSharp, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, ricciBilinear_apply]

theorem ricciSharp_pairing_right (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    D.ricci x v (ricciSharp D x w) =
      ∑ i, D.ricci x w (g.orthonormalBasis x i) *
        D.ricci x v (g.orthonormalBasis x i) := by
  rw [← ricciBilinear_apply]
  simp only [ricciSharp, map_sum, map_smul, smul_eq_mul, ricciBilinear_apply]



theorem hasDerivAt_ricci_transport (hC : RicciFlowCurvatureTheory.{u})
    {a b : ℝ} (F : RicciFlow n M (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric b).toRiemannianMetric⟩
    ∀ {V : ℝ → TangentSpace (𝓡 n) x},
      HasDerivAt V (ricciSharp (F.connection t) x (V t)) t →
      HasDerivAt (fun s => (F.connection s).ricci x (V s) (V s))
        ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![V t, V t] +
          2 * ∑ i, ∑ j,
            (F.connection t).curvatureTensor x (V t)
              ((F.metric t).orthonormalBasis x i) (V t) ((F.metric t).orthonormalBasis x j) *
            (F.connection t).ricci x ((F.metric t).orthonormalBasis x i)
              ((F.metric t).orthonormalBasis x j)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  intro V hV
  let L (s : ℝ) : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (ricciBilinear (F.connection s) x)).toContinuousLinearMap
  have hL (s : ℝ) (v w : TangentSpace (𝓡 n) x) :
      L s v w = (F.connection s).ricci x v w := ricciBilinear_apply _ _ _ _
  have htime (v w : TangentSpace (𝓡 n) x) :=
    (hC.ricci_evolution n M (Icc a b) F t ⟨ht.1.le, ht.2.le⟩ x v w).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hd := hasDerivAt_bilinear_moving L
    (fun v w => (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![v, w] +
      (F.connection t).ricciReaction x v w)
    (fun v w => (htime v w).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => hL s v w)) hV
  simp only [hL, ricciSharp_pairing_left, ricciSharp_pairing_right] at hd
  have hsym (v w) := ((hC.tensor_calculus n M (F.metric t) (F.connection t)).2.2.2.1
    x v w v w).2.2.2
  apply hd.congr_deriv
  simp only [LeviCivitaData.ricciReaction, hsym (V t)]
  ring

theorem exists_ricci_frame_time_support (hC : RicciFlowCurvatureTheory.{u})
    {a b : ℝ} (hab : a < b) (F : RicciFlow n M (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M) {k : ℕ}
    (v : Fin k → TangentSpace (𝓡 n) x)
    (hv : ∀ i j, (F.metric t).inner x (v i) (v j) = if i = j then 1 else 0)
    (hsec : ∀ z w : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).curvatureTensor x z w z w) :
    ∃ (τ : ℝ → ℝ) (d : ℝ), HasDerivAt τ d t ∧
      τ t = ∑ i, (F.connection t).ricci x (v i) (v i) ∧
      (∀ᶠ s in 𝓝 t, ricciPartialTrace (F.connection s) k x ≤ τ s) ∧
      (∑ i, (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x
        ![v i, v i]) ≤ d := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  obtain ⟨U, _, hUd, hpair, hinv⟩ := exists_terminal_ricci_transport hC hab F x
  have htJ : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  let V (i : Fin k) (s : ℝ) := U s ((U t).inverse (v i))
  have hVt (i : Fin k) : V i t = v i := (hinv t htJ).self_apply_inverse _
  have hVpair (s) (hs : s ∈ Icc a b) (i j) :
      (F.metric s).inner x (V i s) (V j s) = if i = j then 1 else 0 := by
    have h := (hpair s hs ((U t).inverse (v i)) ((U t).inverse (v j))).trans
      (hpair t htJ ((U t).inverse (v i)) ((U t).inverse (v j))).symm
    change (F.metric s).inner x (V i s) (V j s) =
      (F.metric t).inner x (V i t) (V j t) at h
    simpa only [hVt, hv] using h
  let τ (s : ℝ) := ∑ i, (F.connection s).ricci x (V i s) (V i s)
  let d := ∑ i, ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x
      ![v i, v i] + 2 * ∑ p, ∑ q,
        (F.connection t).curvatureTensor x (v i) ((F.metric t).orthonormalBasis x p)
          (v i) ((F.metric t).orthonormalBasis x q) *
        (F.connection t).ricci x ((F.metric t).orthonormalBasis x p)
          ((F.metric t).orthonormalBasis x q))
  refine ⟨τ, d, ?_, ?_, ?_, ?_⟩
  · have hd (i : Fin k) := hasDerivAt_ricci_transport hC F ht x (V := V i)
      ((hUd t htJ ((U t).inverse (v i))).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    have hfun : (∑ i, fun s => (F.connection s).ricci x (V i s) (V i s)) = τ := by
      funext s
      simp [τ]
    have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => hd i)
    rw [hfun] at hsum
    simpa only [d, hVt] using hsum
  · simp only [τ, hVt]
  · filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact ricciPartialTrace_le (F.connection s) x (fun i => V i s) (hVpair s hs)
  · exact Finset.sum_le_sum fun i _ => le_add_of_nonneg_right
      (ricci_movingReaction_nonneg (F.connection t)
        (hC.tensor_calculus n M (F.metric t) (F.connection t)) x hsec (v i))



theorem ricciPartialTrace_heatLowerContacts [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b)) {k : ℕ} (hk : k ≤ n)
    (hsec : ∀ t ∈ Ioo a b, ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).curvatureTensor x v w v w) :
    MaximumPrinciple.HeatLowerContacts F.connection univ (Ioo a b)
      (fun x t => ricciPartialTrace (F.connection t) k x) := by
  intro x _ t ht ψ W hW hxW hψ hψeq hψle
  let D := F.connection t
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hkx : k ≤ Module.finrank ℝ (TangentSpace (𝓡 n) x) := by
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
    omega
  obtain ⟨U, Y, hU, hxU, hYs, hYpair, hYeq, hYge, hYlap⟩ :=
    exists_ricci_partialTrace_spatial_support D hD x hkx
  obtain ⟨τ, d, hτd, hτeq, hτge, hdlap⟩ := exists_ricci_frame_time_support hC hab F ht x
    (fun i => Y i x) (hYpair x hxU) (hsec t ht x)
  refine ⟨τ, d, hτd, hτeq.trans hYeq, hτge, ?_⟩
  let σ (y : M) := ∑ i, D.ricci y (Y i y) (Y i y)
  have hσ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U := by
    intro y hy
    exact ContMDiffWithinAt.sum fun i _ =>
      hD.2.1.2 U hU (fun _ : Fin 2 => Y i) (fun _ => hYs i) y hy
  have hmax : IsLocalMax (fun y => ψ y - σ y) x := by
    filter_upwards [hU.mem_nhds hxU, hψle] with y hy hyle
    change ψ y - σ y ≤ ψ x - σ x
    have hx : ψ x = σ x := hψeq.trans hYeq.symm
    rw [hx, sub_self]
    exact sub_nonpos.mpr (hyle.trans (hYge y hy))
  have hsub := D.laplacian_nonpos_of_isLocalMaxOn_open (hW.inter hU)
    ((hψ.mono inter_subset_left).sub (hσ.mono inter_subset_right)) ⟨hxW, hxU⟩ hmax
  rw [LeviCivitaData.Dirichlet.laplacian_sub_on D (hW.inter hU)
    (hψ.mono inter_subset_left) (hσ.mono inter_subset_right) ⟨hxW, hxU⟩] at hsub
  have hσlap : D.laplacian σ x ≤ d := by rw [← hYlap]; exact hdlap
  linarith

end PoincareConjecture.RicciFlow.Splitting
