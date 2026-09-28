import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.CurvatureCarrier
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.TensorRegion
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Algebra
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.TraceRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators
open Poincare.Geometry.Curvature.Operator Poincare.HamiltonIvey

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private instance ricciComplementFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
  unfold TangentSpace
  infer_instance

noncomputable def ricciComplementEvaluation (D : LeviCivitaData g) :
    CovariantTensorEvaluation n M 2 :=
  fun x v => (D.scalarCurvature x / 2) * g.inner x (v 0) (v 1) -
    D.ricci x (v 0) (v 1)

theorem isSmoothCovariantTensor_ricciComplementEvaluation
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) :
    IsSmoothCovariantTensor D.ricciComplementEvaluation := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  have hscalar : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ D.scalarCurvature := by
    change ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x => ∑ i, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
    have hs := (hD.2.1.tensorTrace (g := g)).2 Set.univ isOpen_univ
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    simpa [contMDiffOn_univ, RiemannianMetric.tensorTrace, LeviCivitaData.scalarCurvature,
      ricciEvaluation] using hs
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hD.2.1.1 x
    refine ⟨(D.scalarCurvature x / 2) •
      TensorFiber.toMultilinear (TensorFiber.operatorTensor (LinearMap.id :
        TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x)) - A, ?_⟩
    intro v
    change _ = (D.scalarCurvature x / 2) * inner ℝ (v 0) (v 1) - A v
    exact congrArg ((D.scalarCurvature x / 2) * g.inner x (v 0) (v 1) - ·) (hA v)
  · intro U hU X hX
    exact ((hscalar.contMDiffOn.div_const 2).mul
      ((hX 0).inner_bundle (hX 1))).sub (hD.2.1.2 U hU X hX)

noncomputable def ricciComplementTensor (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    TensorFiber (TangentSpace (𝓡 n) x) 2 :=
  TensorFiber.toMultilinear.symm
    (Classical.choose ((D.isSmoothCovariantTensor_ricciComplementEvaluation hD).1 x))

@[simp] theorem ricciComplementTensor_apply (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (v : Fin 2 → TangentSpace (𝓡 n) x) :
    D.ricciComplementTensor hD x v = D.ricciComplementEvaluation x v :=
  (Classical.choose_spec
    ((D.isSmoothCovariantTensor_ricciComplementEvaluation hD).1 x) v).symm

theorem ricciComplementEvaluation_symm (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.ricciComplementEvaluation x ![v, w] =
      D.ricciComplementEvaluation x ![w, v] := by
  change _ * g.inner x v w - D.ricci x v w =
    _ * g.inner x w v - D.ricci x w v
  rw [g.symm, (hD.2.2.2.1 x v w v w).2.2.2]

end PoincareConjecture.LeviCivitaData

namespace Poincare.Geometry.Curvature.Operator

private theorem curvatureMatrix_eq_trace_sub_ricci
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (hpair : ∀ i j k l, R i j k l = R k l i j) (i j : Fin 3) :
    curvatureMatrix R i j =
      Matrix.trace (curvatureMatrix R) * (if i = j then 1 else 0) -
        ∑ p, R i p j p := by
  have hdiagFirst (i k l) : R i i k l = 0 := by linarith [hfirst i i k l]
  have hdiagLast (i j k) : R i j k k = 0 := by linarith [hlast i j k k]
  have hswap (i j) : R i j i j = R j i j i := by
    rw [hfirst, hlast j i i j, neg_neg]
  fin_cases i <;> fin_cases j <;>
    simp [curvatureMatrix, Matrix.trace, Fin.sum_univ_succ, pairFirst, pairSecond,
      hdiagFirst, hdiagLast]
  · linarith [hswap 0 2]
  · linarith [hfirst 0 2 1 2, hpair 2 0 1 2]
  · linarith [hlast 0 1 2 1, hpair 0 1 1 2]
  · linarith [hlast 1 2 0 2, hpair 1 2 2 0]
  · linarith [hswap 1 0]
  · linarith [hfirst 1 0 2 0, hpair 0 1 2 0]
  · linarith [hfirst 2 1 0 1, hpair 1 2 0 1]
  · linarith [hlast 2 0 1 0, hpair 2 0 0 1]
  · linarith [hswap 2 1]

end Poincare.Geometry.Curvature.Operator

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private instance ricciComplementThreeFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

private theorem complement_curvature_skew_first (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) (u v w z : TangentSpace (𝓡 3) x) :
    D.curvatureTensor x u v w z = -D.curvatureTensor x v u w z := by
  rw [(hD.2.2.2.1 x u v w z).2.1, (hD.2.2.2.1 x w z u v).1,
    (hD.2.2.2.1 x w z v u).2.1]

theorem ricci_eq_sum_orthonormalBasis [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
      (u v : TangentSpace (𝓡 3) x),
      D.ricci x u v = ∑ p, D.curvatureTensor x u (b p) v (b p) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b u v
  have hswap (a c : TangentSpace (𝓡 3) x) :
      D.curvatureTensor x u a v c = D.curvatureTensor x a u c v := by
    rw [complement_curvature_skew_first D hD x,
      (hD.2.2.2.1 x a u v c).1, neg_neg]
  simp only [ricci, hswap]
  exact bilinear_sum_orthonormalBasis_eq
    (D.curvatureTensor_bilinear_first_third x u v) (g.orthonormalBasis x) b

theorem ricciComplementTensor_apply_orthonormalBasis [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x)) (i j : Fin 3),
      D.ricciComplementTensor hD x ![b i, b j] =
        curvatureMatrix (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)) i j := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b i j
  rw [ricciComplementTensor_apply]
  change (D.scalarCurvature x / 2) * inner ℝ (b i) (b j) - D.ricci x (b i) (b j) = _
  rw [b.inner_eq_ite, D.ricci_eq_sum_orthonormalBasis hD x b,
    D.scalarCurvature_eq_twice_trace_curvatureOperator hD x b,
    curvatureOperator_trace]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  exact (curvatureMatrix_eq_trace_sub_ricci _
    (fun i j k l => complement_curvature_skew_first D hD x (b i) (b j) (b k) (b l))
    (fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).1)
    (fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1) i j).symm

theorem ricciComplementTensor_eq_transport_operatorTensor [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
      D.ricciComplementTensor hD x = TensorFiber.transport b.repr.symm 2
        (TensorFiber.operatorTensor (curvatureOperator
          (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b
  apply TensorFiber.toMultilinear.injective
  apply Module.Basis.ext_multilinear (fun _ => b.toBasis)
  intro v
  have hv : (fun i => b.toBasis (v i)) = ![b (v 0), b (v 1)] := by
    ext i; fin_cases i <;> rfl
  simp only [TensorFiber.toMultilinear_apply, hv]
  rw [D.ricciComplementTensor_apply_orthonormalBasis hD x b]
  simp [TensorFiber.transport_apply, TensorFiber.operatorTensor,
    OrthonormalBasis.repr_self, curvatureOperator, Matrix.toLpLin_apply,
    EuclideanSpace.inner_single_left, Matrix.mulVec_single, Matrix.col]

theorem ricciComplementTensor_mem_tensorRegion_iff [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3)
    {t : ℝ} (ht : 0 ≤ t) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    D.ricciComplementTensor hD x ∈ tensorRegion hn t ↔
      (D.scalarCurvature x / 2, D.negativeCurvaturePart x) ∈ scalarRegion t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := (g.orthonormalBasis x).reindex (finCongr hn)
  rw [D.ricciComplementTensor_eq_transport_operatorTensor hD x b,
    tensorRegion_transport_equiv_iff (by simp) hn b.repr.symm ht,
    operatorTensor_mem_tensorRegion]
  exact D.curvatureOperator_mem_region_iff hD x t b

theorem scaled_ricciComplementTensor_mem_tensorRegion_of_pinching [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3)
    {t : ℝ} (ht : 0 ≤ t)
    (htrace : -6 / (1 + 4 * t) ≤ D.scalarCurvature x)
    (hlog : 0 < D.negativeCurvaturePart x →
      2 * D.negativeCurvaturePart x *
        (Real.log (D.negativeCurvaturePart x) + Real.log (1 + t) - 3) ≤
          D.scalarCurvature x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (1 + t) • D.ricciComplementTensor hD x ∈ tensorRegion hn 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply (tensorRegion_scale_iff hn ht _).mp
  apply (D.ricciComplementTensor_mem_tensorRegion_iff hD x hn ht).mpr
  apply PoincareConjecture.initial_scalar_region_of_pinching ht
  · nlinarith [htrace]
  · intro hX
    nlinarith [hlog hX]

theorem logarithmic_pinching_of_scaled_ricciComplementTensor_mem [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3)
    {t : ℝ} (ht : 0 ≤ t) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (1 + t) • D.ricciComplementTensor hD x ∈ tensorRegion hn 0 →
      0 < D.negativeCurvaturePart x →
        2 * D.negativeCurvaturePart x *
          (Real.log (D.negativeCurvaturePart x) + Real.log (1 + t) - 3) ≤
            D.scalarCurvature x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro hmem
  let b := (g.orthonormalBasis x).reindex (finCongr hn)
  apply D.logarithmic_pinching_of_scaled_curvatureOperator_mem hD x ht
    b
  apply (region_scale_iff _ ht _).mp
  apply (D.curvatureOperator_mem_region_iff hD x t b).mpr
  exact (D.ricciComplementTensor_mem_tensorRegion_iff hD x hn ht).mp
    ((tensorRegion_scale_iff hn ht _).mpr hmem)

end PoincareConjecture.LeviCivitaData
