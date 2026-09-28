import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.MovingCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.GeometricPreservation.CurvaturePDE












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle Filter
open PoincareConjecture.RicciFlow PoincareConjecture.RicciFlow.Frame
open Poincare.Geometry.Curvature.Operator Poincare.HamiltonIvey
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.AncientKappaRoundness

private theorem hasDerivAt_of_tensor_components
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ E) {k : ℕ}
    {T : ℝ → TensorFiber E k} {D : TensorFiber E k} {t : ℝ}
    (h : ∀ v : Fin k → ι,
      HasDerivAt (fun s => T s (fun i => e (v i))) (D (fun i => e (v i))) t) :
    HasDerivAt T D t := by
  let C : TensorFiber E k →ₗ[ℝ] ((Fin k → ι) → ℝ) :=
    { toFun := fun S v => S (fun i => e (v i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hC : Function.Injective C := by
    intro S R heq
    apply TensorFiber.toMultilinear.injective
    apply Module.Basis.ext_multilinear (fun _ => e)
    intro v
    exact congrFun heq v
  obtain ⟨L, hL⟩ := C.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  have hLC (S : TensorFiber E k) : L (C S) = S :=
    congrArg (fun f : TensorFiber E k →ₗ[ℝ] TensorFiber E k => f S) hL
  have hd : HasDerivAt (fun s => C (T s)) (C D) t := hasDerivAt_pi.mpr h
  have hd' := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => L (C (T s))) (L (C D)) t at hd'
  simpa only [hLC] using hd'

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

private theorem exists_transport_orthonormalBasis
    (F : RicciFlow 3 M (Ico a b)) (hab : a < b)
    {t : ℝ} (ht : t ∈ Ico a b) (x : M)
    (e : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (he : ∀ i j, (F.metric a).inner x (e i) (e j) = if i = j then 1 else 0) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ∃ q : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
      ∀ i, q i = canonicalTransport F t x (e i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let c := e.map (orthonormalTransport F t x).toLinearEquiv
  have hc : Orthonormal ℝ c := by
    rw [orthonormal_iff_ite]
    intro i j
    change (F.metric t).inner x (canonicalTransport F t x (e i))
      (canonicalTransport F t x (e j)) = _
    rw [canonicalTransport_pairing F hab ht, he]
  exact ⟨c.toOrthonormalBasis hc, fun i => by
    rw [Module.Basis.coe_toOrthonormalBasis]
    rfl⟩

private theorem complement_eq_cyclic
    [T2Space M] (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (hab : a < b) {t : ℝ} (ht : t ∈ Ico a b) (x : M)
    (e : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (he : ∀ i j, (F.metric a).inner x (e i) (e j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    (F.connection t).ricciComplementEvaluation x
      ![canonicalTransport F t x (e i), canonicalTransport F t x (e j)] =
      (F.connection t).curvatureTensor x
        (canonicalTransport F t x (e (pairFirst i)))
        (canonicalTransport F t x (e (pairSecond i)))
        (canonicalTransport F t x (e (pairFirst j)))
        (canonicalTransport F t x (e (pairSecond j))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  obtain ⟨q, hq⟩ := exists_transport_orthonormalBasis F hab ht x e he
  have h := (F.connection t).ricciComplementTensor_apply_orthonormalBasis
    (hcalculus t) x q i j
  simpa only [LeviCivitaData.ricciComplementTensor_apply, curvatureMatrix, hq] using h

private theorem tensorReaction_pullback
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {g : RiemannianMetric 3 M} (x : M)
    (e : E ≃ₗ[ℝ] TangentSpace (𝓡 3) x)
    (he : ∀ v w, g.inner x (e v) (e w) = inner ℝ v w)
    (T : TensorFiber (TangentSpace (𝓡 3) x) 2) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    tensorReaction (TensorFiber.toMultilinear.symm
      ((TensorFiber.toMultilinear T).compLinearMap (fun _ => e.toLinearMap))) =
      TensorFiber.toMultilinear.symm
        ((TensorFiber.toMultilinear (tensorReaction T)).compLinearMap
          (fun _ => e.toLinearMap)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact tensorReaction_transport (e.isometryOfInner he).symm T

private theorem complement_components_evolution [T2Space M]
    (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (hevolution : ∀ t ∈ Ico a b, ∀ x : M,
      ∀ u v w z : TangentSpace (𝓡 3) x,
      HasDerivWithinAt (fun s => (F.connection s).curvatureTensor x u v w z)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x ![u, v, w, z] +
          (F.connection t).curvatureReaction x u v w z) (Ico a b) t)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M)
    (e : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (he : ∀ i j, (F.metric a).inner x (e i) (e j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    HasDerivAt
      (fun s => (F.connection s).ricciComplementEvaluation x
        ![canonicalTransport F s x (e i), canonicalTransport F s x (e j)])
      ((F.connection t).tensorLaplacian (F.connection t).ricciComplementEvaluation x
        ![canonicalTransport F t x (e i), canonicalTransport F t x (e j)] +
        tensorReaction ((F.connection t).ricciComplementTensor (hcalculus t) x)
          ![canonicalTransport F t x (e i), canonicalTransport F t x (e j)]) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  obtain ⟨q, hq⟩ := exists_transport_orthonormalBasis F (ht.1.trans ht.2)
    ⟨ht.1.le, ht.2⟩ x e he
  have hL := (F.connection t).tensorLaplacian_ricciComplement_apply_orthonormalBasis
    (hcalculus t) x q i j
  have hR := (F.connection t).tensorReaction_ricciComplementTensor_eq_curvatureB
    (hcalculus t) x q i j
  simp only [hq] at hL hR
  rw [hR, hL]
  apply (canonicalTransport_hasDerivAt_curvature_of_applied F hcalculus hevolution ht x
    (e (pairFirst i)) (e (pairSecond i)) (e (pairFirst j))
    (e (pairSecond j))).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact complement_eq_cyclic F hcalculus (ht.1.trans ht.2) ⟨hs.1.le, hs.2⟩ x e he i j


def transportedRicciComplement (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus) (t : ℝ) (x : M) :
    TensorFiber (TangentSpace (𝓡 3) x) 2 :=
  TensorFiber.toMultilinear.symm
    ((TensorFiber.toMultilinear ((F.connection t).ricciComplementTensor (hcalculus t) x)).compLinearMap
      (fun _ => (canonicalTransport F t x).toLinearMap))

@[simp] theorem transportedRicciComplement_apply (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (t : ℝ) (x : M) (v : Fin 2 → TangentSpace (𝓡 3) x) :
    transportedRicciComplement F hcalculus t x v =
      (F.connection t).ricciComplementEvaluation x (fun i => canonicalTransport F t x (v i)) :=
  (F.connection t).ricciComplementTensor_apply (hcalculus t) x _


def transportedRicciComplementDiffusion (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus) (t : ℝ) (x : M) :
    TensorFiber (TangentSpace (𝓡 3) x) 2 :=
  TensorFiber.toMultilinear.symm
    ((TensorFiber.toMultilinear ((F.connection t).tensorLaplacianFiber
      ((F.connection t).isSmoothCovariantTensor_ricciComplementEvaluation (hcalculus t)) x)).compLinearMap
      (fun _ => (canonicalTransport F t x).toLinearMap))

@[simp] theorem transportedRicciComplementDiffusion_apply
    (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (t : ℝ) (x : M) (v : Fin 2 → TangentSpace (𝓡 3) x) :
    transportedRicciComplementDiffusion F hcalculus t x v =
      (F.connection t).tensorLaplacian (F.connection t).ricciComplementEvaluation x
        (fun i => canonicalTransport F t x (v i)) :=
  (F.connection t).tensorLaplacianFiber_apply _ x _



theorem hasDerivAt_transportedRicciComplement [T2Space M]
    (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (hevolution : ∀ t ∈ Ico a b, ∀ x : M,
      ∀ u v w z : TangentSpace (𝓡 3) x,
      HasDerivWithinAt (fun s => (F.connection s).curvatureTensor x u v w z)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x ![u, v, w, z] +
          (F.connection t).curvatureReaction x u v w z) (Ico a b) t)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    HasDerivAt (fun s => transportedRicciComplement F hcalculus s x)
      (transportedRicciComplementDiffusion F hcalculus t x +
        tensorReaction (transportedRicciComplement F hcalculus t x)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  have hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  let e := (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) x)).reindex (finCongr hn)
  have he (i j : Fin 3) : (F.metric a).inner x (e i) (e j) =
      if i = j then 1 else 0 := e.inner_eq_ite i j
  apply hasDerivAt_of_tensor_components e.toBasis
  intro v
  have htuple : (fun i => e.toBasis (v i)) = ![e (v 0), e (v 1)] := by
    ext i
    fin_cases i <;> rfl
  simp only [htuple, TensorFiber.add_apply, transportedRicciComplementDiffusion_apply]
  have hcomponent := complement_components_evolution F hcalculus hevolution ht x e.toBasis he
    (v 0) (v 1)
  have hreaction := tensorReaction_pullback x (orthonormalTransport F t x).toLinearEquiv
    (canonicalTransport_pairing F (ht.1.trans ht.2) ⟨ht.1.le, ht.2⟩ x)
    ((F.connection t).ricciComplementTensor (hcalculus t) x)
  change tensorReaction (transportedRicciComplement F hcalculus t x) = _ at hreaction
  rw [hreaction]
  simp only [LinearEquiv.apply_symm_apply, MultilinearMap.compLinearMap_apply]
  convert hcomponent using 1
  · funext s
    exact transportedRicciComplement_apply F hcalculus s x _
  · congr 2 <;> ext i <;> fin_cases i <;> rfl

end PoincareConjecture.AncientKappaRoundness
