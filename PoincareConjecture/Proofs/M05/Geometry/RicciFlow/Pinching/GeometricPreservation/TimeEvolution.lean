import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.CurvaturePDE
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.TransportedCarrier

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology
open Poincare.HamiltonIvey
open PoincareConjecture.TensorFiber

universe u

namespace PoincareConjecture.TensorFiber

private theorem hasDerivAt_of_components
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
    apply toMultilinear.injective
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

end PoincareConjecture.TensorFiber

namespace PoincareConjecture.RicciFlow.Frame

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

def transportedRicciComplementLaplacian (F : RicciFlow 3 M (Ico a b))
    (hC : RicciFlowCurvatureTheory.{u}) (t : ℝ) (x : M) :
    TensorFiber (TangentSpace (𝓡 3) x) 2 :=
  TensorFiber.toMultilinear.symm
    ((TensorFiber.toMultilinear ((F.connection t).tensorLaplacianFiber
      ((F.connection t).isSmoothCovariantTensor_ricciComplementEvaluation
        (hC.tensor_calculus 3 M (F.metric t) (F.connection t))) x)).compLinearMap
      (fun _ => (canonicalTransport F t x).toLinearMap))

@[simp] theorem transportedRicciComplementLaplacian_apply
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (x : M) (v : Fin 2 → TangentSpace (𝓡 3) x) :
    transportedRicciComplementLaplacian F hC t x v =
      (F.connection t).tensorLaplacian (F.connection t).ricciComplementEvaluation x
        (fun i => canonicalTransport F t x (v i)) :=
  (F.connection t).tensorLaplacianFiber_apply _ x _

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
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact tensorReaction_transport (e.isometryOfInner he).symm T

private theorem tensorReaction_smul (c : ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : TensorFiber E 2) :
    tensorReaction (c • T) = c ^ 2 • tensorReaction T := by
  obtain ⟨A, rfl⟩ := (operatorTensorEquiv (E := E)).surjective T
  have hsmul : c • operatorTensor A.toLinearMap = operatorTensor (c • A.toLinearMap) := by
    apply TensorFiber.ext
    intro v
    simp [operatorTensor, LinearMap.smul_apply, inner_smul_right]
  rw [operatorTensorEquiv_apply, hsmul,
    tensorReaction_operatorTensor, tensorReaction_operatorTensor,
    endomorphismReaction_smul]
  apply TensorFiber.ext
  intro v
  simp [operatorTensor, LinearMap.smul_apply, inner_smul_right]

theorem hasDerivAt_transportedRicciComplementTensor [T2Space M]
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    HasDerivAt (fun s => transportedRicciComplementTensor F hC s x)
      (transportedRicciComplementLaplacian F hC t x +
        tensorReaction (transportedRicciComplementTensor F hC t x)) t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  have hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  let e := (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) x)).reindex (finCongr hn)
  apply TensorFiber.hasDerivAt_of_components e.toBasis
  intro v
  have he (i j : Fin 3) : (F.metric a).inner x (e i) (e j) =
      if i = j then 1 else 0 := e.inner_eq_ite i j
  have hd := canonicalTransport_hasDerivAt_ricciComplement hC F ht x e.toBasis he
    (v 0) (v 1)
  have hr := tensorReaction_pullback x (orthonormalTransport F t x).toLinearEquiv
    (canonicalTransport_pairing F (ht.1.trans ht.2) ⟨ht.1.le, ht.2⟩ x)
    ((F.connection t).ricciComplementTensor
      (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x)
  have htuple : (fun i => e (v i)) = ![e (v 0), e (v 1)] := by
    ext i
    fin_cases i <;> rfl
  rw [transportedTensorLaplacian_pullback F ⟨ht.1.le, ht.2⟩
    ((F.connection t).isSmoothCovariantTensor_ricciComplementEvaluation
      (hC.tensor_calculus 3 M (F.metric t) (F.connection t)))] at hd
  change tensorReaction (transportedRicciComplementTensor F hC t x) = _ at hr
  simp only [OrthonormalBasis.coe_toBasis, htuple, TensorFiber.add_apply, hr,
    transportedRicciComplementLaplacian_apply]
  convert hd using 1
  · funext s
    exact transportedRicciComplementTensor_apply F hC s x _
  · congr 1

theorem hasDerivAt_scaled_transportedRicciComplementTensor [T2Space M]
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (ha : 0 ≤ a) {t : ℝ} (ht : t ∈ Ioo a b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    HasDerivAt (fun s => (1 + s) • transportedRicciComplementTensor F hC s x)
      ((1 + t) • transportedRicciComplementLaplacian F hC t x +
        scaledTensorReaction t ((1 + t) • transportedRicciComplementTensor F hC t x)) t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  have hne : 1 + t ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hd := ((hasDerivAt_id t).const_add 1).smul
    (hasDerivAt_transportedRicciComplementTensor F hC ht x)
  convert hd using 1 <;> try rfl
  simp only [scaledTensorReaction, tensorReaction_smul, smul_add, smul_smul, one_smul, id_eq]
  rw [inv_mul_cancel₀ hne, one_smul,
    show (1 + t)⁻¹ * (1 + t) ^ 2 = 1 + t by field_simp]
  abel

end PoincareConjecture.RicciFlow.Frame
