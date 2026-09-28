
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.GeometricPreservation.Transport












noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle InnerProductSpace
open Poincare.HamiltonIvey

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem ricciComplementTensor_pullback_mem_tensorRegion_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hn : Module.finrank ℝ E = 3)
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (e : E ≃ₗ[ℝ] TangentSpace (𝓡 3) x)
    (he : ∀ v w, g.inner x (e v) (e w) = inner ℝ v w)
    {t : ℝ} (ht : 0 ≤ t) :
    TensorFiber.toMultilinear.symm
        ((TensorFiber.toMultilinear (D.ricciComplementTensor hD x)).compLinearMap
          (fun _ => e.toLinearMap)) ∈ tensorRegion hn t ↔
      (D.scalarCurvature x / 2, D.negativeCurvaturePart x) ∈ scalarRegion t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  have hm : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  let L : E ≃ₗᵢ[ℝ] TangentSpace (𝓡 3) x := e.isometryOfInner he
  have h := tensorRegion_transport_equiv_iff hm hn L.symm ht
    (D.ricciComplementTensor hD x)
  exact h.trans (D.ricciComplementTensor_mem_tensorRegion_iff hD x hm ht)

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow.Frame

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance



def transportedRicciComplementTensor (F : RicciFlow 3 M (Ico a b))
    (hC : RicciFlowCurvatureTheory.{u}) (t : ℝ) (x : M) :
    TensorFiber (TangentSpace (𝓡 3) x) 2 :=
  TensorFiber.toMultilinear.symm
    ((TensorFiber.toMultilinear ((F.connection t).ricciComplementTensor
      (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x)).compLinearMap
        (fun _ => (canonicalTransport F t x).toLinearMap))

@[simp] theorem transportedRicciComplementTensor_apply
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (x : M) (v : Fin 2 → TangentSpace (𝓡 3) x) :
    transportedRicciComplementTensor F hC t x v =
      (F.connection t).ricciComplementEvaluation x
        (fun i => canonicalTransport F t x (v i)) := by
  exact (F.connection t).ricciComplementTensor_apply _ x _

@[simp] theorem transportedRicciComplementTensor_initial
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (hab : a < b) (x : M) :
    transportedRicciComplementTensor F hC a x =
      (F.connection a).ricciComplementTensor
        (hC.tensor_calculus 3 M (F.metric a) (F.connection a)) x := by
  apply TensorFiber.ext
  intro v
  simp only [transportedRicciComplementTensor_apply, canonicalTransport_initial F hab,
    ContinuousLinearMap.id_apply, LeviCivitaData.ricciComplementTensor_apply]


theorem transportedRicciComplementTensor_isSmooth
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    {t : ℝ} (ht : t ∈ Ico a b) :
    IsSmoothCovariantTensor (fun x v => transportedRicciComplementTensor F hC t x v) := by
  have hT := (F.connection t).isSmoothCovariantTensor_ricciComplementEvaluation
    (hC.tensor_calculus 3 M (F.metric t) (F.connection t))
  constructor
  · intro x
    exact ⟨TensorFiber.toMultilinear (transportedRicciComplementTensor F hC t x),
      fun _ => rfl⟩
  · intro O hO Y hY
    simpa only [transportedRicciComplementTensor_apply] using
      hT.2 O hO (fun i y => canonicalTransport F t y (Y i y))
        (fun i => (canonicalTransport_contMDiff_space F ht).contMDiffOn.clm_bundle_apply (hY i))



theorem transportedRicciComplementTensor_mem_tensorRegion_iff [T2Space M]
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (hab : a < b) (x : M) (hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3)
    {t : ℝ} (ht : t ∈ Ico a b) {s : ℝ} (hs : 0 ≤ s) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    transportedRicciComplementTensor F hC t x ∈ tensorRegion hn s ↔
      ((F.connection t).scalarCurvature x / 2,
        (F.connection t).negativeCurvaturePart x) ∈ scalarRegion s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  exact (F.connection t).ricciComplementTensor_pullback_mem_tensorRegion_iff hn
    (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x
    (orthonormalTransport F t x).toLinearEquiv
    (canonicalTransport_pairing F hab ht x) hs



theorem scaled_transportedRicciComplementTensor_mem_iff [T2Space M]
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (ha : 0 ≤ a) (hab : a < b) (x : M)
    (hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3)
    {t : ℝ} (ht : t ∈ Ico a b) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    (1 + t) • transportedRicciComplementTensor F hC t x ∈ tensorRegion hn 0 ↔
      ((F.connection t).scalarCurvature x / 2,
        (F.connection t).negativeCurvaturePart x) ∈ scalarRegion t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  rw [← tensorRegion_scale_iff hn (ha.trans ht.1)]
  exact transportedRicciComplementTensor_mem_tensorRegion_iff F hC hab x hn ht
    (ha.trans ht.1)



theorem scaled_transportedRicciComplementTensor_initial_mem [T2Space M]
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (ha : 0 ≤ a) (hab : a < b) (x : M)
    (hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3)
    (htrace : -6 / (1 + 4 * a) ≤ (F.connection a).scalarCurvature x)
    (hlog : 0 < (F.connection a).negativeCurvaturePart x →
      2 * (F.connection a).negativeCurvaturePart x *
        (Real.log ((F.connection a).negativeCurvaturePart x) + Real.log (1 + a) - 3) ≤
          (F.connection a).scalarCurvature x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    (1 + a) • transportedRicciComplementTensor F hC a x ∈ tensorRegion hn 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  rw [transportedRicciComplementTensor_initial F hC hab]
  exact (F.connection a).scaled_ricciComplementTensor_mem_tensorRegion_of_pinching
    (hC.tensor_calculus 3 M (F.metric a) (F.connection a)) x hn ha htrace hlog



theorem logarithmic_pinching_of_scaled_transportedRicciComplementTensor_mem [T2Space M]
    (F : RicciFlow 3 M (Ico a b)) (hC : RicciFlowCurvatureTheory.{u})
    (ha : 0 ≤ a) (hab : a < b) (x : M)
    (hn : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3)
    {t : ℝ} (ht : t ∈ Ico a b) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    (1 + t) • transportedRicciComplementTensor F hC t x ∈ tensorRegion hn 0 →
      0 < (F.connection t).negativeCurvaturePart x →
        2 * (F.connection t).negativeCurvaturePart x *
          (Real.log ((F.connection t).negativeCurvaturePart x) + Real.log (1 + t) - 3) ≤
            (F.connection t).scalarCurvature x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  intro hmem
  have hscalar := (scaled_transportedRicciComplementTensor_mem_iff F hC ha hab x hn ht).mp
    hmem
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have hD := hC.tensor_calculus 3 M (F.metric t) (F.connection t)
  apply (F.connection t).logarithmic_pinching_of_scaled_ricciComplementTensor_mem
    hD x hn (ha.trans ht.1)
  apply (tensorRegion_scale_iff hn (ha.trans ht.1) _).mp
  exact ((F.connection t).ricciComplementTensor_mem_tensorRegion_iff hD x hn
    (ha.trans ht.1)).mpr hscalar

end PoincareConjecture.RicciFlow.Frame
