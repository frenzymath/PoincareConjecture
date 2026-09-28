import PoincareConjecture.Proofs.M34.Mathlib.NeckChartDerivative
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckBilinearJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {J : Set ℝ} {L : BlowupLimitFlow.{u} J}

private local instance : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance : ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold



theorem blowupCoordinateBilinear_apply
    {G : GeneralizedRicciFlowData.{u}} {origin scale : ℝ} {K : Set ℝ}
    {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder G L.sliceCarrier origin scale K U)
    (q : L.sliceCarrier.carrier) {s : ℝ} (hs : s ∈ K) (y v w : E₃) :
    blowupCoordinateBilinear e q s y v w =
      e.pullbackInner s hs ((extChartAt (𝓡 3) q).symm y)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y v)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y w) := by
  let c := extChartAt (𝓡 3) q
  let f := e.forward s hs
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (f (c.symm y))) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (f (c.symm y))) := by
    unfold TangentSpace
    infer_instance
  let A : E₃ →L[ℝ] TangentSpace (𝓡 3) (f (c.symm y)) :=
    (mfderiv (𝓡 3) (𝓡 3) f (c.symm y)).comp
    (mfderiv (𝓡 3) (𝓡 3) c.symm y)
  let B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := scale •
    ((G.metric (origin + s / scale)).inner (f (c.symm y))).bilinearComp A A
  have hB : blowupCoordinateBilinear e q s y = B := by
    have hc : (fun a b => blowupPullbackCoefficient e q a b (s, y)) =
        (fun a b => B (PiLp.single 2 a 1) (PiLp.single 2 b 1)) := by
      funext a b
      simp only [blowupPullbackCoefficient, dif_pos hs, EuclideanSpace.basisFun_apply]
      rfl
    exact (congrArg (ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := 2) (q := 2) (𝕜 := ℝ)) hc).trans
        (ContinuousLinearMap.piLpBilinearFromCoordinates_evaluations B)
  rw [hB]
  rfl



theorem limitCoordinateBilinear_apply (q : L.sliceCarrier.carrier) (s : ℝ) (y v w : E₃) :
    limitCoordinateBilinear L q s y v w =
      (L.flow.metric s).inner ((extChartAt (𝓡 3) q).symm y)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y v)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y w) := by
  let c := extChartAt (𝓡 3) q
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (c.symm y)) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (c.symm y)) := by
    unfold TangentSpace
    infer_instance
  let A : E₃ →L[ℝ] TangentSpace (𝓡 3) (c.symm y) := mfderiv (𝓡 3) (𝓡 3) c.symm y
  let B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
    ((L.flow.metric s).inner (c.symm y)).bilinearComp A A
  have hB : limitCoordinateBilinear L q s y = B := by
    have hc : (fun a b => FlowCarrier.coordinateCoefficient L.carrier q
        (fun t x v w => (L.flow.metric t).inner x v w) a b (s, y)) =
        (fun a b => B (PiLp.single 2 a 1) (PiLp.single 2 b 1)) := by
      funext a b
      simp only [FlowCarrier.coordinateCoefficient, EuclideanSpace.basisFun_apply]
      rfl
    exact (congrArg (ContinuousLinearMap.piLpBilinearFromCoordinates
      (p := 2) (q := 2) (𝕜 := ℝ)) hc).trans
        (ContinuousLinearMap.piLpBilinearFromCoordinates_evaluations B)
  rw [hB]
  rfl



theorem blowupCoordinateBilinear_pullback_apply
    {G : GeneralizedRicciFlowData.{u}} {origin scale : ℝ} {K : Set ℝ}
    {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder G L.sliceCarrier origin scale K U)
    (q : L.sliceCarrier.carrier) {s : ℝ} (hs : s ∈ K)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → L.sliceCarrier.carrier} {x : E}
    (hφ : MDifferentiableAt 𝓘(ℝ, E) (𝓡 3) φ x)
    (hq : φ x ∈ (extChartAt (𝓡 3) q).source) (v w : E) :
    ((blowupCoordinateBilinear e q s ((extChartAt (𝓡 3) q) (φ x))).bilinearComp
      (fderiv ℝ ((extChartAt (𝓡 3) q) ∘ φ) x)
      (fderiv ℝ ((extChartAt (𝓡 3) q) ∘ φ) x)) v w =
      e.pullbackInner s hs (φ x)
        (mfderiv 𝓘(ℝ, E) (𝓡 3) φ x v) (mfderiv 𝓘(ℝ, E) (𝓡 3) φ x w) := by
  have hd := mfderiv_inverse_chart_comp_fderiv_coordinates q hφ hq
  change blowupCoordinateBilinear e q s ((extChartAt (𝓡 3) q) (φ x)) _ _ = _
  rw [blowupCoordinateBilinear_apply e q hs]
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  exact (congrArg₂ (fun V W : E₃ => e.pullbackInner s hs
    ((extChartAt (𝓡 3) q).symm ((extChartAt (𝓡 3) q) (φ x))) V W) hv hw).trans
      (congrArg (fun Y : L.sliceCarrier.carrier => e.pullbackInner s hs Y
        (mfderiv 𝓘(ℝ, E) (𝓡 3) φ x v) (mfderiv 𝓘(ℝ, E) (𝓡 3) φ x w))
        ((extChartAt (𝓡 3) q).left_inv hq))


theorem limitCoordinateBilinear_pullback_apply
    (q : L.sliceCarrier.carrier) (s : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → L.sliceCarrier.carrier} {x : E}
    (hφ : MDifferentiableAt 𝓘(ℝ, E) (𝓡 3) φ x)
    (hq : φ x ∈ (extChartAt (𝓡 3) q).source) (v w : E) :
    ((limitCoordinateBilinear L q s ((extChartAt (𝓡 3) q) (φ x))).bilinearComp
      (fderiv ℝ ((extChartAt (𝓡 3) q) ∘ φ) x)
      (fderiv ℝ ((extChartAt (𝓡 3) q) ∘ φ) x)) v w =
      (L.flow.metric s).inner (φ x)
        (mfderiv 𝓘(ℝ, E) (𝓡 3) φ x v) (mfderiv 𝓘(ℝ, E) (𝓡 3) φ x w) := by
  have hd := mfderiv_inverse_chart_comp_fderiv_coordinates q hφ hq
  change limitCoordinateBilinear L q s ((extChartAt (𝓡 3) q) (φ x)) _ _ = _
  rw [limitCoordinateBilinear_apply]
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  exact (congrArg₂ (fun V W : E₃ => (L.flow.metric s).inner
    ((extChartAt (𝓡 3) q).symm ((extChartAt (𝓡 3) q) (φ x))) V W) hv hw).trans
      (congrArg (fun Y : L.sliceCarrier.carrier => (L.flow.metric s).inner Y
        (mfderiv 𝓘(ℝ, E) (𝓡 3) φ x v) (mfderiv 𝓘(ℝ, E) (𝓡 3) φ x w))
        ((extChartAt (𝓡 3) q).left_inv hq))

end PoincareConjecture.M34
