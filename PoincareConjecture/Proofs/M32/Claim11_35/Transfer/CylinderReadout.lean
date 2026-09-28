import PoincareConjecture.Proofs.M32.Claim11_35.Transfer.BilinearJets
import PoincareConjecture.Proofs.M32.Mathlib.InverseChartDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients
import PoincareConjecture.Definitions.Ch11.SingularLimits

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

set_option backward.isDefEq.respectTransparency false in
private theorem cylinder_bilinear_error_apply
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale I U)
    (q : L.sliceCarrier.carrier) {s : ℝ} (hs : s ∈ I) (y v w : E₃) :
    (∑ a : Fin 3, ∑ b : Fin 3,
      (blowupPullbackCoefficient e q a b (s, y) -
        FlowCarrier.coordinateCoefficient L.carrier q
          (fun t x v w => (L.flow.metric t).inner x v w) a b (s, y)) •
        (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ a)).smulRight
          (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ b))) v w =
      e.pullbackInner s hs ((extChartAt (𝓡 3) q).symm y)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y v)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y w) -
      (L.flow.metric s).inner ((extChartAt (𝓡 3) q).symm y)
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
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (c.symm y)) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (c.symm y)) := by
    unfold TangentSpace
    infer_instance
  let A : E₃ →L[ℝ] TangentSpace (𝓡 3) (f (c.symm y)) :=
    (mfderiv (𝓡 3) (𝓡 3) f (c.symm y)).comp
      (mfderiv (𝓡 3) (𝓡 3) c.symm y)
  let D : E₃ →L[ℝ] TangentSpace (𝓡 3) (c.symm y) := mfderiv (𝓡 3) (𝓡 3) c.symm y
  let B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
    scale • ((F.metric (origin + s / scale)).inner (f (c.symm y))).bilinearComp A A -
      ((L.flow.metric s).inner (c.symm y)).bilinearComp D D
  have hB := SpacetimeBounds.bilinear_eq_sum_dual (EuclideanSpace.basisFun (Fin 3) ℝ) B
  have hentry (a b : Fin 3) : B (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      blowupPullbackCoefficient e q a b (s, y) -
        FlowCarrier.coordinateCoefficient L.carrier q
          (fun t x v w => (L.flow.metric t).inner x v w) a b (s, y) := by
    simp only [blowupPullbackCoefficient, dif_pos hs, FlowCarrier.coordinateCoefficient]
    rfl
  simp only [hentry] at hB
  rw [← hB]
  rfl

private theorem mfderiv_chosen_cylinder_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
    (q : UnitTwoSphere) (f : RoundCylinderSpace → M) (p : RoundCylinderCoordinates)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f
      ((chartAt E₂ q).symm p.1, p.2)) (v : RoundCylinderCoordinates) :
    mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
      (fun y => f ((chartAt E₂ q).symm y.1, y.2)) p v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f ((chartAt E₂ q).symm p.1, p.2)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm p.1 v.1, v.2) := by
  let c := chartAt E₂ q
  have hc : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm p.1 := by
    apply ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := q)).contMDiffAt
      ?_).mdifferentiableAt (by simp)
    exact c.open_target.mem_nhds (by rw [roundCylinder_sphereChart_target]; trivial)
  let A := ContinuousLinearMap.fst ℝ E₂ ℝ
  let B := ContinuousLinearMap.snd ℝ E₂ ℝ
  have ha := hc.comp p A.mdifferentiableAt
  have hb := B.mdifferentiableAt (x := p)
  have h := mfderiv_comp p hf (ha.prodMk hb)
  have hA : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 2) Prod.fst p = A := A.mfderiv_eq
  have hB : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) 𝓘(ℝ, ℝ) B p = B := B.mfderiv_eq
  rw [mfderiv_prodMk ha hb, mfderiv_comp p hc A.mdifferentiableAt, hA, hB] at h
  exact congrArg (fun L => L v) h

set_option backward.isDefEq.respectTransparency false in

theorem cylinder_coefficient_error_fixed_chart
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {F : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale I U)
    (coordinate : RoundCylinderSpace → L.sliceCarrier.carrier)
    (q : UnitTwoSphere) (a : L.sliceCarrier.carrier) {s : ℝ} (hs : s ∈ I)
    (p : RoundCylinderCoordinates)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate
      ((chartAt E₂ q).symm p.1, p.2))
    (ha : coordinate ((chartAt E₂ q).symm p.1, p.2) ∈ (extChartAt (𝓡 3) a).source)
    (i j : Fin 3) :
    let φ := fun y : RoundCylinderCoordinates => coordinate ((chartAt E₂ q).symm y.1, y.2)
    let f := (extChartAt (𝓡 3) a) ∘ φ
    let B := fun y : E₃ => ∑ v : Fin 3, ∑ w : Fin 3,
      (blowupPullbackCoefficient e a v w (s, y) -
        FlowCarrier.coordinateCoefficient L.carrier a
          (fun t x v w => (L.flow.metric t).inner x v w) v w (s, y)) •
        (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ v)).smulRight
          (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ w))
    roundCylinderTensorCoefficient (generalizedCylinderPullback e coordinate s)
        (chartAt E₂ q) p i j -
      roundCylinderTensorCoefficient (roundCylinderPullback (L.flow.metric s) coordinate)
        (chartAt E₂ q) p i j =
      ((B (f p)).bilinearComp (fderiv ℝ f p) (fderiv ℝ f p))
        (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) := by
  dsimp only
  let φ : RoundCylinderCoordinates → L.sliceCarrier.carrier := fun y =>
    coordinate ((chartAt E₂ q).symm y.1, y.2)
  let c := extChartAt (𝓡 3) a
  let f := c ∘ φ
  have hφ : MDifferentiableAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ p :=
    hf.comp p ((cylinderChart_symm_smooth q p).mdifferentiableAt (by simp))
  have hd := mfderiv_inverse_chart_comp_fderiv_coordinates a hφ ha
  have hvi := congrArg (fun A => A (roundCylinderCoordinateBasis i)) hd
  have hvj := congrArg (fun A => A (roundCylinderCoordinateBasis j)) hd
  simp only [ContinuousLinearMap.comp_apply] at hvi hvj
  have hb := cylinder_bilinear_error_apply e a hs (f p)
    (fderiv ℝ f p (roundCylinderCoordinateBasis i))
    (fderiv ℝ f p (roundCylinderCoordinateBasis j))
  have hleft : c.symm (f p) = φ p := c.left_inv ha
  have hmove := congrArg₂ (fun V W : E₃ =>
    e.pullbackInner s hs (c.symm (f p)) V W -
      (L.flow.metric s).inner (c.symm (f p)) V W) hvi hvj
  have hpoint := congrArg (fun Y : L.sliceCarrier.carrier =>
    e.pullbackInner s hs Y
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ p (roundCylinderCoordinateBasis i))
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ p (roundCylinderCoordinateBasis j)) -
      (L.flow.metric s).inner Y
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ p (roundCylinderCoordinateBasis i))
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) φ p (roundCylinderCoordinateBasis j))) hleft
  have hread := hb.trans (hmove.trans hpoint)
  have hi := mfderiv_chosen_cylinder_chart q coordinate p hf (roundCylinderCoordinateBasis i)
  have hj := mfderiv_chosen_cylinder_chart q coordinate p hf (roundCylinderCoordinateBasis j)
  rw [hi, hj] at hread
  simpa only [ContinuousLinearMap.bilinearComp_apply, generalizedCylinderPullback,
    dif_pos hs, roundCylinderTensorCoefficient, roundCylinderPullback, φ] using hread.symm

end PoincareConjecture.M32
