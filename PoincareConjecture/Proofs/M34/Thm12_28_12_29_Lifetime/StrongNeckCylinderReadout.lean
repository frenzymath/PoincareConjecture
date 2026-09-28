import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckBilinearReadout
import PoincareConjecture.Proofs.M34.Mathlib.RoundCylinderParametrizedJets
import PoincareConjecture.Definitions.Ch11.SingularLimits









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)



theorem mfderiv_comp_chosen_cylinder_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M] (q : UnitTwoSphere)
    (f : RoundCylinderSpace → M) (p : RoundCylinderCoordinates)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f
      ((chartAt E₂ q).symm p.1, p.2)) (v : RoundCylinderCoordinates) :
    mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
      (fun y => f ((chartAt E₂ q).symm y.1, y.2)) p v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f
        ((chartAt E₂ q).symm p.1, p.2)
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
  have hA : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 2) Prod.fst p = A :=
    A.mfderiv_eq
  have hB : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) 𝓘(ℝ, ℝ) B p = B :=
    B.mfderiv_eq
  rw [mfderiv_prodMk ha hb, mfderiv_comp p hc A.mdifferentiableAt, hA, hB] at h
  exact congrArg (fun L => L v) h

variable {J : Set ℝ} {L : BlowupLimitFlow.{u} J}

private local instance : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance : ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold




theorem cylinder_coefficient_difference_fixed_chart
    {G : GeneralizedRicciFlowData.{u}} {origin scale : ℝ} {K : Set ℝ}
    {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder G L.sliceCarrier origin scale K U)
    (coordinate : RoundCylinderSpace → L.sliceCarrier.carrier)
    (q : UnitTwoSphere) (a : L.sliceCarrier.carrier) {s : ℝ} (hs : s ∈ K)
    (p : RoundCylinderCoordinates)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate
      ((chartAt E₂ q).symm p.1, p.2))
    (ha : coordinate ((chartAt E₂ q).symm p.1, p.2) ∈ (extChartAt (𝓡 3) a).source)
    (i j : Fin 3) :
    let φ := fun y : RoundCylinderCoordinates => coordinate ((chartAt E₂ q).symm y.1, y.2)
    let f := (extChartAt (𝓡 3) a) ∘ φ
    roundCylinderTensorCoefficient (generalizedCylinderPullback e coordinate s)
        (chartAt E₂ q) p i j -
      roundCylinderTensorCoefficient (roundCylinderPullback (L.flow.metric s) coordinate)
        (chartAt E₂ q) p i j =
      ((blowupCoordinateBilinear e a s (f p) - limitCoordinateBilinear L a s (f p)).bilinearComp
        (fderiv ℝ f p) (fderiv ℝ f p))
        (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) := by
  dsimp only
  have hφ := hf.comp p ((cylinderChart_symm_smooth q p).mdifferentiableAt (by simp))
  have hb := blowupCoordinateBilinear_pullback_apply e a hs hφ ha
    (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)
  have hl := limitCoordinateBilinear_pullback_apply a s hφ ha
    (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)
  simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply] at hb hl ⊢
  have hv := mfderiv_comp_chosen_cylinder_chart q coordinate p hf (roundCylinderCoordinateBasis i)
  have hw := mfderiv_comp_chosen_cylinder_chart q coordinate p hf (roundCylinderCoordinateBasis j)
  refine ((congrArg₂ (fun v w : ℝ => v - w) hb hl).trans ?_).symm
  simp only [generalizedCylinderPullback, dif_pos hs, roundCylinderTensorCoefficient,
    roundCylinderPullback]
  exact congrArg₂ (fun v w : ℝ => v - w)
    (congrArg₂ (fun V W : E₃ => e.pullbackInner s hs
      (coordinate ((chartAt E₂ q).symm p.1, p.2)) V W) hv hw)
    (congrArg₂ (fun V W : E₃ => (L.flow.metric s).inner
      (coordinate ((chartAt E₂ q).symm p.1, p.2)) V W) hv hw)

end PoincareConjecture.M34
