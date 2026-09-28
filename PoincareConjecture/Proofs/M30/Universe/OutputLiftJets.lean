import PoincareConjecture.Proofs.M30.Universe.OutputLift
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

private theorem ulift_extChartAt_target {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (q : M) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} M) :=
      Poincare.Manifold.uliftChartedSpace _ M
    (extChartAt (𝓡 n) (ULift.up.{u} q)).target = (extChartAt (𝓡 n) q).target := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} M) :=
    Poincare.Manifold.uliftChartedSpace _ M
  have hchart : (chartAt (EuclideanSpace ℝ (Fin n)) (ULift.up.{u} q)).target =
      (chartAt (EuclideanSpace ℝ (Fin n)) q).target := by
    change ((Homeomorph.ulift : ULift.{u} M ≃ₜ M).toOpenPartialHomeomorph.trans
      (chartAt (EuclideanSpace ℝ (Fin n)) q)).target = _
    simp only [OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
      preimage_univ, inter_univ]
  rw [extChartAt_target, extChartAt_target, hchart]

private theorem ulift_extChartAt_symm {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (q : M) (y : EuclideanSpace ℝ (Fin n)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} M) :=
      Poincare.Manifold.uliftChartedSpace _ M
    (extChartAt (𝓡 n) (ULift.up.{u} q)).symm y =
      ULift.up.{u} ((extChartAt (𝓡 n) q).symm y) := by
  rfl

private theorem ulift_down_mfderiv_extChartAt_symm {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (q : M) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ (extChartAt (𝓡 n) q).target) (v : EuclideanSpace ℝ (Fin n)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} M) :=
      Poincare.Manifold.uliftChartedSpace _ M
    letI : IsManifold (𝓡 n) ∞ (ULift.{u} M) :=
      Poincare.Manifold.uliftIsManifold (𝓡 n) M
    mfderiv (𝓡 n) (𝓡 n) (ULift.down : ULift.{u} M → M)
        ((extChartAt (𝓡 n) (ULift.up.{u} q)).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (ULift.up.{u} q)).symm y v) =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm y v := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} M) :=
    Poincare.Manifold.uliftChartedSpace _ M
  let : IsManifold (𝓡 n) ∞ (ULift.{u} M) :=
    Poincare.Manifold.uliftIsManifold (𝓡 n) M
  have hy' : y ∈ (extChartAt (𝓡 n) (ULift.up.{u} q)).target := by
    rw [ulift_extChartAt_target]
    exact hy
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞)
    (ULift.up.{u} q) hy').contMDiffAt (extChartAt_target_mem_nhds' hy')
  have hd : MDifferentiable (𝓡 n) (𝓡 n) (ULift.down : ULift.{u} M → M) :=
    (Poincare.Manifold.uliftDiffeomorph (𝓡 n) M).contMDiff.mdifferentiable (by simp)
  have hfun : (ULift.down : ULift.{u} M → M) ∘
      (extChartAt (𝓡 n) (ULift.up.{u} q)).symm = (extChartAt (𝓡 n) q).symm := by
    funext z
    rw [Function.comp_apply, ulift_extChartAt_symm]
  have h := mfderiv_comp_apply y (hd _) (hc.mdifferentiableAt (by simp)) v
  rw [hfun] at h
  exact h.symm




theorem liftFlowCarrier_coordinateCoefficient_eqOn {n : ℕ}
    (C : FlowCarrier.{0} n) (q : C.carrier)
    (B : ∀ _t : ℝ, ∀ x : C.carrier, C.tangent x → C.tangent x → ℝ)
    (J : Set ℝ) (a b : Fin n) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace (ULift.{u} C.carrier) :=
      (liftFlowCarrier.{u} C).topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} C.carrier) :=
      (liftFlowCarrier.{u} C).chartedSpace
    letI : IsManifold (𝓡 n) ∞ (ULift.{u} C.carrier) :=
      (liftFlowCarrier.{u} C).isManifold
    EqOn
      ((liftFlowCarrier.{u} C).coordinateCoefficient (ULift.up q)
        (fun t x v w => B t x.down
          (mfderiv (𝓡 n) (𝓡 n) (ULift.down : ULift.{u} C.carrier → C.carrier) x v)
          (mfderiv (𝓡 n) (𝓡 n) (ULift.down : ULift.{u} C.carrier → C.carrier) x w)) a b)
      (C.coordinateCoefficient q B a b)
      (J ×ˢ (extChartAt (𝓡 n) q).target) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace (ULift.{u} C.carrier) :=
    (liftFlowCarrier.{u} C).topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} C.carrier) :=
    (liftFlowCarrier.{u} C).chartedSpace
  let : IsManifold (𝓡 n) ∞ (ULift.{u} C.carrier) :=
    (liftFlowCarrier.{u} C).isManifold
  intro p hp
  dsimp only [FlowCarrier.coordinateCoefficient]
  rw [ulift_down_mfderiv_extChartAt_symm q p.2 hp.2
      (EuclideanSpace.basisFun (Fin n) ℝ a),
    ulift_down_mfderiv_extChartAt_symm q p.2 hp.2
      (EuclideanSpace.basisFun (Fin n) ℝ b), ulift_extChartAt_symm]



theorem liftBlowupLimit_metricChartDomain {J : Set ℝ}
    (L : BlowupLimitFlow.{0} J) (q : L.carrier.carrier) :
    blowupMetricChartDomain (liftBlowupLimit.{u} L) (ULift.up q) =
      blowupMetricChartDomain L q := by
  let : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} L.carrier.carrier) :=
    (liftFlowCarrier.{u} L.carrier).chartedSpace
  change J ×ˢ (extChartAt (𝓡 3) (ULift.up.{u} q)).target =
    J ×ˢ (extChartAt (𝓡 3) q).target
  rw [ulift_extChartAt_target]




theorem liftBlowupLimit_iteratedFDerivWithin_coordinateCoefficient {J : Set ℝ}
    (L : BlowupLimitFlow.{0} J) (q : L.carrier.carrier) (a b : Fin 3) (r : ℕ)
    (p : ℝ × EuclideanSpace ℝ (Fin 3)) (hp : p ∈ blowupMetricChartDomain L q) :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
    letI : TopologicalSpace (liftBlowupLimit.{u} L).carrier.carrier :=
      (liftBlowupLimit.{u} L).carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
        (liftBlowupLimit.{u} L).carrier.carrier :=
      (liftBlowupLimit.{u} L).carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ (liftBlowupLimit.{u} L).carrier.carrier :=
      (liftBlowupLimit.{u} L).carrier.isManifold
    iteratedFDerivWithin ℝ r
        ((liftBlowupLimit.{u} L).carrier.coordinateCoefficient (ULift.up q)
          (fun t x v w => ((liftBlowupLimit.{u} L).flow.metric t).inner x v w) a b)
        (blowupMetricChartDomain (liftBlowupLimit.{u} L) (ULift.up q)) p =
      iteratedFDerivWithin ℝ r
        (L.carrier.coordinateCoefficient q
          (fun t x v w => (L.flow.metric t).inner x v w) a b)
        (blowupMetricChartDomain L q) p := by
  let : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
  let : TopologicalSpace (liftBlowupLimit.{u} L).carrier.carrier :=
    (liftBlowupLimit.{u} L).carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (liftBlowupLimit.{u} L).carrier.carrier :=
    (liftBlowupLimit.{u} L).carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ (liftBlowupLimit.{u} L).carrier.carrier :=
    (liftBlowupLimit.{u} L).carrier.isManifold
  rw [liftBlowupLimit_metricChartDomain]
  apply iteratedFDerivWithin_congr ?_ hp r
  exact liftFlowCarrier_coordinateCoefficient_eqOn.{u} L.carrier q
    (fun t x v w => (L.flow.metric t).inner x v w) J a b

end PoincareConjecture.M30
