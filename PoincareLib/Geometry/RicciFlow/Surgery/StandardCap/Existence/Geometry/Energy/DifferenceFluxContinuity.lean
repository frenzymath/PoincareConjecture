import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.DifferenceFluxAlgebra

/-!
# Continuity of the finite curvature-flux factors

Every factor is polynomial in the inverse metric maps, connection array,
background curvature, and its covariant derivative. These parameter
continuity statements are independent of a flow and of a chart index.
They supply the compact coefficient bounds for Morgan-Tian Section 12.5,
pp. 309-319.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The factors use nested continuous linear-map tensor fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped BigOperators

namespace PoincareMT.M34.DifferenceEnergy

variable {X : Type*} [TopologicalSpace X] {K : Set X} {n : ℕ}

/-- The slot-correction polynomial is continuous for continuous arrays
(Section 12.5, pp. 309-319). -/
theorem continuousOn_curvatureAction {gamma : X → Gamma n} {T : X → Raw n}
    (hgamma : ∀ i j l, ContinuousOn (fun p => gamma p i j l) K)
    (hT : ∀ l j k m, ContinuousOn (fun p => T p l j k m) K) (d l j k m : Fin n) :
    ContinuousOn (fun p => curvatureAction (gamma p) d (T p) l j k m) K := by
  dsimp only [curvatureAction, LinearMap.coe_mk, AddHom.coe_mk]
  exact continuousOn_finsetSum _ (fun b _ =>
    ((((hgamma d b l).mul (hT b j k m)).sub ((hgamma d j b).mul (hT l b k m))).sub
      ((hgamma d k b).mul (hT l j b m))).sub ((hgamma d m b).mul (hT l j k b)))

/-- The full raised divergence polynomial is continuous, including
the positive trace correction (Section 12.5, pp. 309-319). -/
theorem continuousOn_divergenceAction {gamma : X → Gamma n} {T : X → Flux n}
    (hgamma : ∀ i j l, ContinuousOn (fun p => gamma p i j l) K)
    (hT : ∀ i l j k m, ContinuousOn (fun p => T p i l j k m) K) (l j k m : Fin n) :
    ContinuousOn (fun p => divergenceAction (gamma p) (T p) l j k m) K := by
  dsimp only [divergenceAction, LinearMap.coe_mk, AddHom.coe_mk]
  exact continuousOn_finsetSum _ (fun i _ =>
    (continuousOn_curvatureAction hgamma (hT i) i l j k m).add
      (continuousOn_finsetSum _ (fun b _ => (hgamma i b i).mul (hT b l j k m))))

/-- Fixed curvature-coordinate contraction preserves parameter
continuity (Section 12.5, pp. 309-319). -/
theorem continuousOn_curvatureContraction {dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) {T : X → Raw n}
    (hT : ∀ l j k m, ContinuousOn (fun p => T p l j k m) K) (alpha : Fin dS) :
    ContinuousOn (fun p => curvatureContraction qS (T p) alpha) K := by
  dsimp only [curvatureContraction, LinearMap.coe_mk, AddHom.coe_mk]
  exact continuousOn_finsetSum _ (fun l _ => continuousOn_finsetSum _ (fun j _ =>
    continuousOn_finsetSum _ (fun k _ => continuousOn_finsetSum _ (fun m _ =>
      continuousOn_const.mul (hT l j k m)))))

/-- The metric-flux factor is continuous in both inverse metrics and
the background covariant curvature derivative (Section 12.5, pp. 309-319). -/
theorem continuousOn_metricFlux {I0 I1 : X → Inverse n} {kp : X → Flux n}
    (hI0 : ContinuousOn I0 K) (hI1 : ContinuousOn I1 K)
    (hkp : ∀ d l j k m, ContinuousOn (fun p => kp p d l j k m) K)
    (H : FH n) (i l j k m : Fin n) :
    ContinuousOn (fun p => metricFlux (I0 p) (I1 p) (kp p) H i l j k m) K := by
  dsimp only [metricFlux, LinearMap.coe_mk, AddHom.coe_mk]
  apply continuousOn_finsetSum
  intro d _
  exact (((EuclideanSpace.proj i).continuous.comp_continuousOn
    (hI0.clm_apply (H.continuous.comp_continuousOn
      (hI1.clm_apply continuousOn_const)))).neg).mul (hkp d l j k m)

/-- The connection-flux factor is continuous in the inverse metric
and background curvature (Section 12.5, pp. 309-319). -/
theorem continuousOn_connectionFlux {I0 : X → Inverse n} {R1 : X → Raw n}
    (hI0 : ContinuousOn I0 K)
    (hR1 : ∀ l j k m, ContinuousOn (fun p => R1 p l j k m) K)
    (A : FA n) (i l j k m : Fin n) :
    ContinuousOn (fun p => connectionFlux (I0 p) (R1 p) A i l j k m) K := by
  dsimp only [connectionFlux, LinearMap.coe_mk, AddHom.coe_mk]
  exact continuousOn_finsetSum _ (fun d _ =>
    ((EuclideanSpace.proj i).continuous.comp_continuousOn
      (hI0.clm_apply continuousOn_const)).mul
        (continuousOn_curvatureAction (gamma := fun _ : X => ag A)
          (fun _ _ _ => continuousOn_const) hR1 d l j k m))

/-- The curvature-flux factor is continuous in the inverse metric and
connection coefficients (Section 12.5, pp. 309-319). -/
theorem continuousOn_curvatureFlux {I0 : X → Inverse n} {gamma : X → Gamma n}
    (hI0 : ContinuousOn I0 K)
    (hgamma : ∀ i j l, ContinuousOn (fun p => gamma p i j l) K)
    (S : FS n) (i l j k m : Fin n) :
    ContinuousOn (fun p => curvatureFlux (I0 p) (gamma p) S i l j k m) K := by
  dsimp only [curvatureFlux, LinearMap.coe_mk, AddHom.coe_mk]
  exact continuousOn_finsetSum _ (fun d _ =>
    ((EuclideanSpace.proj i).continuous.comp_continuousOn
      (hI0.clm_apply continuousOn_const)).mul
        (continuousOn_curvatureAction (T := fun _ : X => raw S)
          hgamma (fun _ _ _ _ => continuousOn_const) d l j k m))

/-- The principal derivative factor is continuous in its inverse
metric parameter (Section 12.5, pp. 309-319). -/
theorem continuousOn_principalFlux {dS : ℕ} {I0 : X → Inverse n}
    (hI0 : ContinuousOn I0 K) (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    (d : Fin dS × Fin n → ℝ) (i l j k m : Fin n) :
    ContinuousOn (fun p => principalFlux (I0 p) qS d i l j k m) K := by
  dsimp only [principalFlux, LinearMap.coe_mk, AddHom.coe_mk]
  exact continuousOn_finsetSum _ (fun b _ =>
    ((EuclideanSpace.proj i).continuous.comp_continuousOn
      (hI0.clm_apply continuousOn_const)).mul continuousOn_const)

/-- The extra connection remainder is continuous in the raised
background flux (Section 12.5, pp. 309-319). -/
theorem continuousOn_connectionRemainder {vp : X → Flux n}
    (hvp : ∀ i l j k m, ContinuousOn (fun p => vp p i l j k m) K)
    (A : FA n) (l j k m : Fin n) :
    ContinuousOn (fun p => connectionRemainder (vp p) A l j k m) K := by
  dsimp only [connectionRemainder, LinearMap.coe_mk, AddHom.coe_mk]
  exact continuousOn_divergenceAction (gamma := fun _ : X => ag A)
    (fun _ _ _ => continuousOn_const) hvp l j k m

end PoincareMT.M34.DifferenceEnergy
