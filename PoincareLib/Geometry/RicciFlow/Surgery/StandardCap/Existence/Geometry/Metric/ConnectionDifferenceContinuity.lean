import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Metric.ConnectionDifferenceAlgebra

/-!
# Continuous background families for the connection difference

All four linear rate factors depend continuously on the inverse metric,
unprimed connection, primed curvature and primed native velocity. The
background parameter is arbitrary and no flow is fixed in these estimates.
This is Morgan-Tian Section 12.5, pp. 309-319 and the owned
canonical-connection-difference-rate derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The linear rate factors take values in nested Hom fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped BigOperators

namespace PoincareMT.M34.DifferenceEnergy

variable {X : Type*} [TopologicalSpace X] {K : Set X} {n : ℕ}

/-- The cyclic combination preserves continuous parameter dependence
(Section 12.5, pp. 309-319). -/
theorem continuousOn_cyclicRicciGradient {P : X → Gamma n} (hP : ContinuousOn P K) :
    ContinuousOn (fun p => cyclicRicciGradient n (P p)) K := by
  have hh (i j k : Fin n) := continuousOn_pi.mp (continuousOn_pi.mp
    (continuousOn_pi.mp hP i) j) k
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro k
  exact ((hh i j k).neg.sub (hh j k i)).add (hh k i j)

/-- Inverse raising and finite tensor reconstruction preserve joint
continuity of the background and the lowered array
(Section 12.5, pp. 309-319). -/
theorem continuousOn_connectionRaise {I0 : X → Inverse n} {P : X → Gamma n}
    (hI : ContinuousOn I0 K) (hP : ContinuousOn P K) :
    ContinuousOn (fun p => connectionRaise (I0 p) (P p)) K := by
  dsimp only [connectionRaise, LinearMap.coe_mk, AddHom.coe_mk]
  let L : (Fin n → Fin n → V n) →L[ℝ] FA n :=
    ContinuousLinearMap.piLpBilinearFromCoordinates
  apply L.continuous.comp_continuousOn
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro i
  apply hI.clm_apply
  apply continuousOn_finsetSum
  intro k _
  exact (continuousOn_pi.mp (continuousOn_pi.mp
    (continuousOn_pi.mp hP i) j) k).smul continuousOn_const

/-- The curvature-input covariant Ricci correction depends continuously
on the background connection (Section 12.5, pp. 309-319). -/
theorem continuousOn_ricciGradientCurvature {gamma : X → Gamma n}
    (hg : ContinuousOn gamma K) (S : FS n) :
    ContinuousOn (fun p => ricciGradientCurvature (gamma p) S) K := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro k
  have hh (a b : Fin n) : ContinuousOn
      (fun x => ∑ q : Fin n, gamma x i a q * ∑ l : Fin n, raw S l l q b) K :=
    continuousOn_finsetSum _ (fun q _ => (continuousOn_pi.mp
      (continuousOn_pi.mp (continuousOn_pi.mp hg i) a) q).mul continuousOn_const)
  have hh' : ContinuousOn
      (fun x => ∑ q : Fin n, gamma x i k q * ∑ l : Fin n, raw S l l j q) K :=
    continuousOn_finsetSum _ (fun q _ => (continuousOn_pi.mp
      (continuousOn_pi.mp (continuousOn_pi.mp hg i) k) q).mul continuousOn_const)
  exact (hh j k).neg.sub hh'

/-- The connection-input correction depends continuously on primed
curvature (Section 12.5, pp. 309-319). -/
theorem continuousOn_ricciGradientConnection {R1 : X → Raw n}
    (hR : ContinuousOn R1 K) (A : FA n) :
    ContinuousOn (fun p => ricciGradientConnection (R1 p) A) K := by
  have hh (a b : Fin n) : ContinuousOn (fun x => ∑ l : Fin n, R1 x l l a b) K :=
    continuousOn_finsetSum _ (fun l _ => continuousOn_pi.mp (continuousOn_pi.mp
      (continuousOn_pi.mp (continuousOn_pi.mp hR l) l) a) b)
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro k
  exact (continuousOn_finsetSum _ (fun q _ => (hh q k).const_mul (ag A i j q))).neg.sub
    (continuousOn_finsetSum _ (fun q _ => (hh j q).const_mul (ag A i k q)))

/-- The derivative-input rate is continuous in the inverse background
(Section 12.5, pp. 309-319). -/
theorem continuousOn_connectionDerivativeRate {dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) {I0 : X → Inverse n}
    (hI : ContinuousOn I0 K) (d : Fin dS × Fin n → ℝ) :
    ContinuousOn (fun p => connectionDerivativeRate qS (I0 p) d) K := by
  exact continuousOn_connectionRaise hI continuousOn_const

/-- The metric-input rate is continuous in the inverse metric and actual
primed velocity (Section 12.5, pp. 309-319). -/
theorem continuousOn_connectionMetricRate {I0 : X → Inverse n}
    {vp : X → Fin n → Fin n → V n}
    (hI : ContinuousOn I0 K) (hv : ContinuousOn vp K) (H : FH n) :
    ContinuousOn (fun p => connectionMetricRate (I0 p) (vp p) H) K := by
  dsimp only [connectionMetricRate, LinearMap.coe_mk, AddHom.coe_mk]
  let L : (Fin n → Fin n → V n) →L[ℝ] FA n :=
    ContinuousLinearMap.piLpBilinearFromCoordinates
  apply L.continuous.comp_continuousOn
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro i
  exact (hI.clm_apply (H.continuous.comp_continuousOn
    (continuousOn_pi.mp (continuousOn_pi.mp hv i) j))).neg

/-- The connection-input rate is continuous in both background fields
(Section 12.5, pp. 309-319). -/
theorem continuousOn_connectionConnectionRate {I0 : X → Inverse n} {R1 : X → Raw n}
    (hI : ContinuousOn I0 K) (hR : ContinuousOn R1 K) (A : FA n) :
    ContinuousOn (fun p => connectionConnectionRate (I0 p) (R1 p) A) K := by
  exact continuousOn_connectionRaise hI
    (continuousOn_cyclicRicciGradient (continuousOn_ricciGradientConnection hR A))

/-- The curvature-input rate is continuous in both background fields
(Section 12.5, pp. 309-319). -/
theorem continuousOn_connectionCurvatureRate {I0 : X → Inverse n} {gamma : X → Gamma n}
    (hI : ContinuousOn I0 K) (hg : ContinuousOn gamma K) (S : FS n) :
    ContinuousOn (fun p => connectionCurvatureRate (I0 p) (gamma p) S) K := by
  exact continuousOn_connectionRaise hI
    (continuousOn_cyclicRicciGradient (continuousOn_ricciGradientCurvature hg S))

end PoincareMT.M34.DifferenceEnergy
