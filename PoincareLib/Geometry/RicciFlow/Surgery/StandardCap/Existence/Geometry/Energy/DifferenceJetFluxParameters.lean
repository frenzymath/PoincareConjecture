import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.DifferenceEnergyJetOperators
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.DifferenceFluxContinuity

/-!
# Curvature-flux parameters on formal metric three-jets

The inverse map, connection, raised curvature, covariant curvature derivative
and its raised flux are continuous on the invertible metric-jet domain.
Thus one compact pair of elliptic jet boxes supplies all parameters in the
actual curvature-difference flux. This is the coefficient preparation for
Morgan-Tian Section 12.5, pp. 309-319.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The finite jets and curvature targets use nested Hom fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped ContDiff BigOperators

namespace PoincareMT.M34.DifferenceEnergy

open SpacetimeBounds SpacetimeBounds.Bootstrap

/-- The actual inverse bilinear map read from the zeroth coefficient of a
formal metric three-jet (Section 12.5, pp. 309-319). -/
noncomputable def inverseMetricThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Inverse n :=
  (twoJetProjection n (truncate 2 J)).1.inverse

/-- The direction-first connection array read from a metric three-jet
(Section 12.5, pp. 309-319). -/
noncomputable def connectionThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Gamma n :=
  connectionJetArray n (truncate 2 J)

/-- The one-output curvature array read from a metric three-jet
(Section 12.5, pp. 309-319). -/
noncomputable def curvatureThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Raw n :=
  raisedCurvatureJetArray n (truncate 2 J)

/-- Ordinary curvature differentiation plus the exact four slot corrections
gives the formal covariant derivative (Section 12.5, pp. 309-319). -/
noncomputable def covariantCurvatureThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Flux n :=
  fun d l j k m =>
    prolong 2 (raisedCurvatureJetArray n) J (EuclideanSpace.single d 1) l j k m +
      curvatureAction (connectionThreeJet n J) d (curvatureThreeJet n J) l j k m

/-- Raise the derivative index of the background covariant curvature
derivative with the formal inverse metric (Section 12.5, pp. 309-319). -/
noncomputable def raisedCurvatureFluxThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Flux n :=
  fun i l j k m => ∑ d : Fin n,
    EuclideanSpace.proj i (inverseMetricThreeJet n J (EuclideanSpace.proj d)) *
      covariantCurvatureThreeJet n J d l j k m

/-- The inverse map is smooth on the three-jet invertible domain
(Section 12.5, pp. 309-319). -/
theorem contDiffOn_inverseMetricThreeJet (n : ℕ) :
    ContDiffOn ℝ ∞ (inverseMetricThreeJet n) (curvatureJetDomain n 1) := by
  intro J hJ
  have ht : ContDiffAt ℝ ∞ (truncate (E := V n) (V := MetricCoefficient n) 2) J :=
    (truncate (E := V n) (V := MetricCoefficient n) 2).contDiff.contDiffAt
  have hc := contDiffAt_fst.comp J ((twoJetProjection n).contDiff.contDiffAt.comp J ht)
  exact (hJ.contDiffAt_map_inverse.comp J hc).contDiffWithinAt

/-- The connection three-jet readout is continuous on the invertible domain
(Section 12.5, pp. 309-319). -/
theorem continuousOn_connectionThreeJet (n : ℕ) :
    ContinuousOn (connectionThreeJet n) (curvatureJetDomain n 1) :=
  (contDiffOn_differenceEnergyJetBackground n).continuousOn.fst.snd

/-- The raised curvature readout is continuous on the invertible domain
(Section 12.5, pp. 309-319). -/
theorem continuousOn_curvatureThreeJet (n : ℕ) :
    ContinuousOn (curvatureThreeJet n) (curvatureJetDomain n 1) :=
  (contDiffOn_differenceEnergyJetBackground n).continuousOn.snd.fst

/-- The covariant background derivative depends continuously on the metric
three-jet (Section 12.5, pp. 309-319). -/
theorem continuousOn_covariantCurvatureThreeJet (n : ℕ) :
    ContinuousOn (covariantCurvatureThreeJet n) (curvatureJetDomain n 1) := by
  have hg := continuousOn_connectionThreeJet n
  have hR := continuousOn_curvatureThreeJet n
  have hd : ContinuousOn (prolong 2 (raisedCurvatureJetArray n)) (curvatureJetDomain n 1) :=
    (contDiffOn_differenceEnergyJetBackground n).continuousOn.snd.snd
  apply continuousOn_pi.mpr
  intro d
  apply continuousOn_pi.mpr
  intro l
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro k
  apply continuousOn_pi.mpr
  intro m
  have heval := hd.clm_apply (continuousOn_const (c := EuclideanSpace.single d 1))
  exact (continuousOn_pi.mp (continuousOn_pi.mp
    (continuousOn_pi.mp (continuousOn_pi.mp heval l) j) k) m).add
    (continuousOn_curvatureAction
      (fun i j l => continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hg i) j) l)
      (fun l j k m => continuousOn_pi.mp (continuousOn_pi.mp
        (continuousOn_pi.mp (continuousOn_pi.mp hR l) j) k) m)
      d l j k m)

/-- The raised background curvature flux is continuous on the invertible
metric-jet domain (Section 12.5, pp. 309-319). -/
theorem continuousOn_raisedCurvatureFluxThreeJet (n : ℕ) :
    ContinuousOn (raisedCurvatureFluxThreeJet n) (curvatureJetDomain n 1) := by
  have hI := (contDiffOn_inverseMetricThreeJet n).continuousOn
  have hk := continuousOn_covariantCurvatureThreeJet n
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro l
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro k
  apply continuousOn_pi.mpr
  intro m
  exact continuousOn_finsetSum _ (fun d _ =>
    ((EuclideanSpace.proj i).continuous.comp_continuousOn
      (hI.clm_apply continuousOn_const)).mul
        (continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp
          (continuousOn_pi.mp (continuousOn_pi.mp hk d) l) j) k) m))

end PoincareMT.M34.DifferenceEnergy
