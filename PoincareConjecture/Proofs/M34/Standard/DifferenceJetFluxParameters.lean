import PoincareConjecture.Proofs.M34.Standard.DifferenceEnergyJetOperators
import PoincareConjecture.Proofs.M34.Standard.DifferenceFluxContinuity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M34.DifferenceEnergy

open SpacetimeBounds SpacetimeBounds.Bootstrap



noncomputable def inverseMetricThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Inverse n :=
  (twoJetProjection n (truncate 2 J)).1.inverse



noncomputable def connectionThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Gamma n :=
  connectionJetArray n (truncate 2 J)



noncomputable def curvatureThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Raw n :=
  raisedCurvatureJetArray n (truncate 2 J)



noncomputable def covariantCurvatureThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Flux n :=
  fun d l j k m =>
    prolong 2 (raisedCurvatureJetArray n) J (EuclideanSpace.single d 1) l j k m +
      curvatureAction (connectionThreeJet n J) d (curvatureThreeJet n J) l j k m



noncomputable def raisedCurvatureFluxThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) : Flux n :=
  fun i l j k m => ∑ d : Fin n,
    EuclideanSpace.proj i (inverseMetricThreeJet n J (EuclideanSpace.proj d)) *
      covariantCurvatureThreeJet n J d l j k m



theorem contDiffOn_inverseMetricThreeJet (n : ℕ) :
    ContDiffOn ℝ ∞ (inverseMetricThreeJet n) (curvatureJetDomain n 1) := by
  intro J hJ
  have ht : ContDiffAt ℝ ∞ (truncate (E := V n) (V := MetricCoefficient n) 2) J :=
    (truncate (E := V n) (V := MetricCoefficient n) 2).contDiff.contDiffAt
  have hc := contDiffAt_fst.comp J ((twoJetProjection n).contDiff.contDiffAt.comp J ht)
  exact (hJ.contDiffAt_map_inverse.comp J hc).contDiffWithinAt



theorem continuousOn_connectionThreeJet (n : ℕ) :
    ContinuousOn (connectionThreeJet n) (curvatureJetDomain n 1) :=
  (contDiffOn_differenceEnergyJetBackground n).continuousOn.fst.snd



theorem continuousOn_curvatureThreeJet (n : ℕ) :
    ContinuousOn (curvatureThreeJet n) (curvatureJetDomain n 1) :=
  (contDiffOn_differenceEnergyJetBackground n).continuousOn.snd.fst



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

end PoincareConjecture.M34.DifferenceEnergy
