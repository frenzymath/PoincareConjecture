import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreePhaseSeed
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedAnnulusEnergyIdentity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_normalized_freeWeakPhase_seed
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e)
    (R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    (c0 c1 : ℝ → Q.charts.Point) (hp0 : Function.Periodic c0 curvePeriod)
    (hp1 : Function.Periodic c1 curvePeriod) (H0 H1 : ℝ ≃o ℝ)
    (hzero : ∀ x, P.circle.quotient (H0 x) = (c0 x).1.2)
    (hone : ∀ x, P.circle.quotient (H1 x) = (c1 x).1.2)
    {D : ℝ} (hdegree : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = (Q.flow.metric time).inner q v v)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (Q.flow.metric time) (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.map S) :
    ∃ W : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e R c0 c1 H0 H1 (curvePeriod / circumference) D,
      W.annulus.map = A.map ∧ ∀ r : ℝ,
        W.annulus.weightedEnergy B r = m64ClassicalWeightedGramEnergy (Q.flow.metric time) A r := by
  let Anorm : M64Annulus (Q.flow.metric time)
      (c0 ∘ (normalizedDegreeOneLift sigma0).map)
      (c1 ∘ (normalizedDegreeOneLift sigma1).map) := {
    A with
    lower_boundary := fun x => (A.lower_boundary x).trans
      (congrFun (normalizedDegreeOneLift_trace hp0 sigma0).symm x)
    upper_boundary := fun x => (A.upper_boundary x).trans
      (congrFun (normalizedDegreeOneLift_trace hp1 sigma1).symm x) }
  obtain ⟨W, -, -, hmap, hcol, -⟩ := auxiliaryCircle_freeWeakPhase_seed P Q time
    e he R hR c0 c1 H0 H1 hzero hone hdegree
    (normalizedDegreeOneLift sigma0) (normalizedDegreeOneLift sigma1)
    (Ico_subset_Icc_self (normalizedDegreeOneLift_zero sigma0))
    (Ico_subset_Icc_self (normalizedDegreeOneLift_zero sigma1)) Anorm hA
  refine ⟨W, hmap, ?_⟩
  intro r
  unfold M64ObservedWeakAnnulus.weightedEnergy m64ClassicalWeightedGramEnergy
  rw [m64Annulus_restrict_closed_eq_interior]
  apply integral_congr_ae
  filter_upwards [hcol 0, hcol 1, ae_restrict_of_ae A.ae_manifold_differentiable,
    ae_restrict_mem isOpen_interior.measurableSet] with p h0 h1 hp hm
  rw [hmap, h0, h1,
    m64ObservedMetric_diagonal_of_mDifferentiableAt (Q.flow.metric time) e he B hdiag
      (hp (interior_subset hm)) 0,
    m64ObservedMetric_diagonal_of_mDifferentiableAt (Q.flow.metric time) e he B hdiag
      (hp (interior_subset hm)) 1]

end PoincareConjecture.M64
