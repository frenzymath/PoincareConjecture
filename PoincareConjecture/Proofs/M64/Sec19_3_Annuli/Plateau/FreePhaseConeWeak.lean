import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseConeLift
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseLiftH1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseDiskGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityCharts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => ball (0 : LoopPlane) 1
local notation "mu" => volume.restrict S

theorem auxiliaryCircle_cone_weak_phase
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    {e : Q.charts.Point → EuclideanSpace ℝ (Fin m)} (he : Continuous e)
    (R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    {gamma : ℝ → Q.charts.Point}
    (A : M64ObservedConeDisk (n := (n + 1) + 1) e gamma)
    {L : ℝ → ℝ} (hL : Continuous L)
    (hquot : ∀ x, P.circle.quotient (L x) = (gamma x).1.2) :
    ∃ (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ), Continuous u ∧
      (∀ p, P.circle.quotient (u p) = (A.map p).1.2) ∧
      (∀ x, u (angularPoint x) = L x) ∧ MemLp u 2 mu ∧
      (∀ i, MemLp (V i) 2 mu) ∧ (∀ i, HasWeakPartialDeriv i (V i) u S) ∧
      (∀ i, ∀ᵐ p ∂mu, ‖R (A.column i p)‖ ^ 2 =
        (curvePeriod / circumference) ^ 2 * (V i p) ^ 2) ∧
      ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
        (∫ p in S, phi p * V i p) +
          (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) =
          ∫ t in Icc (-Real.pi) Real.pi,
            angularPoint t i * (phi (angularPoint t) * L t) := by
  obtain ⟨u, hu, hquotu, hboundary⟩ := auxiliaryCircle_cone_real_phase P Q A hL hquot
  let k := curvePeriod / circumference
  let q := fun p => R (e (A.map p))
  let Z := fun i p => R (A.column i p)
  have hk : k ≠ 0 := div_ne_zero (ne_of_gt (by unfold curvePeriod; positivity))
    P.circle.positive.ne'
  have hq : Continuous q := R.continuous.comp (he.comp A.continuous)
  have huLp : MemLp u 2 mu := by
    apply (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mpr
    exact (hu.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall
  have hZ (i : Fin 2) : MemLp (Z i) 2 mu := R.comp_memLp' (Lp.memLp (A.column i))
  have hw (i j : Fin 2) : HasWeakPartialDeriv i (fun p => Z i p j) (fun p => q p j) S :=
    m64WeakPartial_comp_linear A.observed_memLp (Lp.memLp (A.column i))
      (A.weak_partial i) R j
  have hphase (p : LoopPlane) : q p = angularPoint (k * u p) := by
    dsimp only [q, k]
    rw [hR, ← hquotu, planarCircleObservation_quotient]
  obtain ⟨hV, hwV, hnorm⟩ :=
    m64ContinuousPhase_weak_columns isOpen_ball hk hu hq huLp hZ hw hphase
  refine ⟨u, _, hu, hquotu, hboundary, huLp, hV, hwV, hnorm, ?_⟩
  intro phi hphi i
  simpa only [hboundary] using m64ContinuousScalarH1Disk_green huLp hV hwV hu phi hphi i

end PoincareConjecture.M64
