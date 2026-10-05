import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Noncollapse.Generalized
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Noncollapse.TestHistory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.ConfigurationTransfer
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Seed.EpochWindow
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Seed.SeedScales

/-!
# Physical volume from the actual old generalized seed

The literal half-radius cylinder, confinement and seed comparisons
give one actual M15 configuration and its original tested-ball volume.
Source: MT Theorem 8.1 and Claim 16.27, pp. 169 and 393-394;
derivations/seed-m15-source.md, Stage J3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.M47

open Proofs.M46

/-- The M15 package depends only on the old prefix and its already
chosen analytic constant, before any next radius or observed flow. -/
theorem exists_seedM15_uniformData
    (P : M46Predecessors.{u}) {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {B : ℝ} (hB : 1 ≤ B) :
    Nonempty (M15GeneralizedUniformData.{u} 3 (surgeryEpochStart (p.i + 1))
      (actionBudget p / (4 * p.setup.epsilon))
      (p.kappa (Fin.last p.i) * seedImageRadius B (p.r (Fin.last p.i)) ^ 3 / 8)) := by
  have hH : 0 < surgeryEpochStart (p.i + 1) :=
    (by norm_num : (0 : ℝ) < 1 / 32).trans_le (epochStart_ge_initial _)
  have hbudget : 0 < actionBudget p := by unfold actionBudget; positivity
  have hl0 : 0 < actionBudget p / (4 * p.setup.epsilon) :=
    div_pos hbudget (mul_pos (by norm_num) p.setup.epsilon_pos)
  have hrho := seedImageRadius_pos hB (p.r_pos (Fin.last p.i))
  have hkappa := p.kappa_pos (Fin.last p.i)
  exact P.uniformConfigurationData _ _ _ hH hl0 (by positivity)

/-- A fixed M15 uniform package applies to the same actual seed and
half-radius cylinder; the resulting estimate is on the physical test. -/
theorem seedM15_volume_of_oldSeed
    (P : M46Predecessors.{u}) {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {V : ℝ}
    (uniform : M15GeneralizedUniformData.{u} 3 (surgeryEpochStart (p.i + 1))
      (actionBudget p / (4 * p.setup.epsilon)) V)
    {F : SurgeryFlowData.{u}} {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain}
    {x : (F.slice T).carrier} (H : SeedM15TestHistory T hT hTF x r)
    (hr : 0 < r) (hrEps : r ≤ p.setup.epsilon)
    (confinement : ActionConfinement H.spacetime.geometry.toLGeometry T
      (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val)
    (hbarrier : confinement.barrier = actionBudget p)
    (region : MinimizingRegion H.spacetime.geometry.toLGeometry T
      (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val confinement)
    {tau : ℝ} (htau : p.setup.epsilon ^ 2 ≤ tau)
    (htauStart : tau ≤ T - surgeryEpochStart (p.i - 1))
    (htauTop : tau ≤ surgeryEpochStart (p.i + 1))
    (htime : T - tau ∈ interior H.spacetime.history.generalized.interval)
    (A : Set (H.spacetime.geometry.toLGeometry.slices (T - tau)).Point)
    (hA : IsOpen A) (hne : A.Nonempty)
    (hvolume : ENNReal.ofReal V ≤ calibratedMetricVolume
      (H.spacetime.geometry.toLGeometry.slices (T - tau)).metricOnPoints A)
    (hpaths : ∀ q ∈ closure A,
      ∃ path : M14BackwardPath H.spacetime.geometry.toLGeometry T 0 tau
        ((H.spacetime.geometry.sliceIdentification T).identification H.center).val q.val,
        M14BackwardLAction H.spacetime.geometry.toLGeometry path ≤ actionBudget p / 2) :
    ENNReal.ofReal ((uniform.kappa / 8) * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) := by
  have htauPos : 0 < tau := (sq_pos_of_pos p.setup.epsilon_pos).trans_le htau
  have hHpos : 0 < surgeryEpochStart (p.i + 1) :=
    (by norm_num : (0 : ℝ) < 1 / 32).trans_le (epochStart_ge_initial _)
  have hLpos : 0 < actionBudget p := by unfold actionBudget; positivity
  have hl0pos : 0 < actionBudget p / (4 * p.setup.epsilon) :=
    div_pos hLpos (mul_pos (by norm_num) p.setup.epsilon_pos)
  have hbelow : actionBudget p / 2 < confinement.barrier := by rw [hbarrier]; linarith
  have hepssqrt : p.setup.epsilon ≤ Real.sqrt tau := by
    nlinarith [Real.sq_sqrt htauPos.le, Real.sqrt_nonneg tau, p.setup.epsilon_pos]
  have hnormalized : actionBudget p / 2 ≤
      2 * (actionBudget p / (4 * p.setup.epsilon)) * Real.sqrt tau := by
    calc
      actionBudget p / 2 =
          (2 * (actionBudget p / (4 * p.setup.epsilon))) * p.setup.epsilon := by
        field_simp [p.setup.epsilon_pos.ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hepssqrt (mul_pos (by norm_num) hl0pos).le
  have hradius : (r / 2) ^ 2 ≤ tau := by nlinarith [p.setup.epsilon_pos]
  let ball := Proofs.M15.rawActualBallCylinder H.spacetime.geometry P.m13 H.center
    (half_pos hr) H.cylinder H.time_subset H.based H.curvature
  obtain ⟨E, ⟨Q⟩⟩ := seedM15_generalized_configuration P.m12 P.m14
    H.spacetime.geometry.toLGeometry
    ((H.spacetime.geometry.sliceIdentification T).identification H.center)
    ball H.terminal_ball_compact confinement region htauPos htauStart htauTop
    hradius htime (by positivity : 0 ≤ actionBudget p / 2) hbelow hnormalized
    A hA hne hvolume hpaths
  have h := H.spacetime.configuration_half_radius uniform P H.time_mem H.center
    (half_pos hr) H.cylinder H.time_subset H.based H.curvature E Q rfl
  simpa only [H.center_eq] using h

end PoincareMT.M47
