import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Volume
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.EnergyLp
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.TimeIdentification
import Mathlib.MeasureTheory.Group.Prod

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

open Poincare.Analysis.Parabolic.WeakRegularity

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem contDiffOn_scalarCurvature_coordinates :
    ContDiffOn ℝ ∞ (fun z : Spacetime n =>
      (F.connection (-z.2)).scalarCurvature (e z.1)) (domain J e) := by
  have hρ := contDiffOn_density F e he hei
  have hd : ContDiffOn ℝ ∞ (Canonical.timeDeriv (density F e)) (domain J e) :=
    (hρ.fderiv_of_isOpen (isOpen_domain e) (by simp)).clm_apply contDiffOn_const
  apply (hd.div hρ (fun z hz => (density_pos F e he hei hz.1).ne')).congr
  intro z hz
  change (F.connection (-z.2)).scalarCurvature (e z.1) =
    Canonical.timeDeriv (density F e) z / density F e z
  rw [timeDeriv_density F e he hei hz, mul_div_cancel_right₀ _
    (density_pos F e he hei hz.1).ne']

end PoincareConjecture.RicciFlow.BackwardCoordinates

namespace Poincare.Analysis.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

theorem ae_time_slice_deriv_eq_fderiv_of_lipschitz
    {I : Set ℝ} {O : Set E} (hI : IsOpen I) (hO : IsOpen O)
    {u : ℝ × E → ℝ} {L : ℝ≥0} (hu : LipschitzOnWith L u (I ×ˢ O)) :
    ∀ᵐ z ∂(volume.restrict I).prod (volume.restrict O),
      deriv (fun t => u (t, z.2)) z.1 = fderiv ℝ u z (1, 0) := by
  let : (volume : Measure (ℝ × E)).IsAddHaarMeasure := by
    change ((volume : Measure ℝ).prod (volume : Measure E)).IsAddHaarMeasure
    infer_instance
  rw [Measure.prod_restrict]
  have h := WeakDerivative.ae_differentiableAt_of_lipschitzOn
    (volume : Measure (ℝ × E)) (hI.prod hO) hu
  filter_upwards [ae_restrict_of_ae h,
    ae_restrict_mem (hI.measurableSet.prod hO.measurableSet)] with z hz hzU
  exact ((hz hzU).hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv

end Poincare.Analysis.Elliptic
