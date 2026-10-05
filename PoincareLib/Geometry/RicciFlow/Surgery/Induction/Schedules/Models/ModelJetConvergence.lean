import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Models.EvolvingCylinderTimeJets
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Models.EvolvingCylinderCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Convergence.SequenceJets

/-!
# Convergent time and scale parameters give convergent model jets

All finite spatial cylinder jets vary continuously with time. A
convergent scalar factor preserves that convergence, and positive
scaling preserves the actual model coefficient's invertibility.
Source: Morgan--Tian Proposition 15.2, pp. 353-354.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace PoincareMT.M45

open M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance modelConvergenceCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance modelConvergenceCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {ι : Type*} {l : Filter ι}

/-- Converging model times give convergence of every fixed spatial
jet at the centered point. Source: Proposition 15.2, pp. 353-354. -/
theorem pointJetsConverge_evolvingCylinderModel {s : ι → ℝ} {s0 : ℝ}
    (hs : Tendsto s l (𝓝 s0)) :
    PointJetsConverge (fun i => evolvingCylinderModelField (s i)) (fun _ => 0)
      (evolvingCylinderModelField s0) 0 l := by
  intro m
  exact (continuous_model_evolvingCylinder_iteratedFDeriv m 0).continuousAt.tendsto.comp hs

/-- Converging times and scalar factors give convergence of each
finite jet of the rescaled model. Source: Proposition 15.2, pp. 353-354. -/
theorem pointJetsConverge_scaled_evolvingCylinderModel {s r : ι → ℝ} {s0 r0 : ℝ}
    (hs : Tendsto s l (𝓝 s0)) (hr : Tendsto r l (𝓝 r0)) :
    PointJetsConverge (fun i x => r i • evolvingCylinderModelField (s i) x) (fun _ => 0)
      (fun x => r0 • evolvingCylinderModelField s0 x) 0 l := by
  exact (pointJetsConverge_evolvingCylinderModel hs).const_smul_family hr
    (fun i => (evolvingCylinderModelField_contDiff (s i)).contDiffAt)
    (evolvingCylinderModelField_contDiff s0).contDiffAt

/-- Positive rescaling preserves the actual model coefficient's
invertibility at every spatial point before time one. Source:
the metric rescalings in Proposition 15.2, pp. 353-354. -/
theorem model_evolvingCylinder_smul_isInvertible {r t : ℝ}
    (hr : 0 < r) (ht : t < 1) (x : E) :
    (r • evolvingCylinderModelField t x).IsInvertible := by
  have hB := model_evolvingCylinderField_isInvertible ht x
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := r⁻¹ • (evolvingCylinderModelField t x).inverse)
  · apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
      hB.self_apply_inverse, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
      ContinuousLinearMap.id_apply]
  · apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
      hB.inverse_apply_self, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
      ContinuousLinearMap.id_apply]

end PoincareMT.M45
