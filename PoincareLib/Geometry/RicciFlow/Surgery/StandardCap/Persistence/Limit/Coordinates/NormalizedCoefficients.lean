import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.IntrinsicJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.CoordinateJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.ChartTopology
import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients

/-!
# Coordinate jets of the actual normalized cap metric

The coefficient field is precisely the scaled pullback along the supplied
M36 map. Its intrinsic certificate implies ordinary coefficient bounds on
every fixed compact subset of the comparison domain. Morgan--Tian,
Claim 16.6 and Corollary 16.7, pp. 371-372.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.SurgeryCapClose

local notation "E" => StandardCapSpace

noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}

/-- The normalized actual pullback metric of Claim 16.6, retaining the
single inverse-square height factor from the frozen M36 comparison. -/
noncomputable def normalizedCoefficients (Q : SurgeryCapClose g₀ S g tip scale eta) :
    E → E →L[ℝ] E →L[ℝ] ℝ :=
  fun x => scale⁻¹ ^ 2 • g.pullbackCoefficients Q.map x

/-- Evaluation is the tensor appearing in the supplied jet certificate,
with both tangent slots pulled back through the supplied comparison map. -/
theorem normalizedCoefficients_apply (Q : SurgeryCapClose g₀ S g tip scale eta)
    (x : E) (v w : E) :
    Q.normalizedCoefficients x v w = scale⁻¹ ^ 2 *
      g.inner (Q.map x) (mfderiv (𝓡 3) (𝓡 3) Q.map x v)
        (mfderiv (𝓡 3) (𝓡 3) Q.map x w) := rfl

/-- The actual normalized coefficients are smooth throughout their
comparison domain, without any assertion about its complement. -/
theorem contDiffOn_normalizedCoefficients (Q : SurgeryCapClose g₀ S g tip scale eta) :
    ContDiffOn ℝ ∞ Q.normalizedCoefficients (g₀.metric.ball 0 eta⁻¹) := by
  intro x hx
  have hf := Q.map_smooth.contMDiffAt (Q.toPartialDiffeomorph.open_source.mem_nhds hx)
  exact ((contDiffAt_const (c := scale⁻¹ ^ 2)).smul
    (g.contDiffAt_pullbackCoefficients hf)).contDiffWithinAt

/-- Fixed compact coordinate regions have finite-jet constants before
the surgery scale, comparison map and tolerance are chosen. -/
theorem exists_normalized_coefficient_jet_bound
    (g₀ : StandardInitialMetric) {K : Set E} (hK : IsCompact K) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : GeneralizedSliceCarrier.{u})
      (g : RiemannianMetric 3 S.carrier) (tip : S.carrier) (scale eta : ℝ)
      (Q : SurgeryCapClose g₀ S g tip scale eta),
      j ≤ ⌊eta⁻¹⌋₊ → K ⊆ g₀.metric.ball 0 eta⁻¹ → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (Q.normalizedCoefficients - g₀.metric.euclideanCoefficients) x‖ ≤
          C * eta := by
  obtain ⟨C, hC, hbound⟩ :=
    M44.exists_local_bilinear_jet_bound_of_covariant_norms g₀.connection hK j
  refine ⟨C, hC, ?_⟩
  intro S g tip scale eta Q hj hKsub x hx
  apply hbound Q.normalizedCoefficients (g₀.metric.ball 0 eta⁻¹)
    Q.toPartialDiffeomorph.open_source Q.contDiffOn_normalizedCoefficients
    eta Q.eta_pos.le x hx (hKsub hx)
  intro l hl
  exact (Q.covariant_error_lt (hKsub hx) (hl.trans hj)).le

end PoincareMT.SurgeryCapClose
