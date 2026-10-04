import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Geometry.SourceFamilyScales
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction

/-!
# The actual first spatial normalization

Morgan--Tian section 10.3, pp. 247-252. Multiply the entire original
tested-slice metric by its original base scalar. The retained low point
then has a fixed scalar, the high scalar diverges, and the selected path
has a uniform length bound. No connectedness or completeness is assumed.
See M28 derivations 34-35.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

/-- One homothety of the whole tested slice, before any open restriction;
section 10.3, p. 247. -/
noncomputable def normalizedSliceMetric (H : CounterexampleNeckFamily E) (k : ℕ) :
    RiemannianMetric 3 ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier :=
  M13.scaleSmoothMetric ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) (H.base_scalar_pos k)

/-- The actual connection of the globally normalized tested slice;
section 10.3, p. 247. -/
noncomputable def normalizedSliceConnection (H : CounterexampleNeckFamily E) (k : ℕ) :
    LeviCivitaData (H.normalizedSliceMetric k) :=
  M13.scaleLeviCivitaData ((E (k + H.shift)).flow.connection (E (k + H.shift)).time)
    ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) (H.base_scalar_pos k)

/-- All source scalar values use the same global normalization, including
points away from the retained path (section 10.3, p. 247). -/
theorem normalizedSlice_scalar_eq (H : CounterexampleNeckFamily E) (k : ℕ)
    (x : ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) :
    (H.normalizedSliceConnection k).scalarCurvature x =
      (E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, x⟩ /
        (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ := by
  exact M13.homothety_scalarCurvature_eq _ _
    (Diffeomorph.refl (𝓡 3) _ ∞) _ (H.base_scalar_pos k)
    (M13.identity_metricHomothety _ _ (H.base_scalar_pos k)) _ _ x

/-- The actual retained low endpoint has one scalar independent of the
source index in the first normalization (Claim 10.4). -/
theorem normalizedSlice_lower_scalar (H : CounterexampleNeckFamily E) (k : ℕ) :
    (H.normalizedSliceConnection k).scalarCurvature
      ((H.segment k).path (H.segment k).lower) = 16 * (max C 2) ^ 2 := by
  rw [H.normalizedSlice_scalar_eq, (H.segment k).lower_scalar]
  exact mul_div_cancel_right₀ _ (H.base_scalar_pos k).ne'

/-- The actual retained high endpoint diverges in the first normalized
metric, rather than in an unrelated local neck metric (Claim 10.4). -/
theorem normalizedSlice_upper_scalar_tendsto (H : CounterexampleNeckFamily E) :
    Tendsto (fun k => (H.normalizedSliceConnection k).scalarCurvature
      ((H.segment k).path (H.segment k).upper)) atTop atTop := by
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have ht := (tendsto_const_mul_atTop_of_pos
    (by positivity : 0 < 16 * (max C 2) ^ 2)).2 H.retained_ratio_tendsto_atTop
  convert ht using 1
  funext k
  rw [H.normalizedSlice_scalar_eq, (H.segment k).lower_scalar]
  field_simp

/-- The original short retained path has a uniform length in the actual
first normalized metric (Claim 10.4(1), pp. 249-250). -/
theorem normalizedSlice_path_length_lt (H : CounterexampleNeckFamily E) (k : ℕ) :
    (H.normalizedSliceMetric k).pathELength (H.segment k).path
      (H.segment k).lower (H.segment k).upper <
        ENNReal.ofReal (A + 2 * endpointConnectorBudget epsilon C) := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hpath := (H.segment k).path_smooth.mono
    (Icc_subset_Icc (H.segment k).lower_pos.le (H.segment k).upper_lt_one.le)
  have hlength := M13.homothety_pathELength
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    (H.normalizedSliceMetric k) (Diffeomorph.refl (𝓡 3) _ ∞) Q hQ
    (M13.identity_metricHomothety _ Q hQ) (H.segment k).path
    (H.segment k).lower (H.segment k).upper hpath
  change (H.normalizedSliceMetric k).pathELength (H.segment k).path _ _ = _ at hlength
  rw [hlength]
  have hmul := (ENNReal.mul_right_strictMono
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne' ENNReal.ofReal_ne_top)
    (H.segment k).length_lt
  have hscale : Real.sqrt Q *
      ((A + 2 * endpointConnectorBudget epsilon C) * Q ^ (-1 / 2 : ℝ)) =
      A + 2 * endpointConnectorBudget epsilon C := by
    rw [Real.rpow_div_two_eq_sqrt _ hQ.le, Real.rpow_neg_one]
    field_simp
  change ENNReal.ofReal (Real.sqrt Q) * _ < ENNReal.ofReal (Real.sqrt Q) *
    ENNReal.ofReal ((A + 2 * endpointConnectorBudget epsilon C) *
      Q ^ (-1 / 2 : ℝ)) at hmul
  simpa only [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q), hscale] using hmul

end PoincareMT.M28.CounterexampleNeckFamily
