import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Combined
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Cylinder.ImageRestriction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Lemma8_3_Action.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# The action estimate after small-vector confinement

Morgan-Tian Lemma 8.3, p. 174, the action estimate preceding (8.2).
The scalar bound is on the actual trace of a supplied minimizing path.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-20-small-part-action.md`.
The geometric proof of that scalar bound is separate.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareMT.Generalized.Noncollapse

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- A supplied minimum is the actual action infimum. This is the
attainment used in the action estimate of Lemma 8.3, p. 174. -/
theorem actionValue_eq_of_minimizing {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T τ₁ τ₂ x y) (hp : M14IsMinimizing p) :
    M14ActionValue G T τ₁ τ₂ x y = M14BackwardLAction G p := by
  apply IsLeast.csInf_eq
  refine ⟨⟨p, rfl⟩, ?_⟩
  rintro a ⟨q, rfl⟩
  exact hp q

/-- A scalar lower bound along a minimizing path bounds its normalized
reduced length. Source: Lemma 8.3, p. 174. Only the positive interior of the
path interval is needed; `K` may be any real number. -/
theorem minimizing_reducedLength_lower_bound {T τ K : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T 0 τ x y) (hp : M14IsMinimizing p)
    (hscalar : ∀ s ∈ Set.Ioo 0 τ,
      -K ≤ horizontalScalarCurvature G.leafwise (p.curve s)) :
    -K * τ / 3 ≤ M14ReducedLengthValue G T 0 τ x y := by
  have hτ : 0 < τ := p.tau_lt
  have heval : (∫ s in (0 : ℝ)..τ, Real.sqrt s) =
      (2 / 3 : ℝ) * τ * Real.sqrt τ := by
    simp_rw [Real.sqrt_eq_rpow]
    rw [integral_rpow (Or.inl (by norm_num))]
    rw [Real.rpow_add hτ]
    norm_num
    ring
  have hkin (s : ℝ) : 0 ≤ G.spacetime.horizontalMetric.inner (p.curve s)
      (p.horizontal_velocity s) (p.horizontal_velocity s) := by
    by_cases hzero : p.horizontal_velocity s = 0
    · simp [hzero]
    · exact (G.spacetime.horizontalMetric.pos _ _ hzero).le
  have haction : -K * ((2 / 3 : ℝ) * τ * Real.sqrt τ) ≤
      M14BackwardLAction G p := by
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hτ.le
      ((Real.continuous_sqrt.const_mul (-K)).intervalIntegrable 0 τ)
      p.action_integrable (fun s hs => show -K * Real.sqrt s ≤
        M14RawLIntegrand G p.curve p.horizontal_velocity s from by
          change -K * Real.sqrt s ≤ Real.sqrt s *
            (horizontalScalarCurvature G.leafwise (p.curve s) +
              G.spacetime.horizontalMetric.inner (p.curve s)
                (p.horizontal_velocity s) (p.horizontal_velocity s))
          rw [mul_comm (-K)]
          exact mul_le_mul_of_nonneg_left
            ((hscalar s hs).trans (le_add_of_nonneg_right (hkin s)))
            (Real.sqrt_nonneg s))
    rw [intervalIntegral.integral_const_mul, heval] at hmono
    exact hmono
  change -K * τ / 3 ≤ M14ActionValue G T 0 τ x y / (2 * Real.sqrt τ)
  rw [actionValue_eq_of_minimizing p hp]
  apply (le_div_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr hτ))).2
  calc
    (-K * τ / 3) * (2 * Real.sqrt τ) =
        -K * ((2 / 3 : ℝ) * τ * Real.sqrt τ) := by ring
    _ ≤ _ := haction

/-- The stable minimizing trace transfers the scalar bound from the
selected exponential family. Source: Lemma 8.3, p. 174. -/
theorem stable_reducedLength_lower_bound {T τ K : ℝ} {x : G.Point}
    {E : M14ExponentialFamily G T x} (H : M14StableSet G T τ x E)
    {Z : G.Horizontal x} (hZ : Z ∈ H.carrier)
    (hscalar : ∀ s ∈ Set.Ioo 0 τ,
      -K ≤ horizontalScalarCurvature G.leafwise (E.gamma Z (Real.sqrt s))) :
    -K * τ / 3 ≤ M14ReducedLengthValue G T 0 τ x (H.endpoint_map Z) := by
  obtain ⟨p, htrace, hp, _⟩ := H.minimizing_path Z hZ
  apply minimizing_reducedLength_lower_bound p hp
  intro s hs
  rw [htrace (Set.Ioo_subset_Icc_self hs)]
  exact hscalar s hs

/-- The small-part reduced-volume density is bounded using curvature on
the actual stable traces. Source: equation (8.2), p. 174. Finiteness of image
volume is not assumed implicitly and is needed separately for integration. -/
theorem density_le_of_trace_scalar_bound {T τ K : ℝ} {x : G.Point}
    {E : M14ExponentialFamily G T x} {H : M14StableSet G T τ x E}
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hWH : W ⊆ H.carrier)
    (hscalar : ∀ Z ∈ W, ∀ s ∈ Set.Ioo 0 τ,
      -K ≤ horizontalScalarCurvature G.leafwise (E.gamma Z (Real.sqrt s))) :
    ∀ q ∈ H.endpoint_slice_map '' W,
      A.density q ≤ Real.rpow τ (-(n : ℝ) / 2) * Real.exp (K * τ / 3) := by
  rintro q ⟨Z, hZ, rfl⟩
  rw [A.density_eq _ ⟨Z, hWH hZ, rfl⟩, H.endpoint_slice_map_val Z (hWH hZ)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg H.tau_pos.le _)
  apply Real.exp_le_exp.mpr
  have h := stable_reducedLength_lower_bound H (hWH hZ) (hscalar Z hZ)
  linarith

/-- Integrating the trace scalar bound gives the small-part estimate on a
finite-volume image. Source: equation (8.2), p. 174. The geometric image
volume comparison is a separate input. -/
theorem reducedVolumeOn_le_image_volume {T τ K : ℝ} {x : G.Point}
    {E : M14ExponentialFamily G T x} {H : M14StableSet G T τ x E}
    (S : M14ReducedVolumeSourceCoverageData G)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : MeasurableSet W) (hWH : W ⊆ H.carrier)
    (hscalar : ∀ Z ∈ W, ∀ s ∈ Set.Ioo 0 τ,
      -K ≤ horizontalScalarCurvature G.leafwise (E.gamma Z (Real.sqrt s)))
    (hfinite : calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
      (H.endpoint_slice_map '' W) ≠ ⊤) :
    M14ReducedVolumeOnAnalyticCarrier A W ≤
      (Real.rpow τ (-(n : ℝ) / 2) * Real.exp (K * τ / 3)) *
        (calibratedMetricVolume (G.slices (T - τ)).metricOnPoints
          (H.endpoint_slice_map '' W)).toReal := by
  have hmono := setIntegral_mono_on
    (A.density_integrable.mono_set (Set.image_mono hWH))
    (integrableOn_const hfinite) (stable_image_measurable S A hW hWH)
    (density_le_of_trace_scalar_bound A hWH hscalar)
  simpa only [M14ReducedVolumeOnAnalyticCarrier, setIntegral_const,
    smul_eq_mul, Measure.real, mul_comm] using hmono

end PoincareMT.Generalized.Noncollapse
