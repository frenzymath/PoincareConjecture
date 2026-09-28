import PoincareConjecture.Proofs.M14.Sec6_4_AdaptedMetric
import PoincareConjecture.Proofs.M14.Sec6_4_PullbackScalar
import PoincareConjecture.Proofs.M14.Sec6_2_SquarePullback

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

noncomputable def horizontalAdaptedField (a b : ℝ) (P : ∀ s, G.Horizontal (R.curve s)) :
    ∀ s, G.Horizontal (R.curve s) := fun s => ((s - a) / (b - a)) • P s

variable {a b : ℝ} {P Q : ∀ s, G.Horizontal (R.curve s)}

noncomputable def horizontalAdaptedExtension
    (E : M14PullbackExtension G R.curve (Icc a b) P) :
    M14PullbackExtension G R.curve (Icc a b) (horizontalAdaptedField a b P) :=
  smulPullbackExtension E (fun s => (s - a) / (b - a))
    ((contDiff_id.sub contDiff_const).div_const (b - a))

theorem horizontalAdaptedField_contMDiffOn (hP : IsHorizontalUnitAdaptedFieldOn R a b P) :
    ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s)
        (horizontalAdaptedField a b P s)) (Icc a b) := by
  obtain ⟨E, _⟩ := hP.equation
  exact pullbackExtension_field_contMDiffOn (horizontalAdaptedExtension E)
    (R.smooth.mono (hP.interval_subset.trans R.interval_subset))

theorem horizontalAdaptedField_endpoints (hab : a < b) :
    horizontalAdaptedField a b P a = 0 ∧ horizontalAdaptedField a b P b = P b := by
  simp only [horizontalAdaptedField, sub_self, zero_div, zero_smul,
    div_self (sub_ne_zero.mpr hab.ne'), one_smul, and_self]

theorem horizontalAdaptedField_covariant_pair (hP : IsHorizontalUnitAdaptedFieldOn R a b P)
    (E : M14PullbackExtension G R.curve (Icc a b) P)
    {s : ℝ} (hs : s ∈ Icc a b) (W : G.Horizontal (R.curve s)) :
    G.spacetime.horizontalMetric.inner (R.curve s)
        (M14HorizontalCovariantDerivative G R.curve (Icc a b)
          (horizontalAdaptedField a b P) (horizontalAdaptedExtension E) s) W =
      G.spacetime.horizontalMetric.inner (R.curve s) (P s) W / (b - a) -
        2 * s * ((s - a) / (b - a)) * horizontalRicci G.leafwise (R.curve s) (P s) W := by
  have hd : deriv (fun r : ℝ => (r - a) / (b - a)) s = 1 / (b - a) := by
    simpa only [id_eq] using ((hasDerivAt_id s).sub_const a).div_const (b - a) |>.deriv
  unfold horizontalAdaptedExtension horizontalAdaptedField
  rw [horizontalCovariantDerivative_smul E _ _ hs, hd]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
    hP.equation_for_extension E s hs]
  ring

theorem horizontalAdaptedField_equation (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hP : IsHorizontalUnitAdaptedFieldOn R a b P)
    (E : M14PullbackExtension G R.curve (Icc a b) P)
    {s : ℝ} (hs : s ∈ Icc a b) (has : a < s) (W : G.Horizontal (R.curve s)) :
    G.spacetime.horizontalMetric.inner (R.curve s)
        (M14HorizontalCovariantDerivative G R.curve (Icc a b)
          (horizontalAdaptedField a b P) (horizontalAdaptedExtension E) s) W =
      G.spacetime.horizontalMetric.inner (R.curve s) (horizontalAdaptedField a b P s) W /
        (s - a) - 2 * s *
          horizontalRicci G.leafwise (R.curve s) (horizontalAdaptedField a b P s) W := by
  rw [horizontalAdaptedField_covariant_pair hP E hs]
  simp only [horizontalAdaptedField, map_smul, smul_apply, smul_eq_mul,
    horizontalRicci_smul_left hM12]
  field_simp [sub_ne_zero.mpr has.ne', sub_ne_zero.mpr hP.ordered.ne']

theorem horizontalAdaptedField_pair (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hP : IsHorizontalUnitAdaptedFieldOn R a b P)
    (hQ : IsHorizontalUnitAdaptedFieldOn R a b Q) {s : ℝ} (hs : s ∈ Icc a b) :
    G.spacetime.horizontalMetric.inner (R.curve s)
        (horizontalAdaptedField a b P s) (horizontalAdaptedField a b Q s) =
      ((s - a) / (b - a)) ^ 2 * G.spacetime.horizontalMetric.inner (R.curve b) (P b) (Q b) := by
  have hpair := horizontalUnitAdapted_pair_eq hM12 hP hQ hs (right_mem_Icc.mpr hP.ordered.le)
  simp only [horizontalAdaptedField, map_smul, smul_apply, smul_eq_mul]
  rw [← hpair]
  ring

end PoincareConjecture.M14
