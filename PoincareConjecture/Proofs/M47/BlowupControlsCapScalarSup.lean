import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingScalar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

theorem cap_scalarSup_error_of_pointwise_error {X : Type*} {U : Set X}
    (hne : U.Nonempty) (R R' : X → ℝ) (hbounded : BddAbove (R '' U))
    {nu : ℝ} (hclose : ∀ x ∈ U, |R' x - R x| ≤ nu) :
    |sSup (R' '' U) - sSup (R '' U)| ≤ nu := by
  have hbounded' : BddAbove (R' '' U) := by
    obtain ⟨B, hB⟩ := hbounded
    refine ⟨B + nu, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hdiff := (abs_le.mp (hclose x hx)).2
    have hupper := hB (mem_image_of_mem R hx)
    linarith
  have hupper : sSup (R' '' U) ≤ sSup (R '' U) + nu := by
    apply csSup_le (hne.image R')
    rintro _ ⟨x, hx, rfl⟩
    have hdiff := (abs_le.mp (hclose x hx)).2
    have hold := le_csSup hbounded (mem_image_of_mem R hx)
    linarith
  have hlower : sSup (R '' U) ≤ sSup (R' '' U) + nu := by
    apply csSup_le (hne.image R)
    rintro _ ⟨x, hx, rfl⟩
    have hdiff := (abs_le.mp (hclose x hx)).1
    have hnew := le_csSup hbounded' (mem_image_of_mem R' hx)
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem cap_image_scalarSup_close {g : RiemannianMetric 3 M}
    (N : CapCertificate g) (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
    (f : M → X) {nu : ℝ}
    (hclose : ∀ x ∈ N.carrier, |D.scalarCurvature (f x) -
      N.connection.scalarCurvature x| ≤ nu) :
    |scalarCurvatureSupOn h D (f '' N.carrier) -
      scalarCurvatureSupOn g N.connection N.carrier| ≤ nu := by
  obtain ⟨o, ho⟩ := N.core_nonempty
  have hoc : o ∈ N.carrier := by
    have hclosed : o ∈ N.closed_core :=
      interior_subset (N.core_eq_interior_closed_core ▸ ho)
    exact (N.closed_core_eq_complement_end ▸ hclosed).1
  have hbounded : BddAbove (N.connection.scalarCurvature '' N.carrier) := by
    simpa only [image_eq_range] using N.scalar_range_bddAbove_on_subset subset_rfl
  have herror := cap_scalarSup_error_of_pointwise_error ⟨o, hoc⟩
    N.connection.scalarCurvature (D.scalarCurvature ∘ f) hbounded hclose
  simpa only [scalarCurvatureSupOn, ← image_eq_range, image_image, Function.comp_def] using herror

end PoincareConjecture.M47
