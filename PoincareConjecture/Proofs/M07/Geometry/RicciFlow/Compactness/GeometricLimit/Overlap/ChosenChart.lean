import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
  (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
  [∀ i, Nonempty (Piece U i)] (O : OverlapSystem (fun i => Piece U i))

theorem quotientChart_symm_eq_chartParametrization (i : ι) :
    ⇑(quotientChart U hU O i).symm = chartParametrization U hU (O.include i) := rfl

theorem exists_quotient_chartAt (q : Quotient O.setoid) :
    letI := quotientChartedSpace U hU O
    ∃ i, chartAt (EuclideanSpace ℝ (Fin n)) q = quotientChart U hU O i := by
  let := quotientChartedSpace U hU O
  have h := chart_mem_atlas (EuclideanSpace ℝ (Fin n)) q
  change ∃ i, quotientChart U hU O i = chartAt (EuclideanSpace ℝ (Fin n)) q at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi.symm⟩

theorem exists_chosen_quotient_chart (q : Quotient O.setoid) :
    letI := quotientChartedSpace U hU O
    ∃ i, extChartAt (𝓡 n) q = (quotientChart U hU O i).toPartialEquiv ∧
      (extChartAt (𝓡 n) q).target = U i ∧
      ⇑(extChartAt (𝓡 n) q).symm = chartParametrization U hU (O.include i) := by
  let := quotientChartedSpace U hU O
  obtain ⟨i, hi⟩ := exists_quotient_chartAt U hU O q
  have he : extChartAt (𝓡 n) q = (quotientChart U hU O i).toPartialEquiv := by
    simp only [extChartAt, hi, OpenPartialHomeomorph.extend,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl]
  refine ⟨i, he, ?_, ?_⟩
  · rw [he]
    exact quotientChart_target U hU O i
  · rw [he]
    exact quotientChart_symm_eq_chartParametrization U hU O i

theorem comp_chartParametrization_include {M : Type*}
    (f : Quotient O.setoid → M) (i : ι) :
    f ∘ chartParametrization U hU (O.include i) =
      chartParametrization U hU (f ∘ O.include i) := rfl

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem chosenChart_spacetime_pullbackCoefficients_eq
    (q : Quotient O.setoid) (i : ι)
    (hi : letI := quotientChartedSpace U hU O
      ⇑(extChartAt (𝓡 n) q).symm = chartParametrization U hU (O.include i))
    (g : ℝ → RiemannianMetric n M) (f : ℝ → Quotient O.setoid → M) :
    letI := quotientChartedSpace U hU O
    (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g z.1).pullbackCoefficients (f z.1 ∘ (extChartAt (𝓡 n) q).symm) z.2) =
    (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g z.1).pullbackCoefficients
        (chartParametrization U hU (f z.1 ∘ O.include i)) z.2) := by
  let := quotientChartedSpace U hU O
  simp only [hi, comp_chartParametrization_include U hU O]

theorem chosenChart_spacetime_pullbackCoefficients_iteratedFDeriv_eq
    (q : Quotient O.setoid) (i : ι)
    (hi : letI := quotientChartedSpace U hU O
      ⇑(extChartAt (𝓡 n) q).symm = chartParametrization U hU (O.include i))
    (g : ℝ → RiemannianMetric n M) (f : ℝ → Quotient O.setoid → M) (m : ℕ) :
    letI := quotientChartedSpace U hU O
    iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g z.1).pullbackCoefficients (f z.1 ∘ (extChartAt (𝓡 n) q).symm) z.2) =
    iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g z.1).pullbackCoefficients
        (chartParametrization U hU (f z.1 ∘ O.include i)) z.2) := by
  let := quotientChartedSpace U hU O
  rw [chosenChart_spacetime_pullbackCoefficients_eq U hU O q i hi g f]

end PoincareConjecture.ChartDistance
