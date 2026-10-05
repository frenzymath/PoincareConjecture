import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CapMetricScalingNeck
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.ScalarGradientHomothety
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.ScalarEvolutionHomothety
import Mathlib.Data.Real.Pointwise

/-!
# Actual scalar readouts for positive cap metric scaling

Scalar suprema retain Mathlib's empty and unbounded range conventions.
The gradient and evolution
numerator are the actual chosen-connection readouts, transported by the
identity local homothety. Source: Definition 9.72 and the scale invariance
observation after Claim 9.74, pp. 230-231; cap-metric-scaling.md.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M13

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]
  {g : RiemannianMetric 3 M}

/-- Positive metric scaling divides the frozen scalar supremum, including
empty and unbounded ranges (Definition 9.72, pp. 230-231). -/
theorem scaleSmoothMetric_scalarCurvatureSupOn (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (X : Set M) :
    scalarCurvatureSupOn (scaleSmoothMetric g Q hQ) (scaleLeviCivitaData D Q hQ) X =
      scalarCurvatureSupOn g D X / Q := by
  change (⨆ z : X, (scaleLeviCivitaData D Q hQ).scalarCurvature z.1) =
    (⨆ z : X, D.scalarCurvature z.1) / Q
  simp_rw [scaleLeviCivitaData_scalarCurvature, div_eq_mul_inv]
  simpa only [smul_eq_mul, mul_comm] using
    (Real.smul_iSup_of_nonneg (inv_nonneg.mpr hQ.le)
      (fun z : X => D.scalarCurvature z.1)).symm

/-- Powers of a nonnegative actual scalar supremum acquire the inverse
metric factor (Definition 9.72, pp. 230-231). -/
theorem scaleSmoothMetric_scalarCurvatureSupOn_rpow (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (X : Set M)
    (hS : 0 ≤ scalarCurvatureSupOn g D X) (p : ℝ) :
    scalarCurvatureSupOn (scaleSmoothMetric g Q hQ) (scaleLeviCivitaData D Q hQ) X ^ p =
      Q ^ (-p) * scalarCurvatureSupOn g D X ^ p := by
  rw [scaleSmoothMetric_scalarCurvatureSupOn D Q hQ X,
    Real.div_rpow hS hQ.le, Real.rpow_neg hQ.le, div_eq_mul_inv, mul_comm]

/-- The frozen scalar-gradient norm has the inverse three-halves factor
for the literal scaled metric and connection (Definition 9.72, p. 231). -/
theorem scaleSmoothMetric_scalarGradientNorm (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (x : M) :
    scalarGradientNorm (scaleSmoothMetric g Q hQ) (scaleLeviCivitaData D Q hQ) x =
      scalarGradientNorm g D x / Q ^ (3 / 2 : ℝ) := by
  apply scalarGradientNorm_eq_of_local_homothety
    (scaleLeviCivitaData D Q hQ) D hQ (f := id) isOpen_univ
    contMDiff_id.contMDiffOn ?_ (mem_univ x)
  intro y _ v w
  simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq, scaleSmoothMetric_inner]

end PoincareMT.M13

namespace PoincareMT.M13

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {g : RiemannianMetric n M}

/-- The actual scalar-evolution numerator has inverse-square metric scale
(Definition 9.72 and Claim 9.74, p. 231). -/
theorem scaleLeviCivitaData_scalarEvolution (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (x : M) :
    (scaleLeviCivitaData D Q hQ).laplacian
        (scaleLeviCivitaData D Q hQ).scalarCurvature x +
      2 * (scaleLeviCivitaData D Q hQ).ricciNormSq x =
      (D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x) / Q ^ 2 := by
  apply (scaleLeviCivitaData D Q hQ).scalarEvolutionNumerator_eq_of_local_homothety
    D hQ (f := id) isOpen_univ contMDiff_id.contMDiffOn ?_ (mem_univ x)
  intro y _ v w
  simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq, scaleSmoothMetric_inner]

end PoincareMT.M13

namespace PoincareMT.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

omit [T2Space M] in
/-- The actual cap's scalar ratio bounds every scalar range in its carrier
(Definition 9.72(5), p. 230). -/
theorem scalar_range_bddAbove_on_subset {X : Set M} (hX : X ⊆ N.carrier) :
    BddAbove (range (fun z : X => N.connection.scalarCurvature z.1)) := by
  obtain ⟨o, ho⟩ := N.core_nonempty
  have hoc : o ∈ N.carrier := by
    rw [N.core_eq_interior_closed_core] at ho
    have ho' := interior_subset ho
    rw [N.closed_core_eq_complement_end] at ho'
    exact ho'.1
  obtain ⟨b, _, hb⟩ := N.scalar_ratio
  refine ⟨b * N.connection.scalarCurvature o, ?_⟩
  rintro r ⟨z, rfl⟩
  exact hb o hoc z.1 (hX z.2)

omit [T2Space M] in
/-- Scalar positivity and the bounded actual cap range give a positive
frozen supremum on every nonempty subset (Definition 9.72(4)-(5), p. 230). -/
theorem scalarSup_pos_on_subset {X : Set M} (hX : X ⊆ N.carrier) (hne : X.Nonempty) :
    0 < scalarCurvatureSupOn g N.connection X := by
  obtain ⟨x, hx⟩ := hne
  exact (N.scalar_pos x (hX hx)).trans_le
    (le_csSup (N.scalar_range_bddAbove_on_subset hX) ⟨⟨x, hx⟩, rfl⟩)

end PoincareMT.CapCertificate
