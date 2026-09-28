import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.CompactCapture
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Curvature.Pinching
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace SingularCComponent

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {C : ℝ}

theorem scalar_sup_le_constant_div_six_mul (N : SingularCComponent g D C)
    {x : M} (hx : x ∈ N.carrier) :
    scalarCurvatureSupOn g D N.carrier ≤ (C / 6) * D.scalarCurvature x := by
  have htrace := normalization_scalarCurvature_lower_bound D x
    (C⁻¹ * scalarCurvatureSupOn g D N.carrier) (by
      intro v w hvw
      have h := (N.sectional_lower x hx v w hvw).le
      simpa only [LeviCivitaData.sectionalCurvature, hvw.1, hvw.2.1, hvw.2.2,
        mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, div_one] using h)
  have hmul := mul_le_mul_of_nonneg_left htrace N.constant_pos.le
  have heq : C * (6 * (C⁻¹ * scalarCurvatureSupOn g D N.carrier)) =
      6 * scalarCurvatureSupOn g D N.carrier := by
    field_simp [ne_of_gt N.constant_pos]
  rw [heq] at hmul
  linarith

theorem scalar_le_constant_div_six_mul (N : SingularCComponent g D C)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    D.scalarCurvature y ≤ (C / 6) * D.scalarCurvature x := by
  obtain ⟨B, hB⟩ := N.compact.bddAbove_image D.continuous_scalarCurvature.continuousOn
  have hbounded : BddAbove (range (fun z : N.carrier => D.scalarCurvature z.1)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hB ⟨z.1, z.2, rfl⟩
  exact (le_csSup hbounded ⟨⟨y, hy⟩, rfl⟩).trans
    (N.scalar_sup_le_constant_div_six_mul hx)

end SingularCComponent

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_compact_cComponent_carrier_capture
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {x : M} (hx : x ∈ H.reference.regularLimitSet) :
    ∃ A : Set M, IsCompact A ∧ A ⊆ H.reference.regularLimitSet ∧
      ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
        ∀ t (ht : t ∈ Ico H.reference.tMinus T), s ≤ t →
          ∀ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
            H.reference.forward t ht x ∈ N.carrier →
            closure (H.reference.inverse t ht '' N.carrier) ⊆ A := by
  obtain ⟨a, B, U, ha, haT, _, _, hxU, _, hbound⟩ :=
    H.exists_open_uniform_scalar_tail P04 hx
  obtain ⟨A, hA, hAreg, b, _, hbT, hcapture⟩ :=
    H.exists_compact_containing_scalar_sublevel_tail P04 ((H.constant / 6) * B)
  refine ⟨A, hA, hAreg, max a b, ha.trans_le (le_max_left _ _), max_lt haT hbT, ?_⟩
  intro t ht hst N hxN
  have hat : a ≤ t := (le_max_left a b).trans hst
  have hbt : b ≤ t := (le_max_right a b).trans hst
  have hcenter : (F.connection t).scalarCurvature (H.reference.forward t ht x) ≤ B := by
    rw [H.reference.scalar_pullback t ht x]
    exact hbound t ⟨hat, ht.2⟩ x hxU
  apply closure_minimal _ hA.isClosed
  rintro y ⟨z, hz, rfl⟩
  apply hcapture t ⟨hbt, ht.2⟩
  change H.reference.scalar t (H.reference.inverse t ht z) ≤ (H.constant / 6) * B
  dsimp only [SingularTimeReference.scalar]
  rw [← H.reference.scalar_pullback t ht (H.reference.inverse t ht z),
    H.reference.right_inverse t ht z]
  exact (N.scalar_le_constant_div_six_mul hxN hz).trans
    (mul_le_mul_of_nonneg_left hcenter (by positivity [H.constant_pos]))

end SingularTimeAssumptions

end PoincareConjecture
