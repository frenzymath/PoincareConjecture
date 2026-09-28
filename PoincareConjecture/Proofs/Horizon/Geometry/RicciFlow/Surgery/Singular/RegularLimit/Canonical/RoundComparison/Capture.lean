import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.Component
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.CompactCapture








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open SingularRegularLimit.RoundComparison

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem exists_compact_roundComponent_carrier_capture
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hepsilon : H.epsilon ≤ roundComparisonThreshold)
    {x : M} (hx : x ∈ H.reference.regularLimitSet) :
    ∃ A : Set M, IsCompact A ∧ A ⊆ H.reference.regularLimitSet ∧
      ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
        ∀ t (ht : t ∈ Ico H.reference.tMinus T), s ≤ t →
          ∀ N : SingularRoundComponent (F.metric t) H.epsilon,
            H.reference.forward t ht x ∈ N.carrier →
            closure (H.reference.inverse t ht '' N.carrier) ⊆ A := by
  obtain ⟨a, B, U, ha, haT, _, _, hxU, _, hbound⟩ :=
    H.exists_open_uniform_scalar_tail P04 hx
  obtain ⟨A, hA, hAreg, b, _, hbT, hcapture⟩ :=
    H.exists_compact_containing_scalar_sublevel_tail P04 (2 * B)
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
  change H.reference.scalar t (H.reference.inverse t ht z) ≤ 2 * B
  dsimp only [SingularTimeReference.scalar]
  rw [← H.reference.scalar_pullback t ht (H.reference.inverse t ht z),
    H.reference.right_inverse t ht z]
  exact (N.scalar_le_two_mul (F.connection t) hepsilon hxN hz).trans
    (mul_le_mul_of_nonneg_left hcenter (by norm_num))

end PoincareConjecture.SingularTimeAssumptions
