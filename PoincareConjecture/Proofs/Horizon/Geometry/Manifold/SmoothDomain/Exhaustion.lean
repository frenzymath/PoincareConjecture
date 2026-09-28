import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Component
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.FromEmbedding
import PoincareConjecture.Proofs.Horizon.Topology.Exhaustion

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold

private theorem exists_connected_compact_superset
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [LocallyCompactSpace M] [LocallyConnectedSpace M]
    [PreconnectedSpace M] (base : M) {C : Set M} (hC : IsCompact C) :
    ∃ L : Set M, IsCompact L ∧ IsConnected L ∧ C ⊆ L := by
  obtain ⟨U, ho, hc, hk, hnest, hcover, _⟩ :=
    Poincare.exists_connected_open_exhaustion base
  have hmono : Monotone U := monotone_nat_of_le_succ hnest
  obtain ⟨j, hj⟩ := hC.elim_directed_cover U ho (by rw [hcover]; exact subset_univ C)
    hmono.directed_le
  exact ⟨closure (U j), hk j, (hc j).closure, hj.trans subset_closure⟩

theorem exists_smoothDomain_superset
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    [PreconnectedSpace M] [NoncompactSpace M]
    {C : Set M} (hC : IsCompact C) :
    ∃ Ω : Set M, Nonempty (SmoothDomain (n + 1) Ω) ∧ C ⊆ Ω := by
  have : Nonempty M := by
    by_contra h
    let : IsEmpty M := not_nonempty_iff.mp h
    exact NoncompactSpace.noncompact_univ (X := M) isCompact_univ
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (n + 1))) M
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin (n + 1))) M
  obtain ⟨L, hL, hconn, hCL⟩ :=
    exists_connected_compact_superset (Classical.arbitrary M) hC
  obtain ⟨K, CS, hK, hLK, hman, hemb⟩ :=
    exists_compact_smooth_neighborhood (n := n)
      (E := EuclideanSpace ℝ (Fin (n + 1))) (by simp) hL
  let := CS
  let := hman
  obtain ⟨V, VS, _, hV, hcV, hLV, hmV, heV⟩ :=
    exists_connected_smooth_component hK hemb hconn hLK
  let := VS
  let := hmV
  exact ⟨interior V, nonempty_smoothDomain_interior hV hcV heV, hCL.trans hLV⟩

theorem exists_smoothDomain_exhaustion
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    [PreconnectedSpace M] [NoncompactSpace M] :
    ∃ Ω : ℕ → Set M,
      (∀ j, Nonempty (SmoothDomain (n + 1) (Ω j))) ∧
      (∀ j, closure (Ω j) ⊆ Ω (j + 1)) ∧
      (⋃ j, Ω j) = univ := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (n + 1))) M
  let K := CompactExhaustion.choice M
  choose F hF hCF using fun C : {C : Set M // IsCompact C} =>
    exists_smoothDomain_superset (n := n) C.property
  let V : ℕ → {Ω : Set M // Nonempty (SmoothDomain (n + 1) Ω)} :=
    Nat.rec ⟨F ⟨K 0, K.isCompact 0⟩, hF _⟩ fun j prev =>
      let C : {C : Set M // IsCompact C} :=
        ⟨closure prev.val ∪ K (j + 1),
          prev.property.some.isCompact_closure.union (K.isCompact _)⟩
      ⟨F C, hF C⟩
  refine ⟨fun j => (V j).val, fun j => (V j).property, ?_, ?_⟩
  · intro j x hx
    exact hCF ⟨closure (V j).val ∪ K (j + 1),
      (V j).property.some.isCompact_closure.union (K.isCompact _)⟩ (Or.inl hx)
  · apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨j, hj⟩ := K.exists_mem x
    refine ⟨j, ?_⟩
    cases j with
    | zero => exact hCF _ hj
    | succ j => exact hCF _ (Or.inr hj)

end Poincare.Manifold
