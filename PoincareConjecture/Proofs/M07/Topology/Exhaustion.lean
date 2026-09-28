import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.LocallyConnected

open Set Topology

namespace Poincare

variable {X : Type*} [TopologicalSpace X]

theorem iUnion_connectedComponentIn_eq_univ [PreconnectedSpace X]
    [LocallyConnectedSpace X] (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n))
    (hmono : Monotone U) (hcover : ⋃ n, U n = univ) (base : X) :
    (⋃ n, connectedComponentIn (U n) base) = univ := by
  let V := ⋃ n, connectedComponentIn (U n) base
  have hopen : IsOpen V := isOpen_iUnion fun n => (hU n).connectedComponentIn
  have hclosed : IsClosed V := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp hcover x
    refine mem_nhds_iff.mpr
      ⟨connectedComponentIn (U n) x, ?_, (hU n).connectedComponentIn,
        mem_connectedComponentIn hn⟩
    intro y hy hyV
    obtain ⟨m, hm⟩ := mem_iUnion.mp hyV
    have hym : y ∈ connectedComponentIn (U (max n m)) base :=
      connectedComponentIn_mono base (hmono (le_max_right n m)) hm
    have hsub : connectedComponentIn (U n) x ⊆
        connectedComponentIn (U (max n m)) y :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hy
        ((connectedComponentIn_subset _ _).trans (hmono (le_max_left n m)))
    have hxm := hsub (mem_connectedComponentIn hn)
    rw [← connectedComponentIn_eq hym] at hxm
    exact hx (mem_iUnion.mpr ⟨max n m, hxm⟩)
  apply (show IsClopen V from ⟨hclosed, hopen⟩).eq_univ
  obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp hcover base
  exact ⟨base, mem_iUnion.mpr ⟨n, mem_connectedComponentIn hn⟩⟩

theorem CompactExhaustion.exists_connected_open_exhaustion [T2Space X]
    [PreconnectedSpace X] [LocallyConnectedSpace X] (K : CompactExhaustion X)
    (base : X) :
    ∃ U : ℕ → Set X,
      (∀ n, IsOpen (U n)) ∧
      (∀ n, IsConnected (U n)) ∧
      (∀ n, IsCompact (closure (U n))) ∧
      (∀ n, U n ⊆ U (n + 1)) ∧
      (⋃ n, U n = univ) ∧
      (∀ n, base ∈ U n) := by
  obtain ⟨b, hb⟩ := K.exists_mem base
  let V : ℕ → Set X := fun n => interior (K (n + (b + 1)))
  have hVmono : Monotone V := fun _ _ h => interior_mono (K.subset (Nat.add_le_add_right h _))
  have hbase : ∀ n, base ∈ V n := by
    intro n
    exact K.subset_interior (by omega) hb
  have hcover : ⋃ n, V n = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n, K.subset_interior (by omega) hn⟩
  refine ⟨fun n => connectedComponentIn (V n) base,
    fun _ => isOpen_interior.connectedComponentIn,
    fun n => isConnected_connectedComponentIn_iff.mpr (hbase n), ?_,
    fun n => connectedComponentIn_mono base (hVmono (Nat.le_succ n)),
    iUnion_connectedComponentIn_eq_univ V (fun _ => isOpen_interior) hVmono hcover base,
    fun n => mem_connectedComponentIn (hbase n)⟩
  intro n
  apply (K.isCompact (n + (b + 1))).of_isClosed_subset isClosed_closure
  exact closure_minimal
    ((connectedComponentIn_subset _ _).trans interior_subset) (K.isCompact _).isClosed

theorem exists_connected_open_exhaustion [T2Space X] [PreconnectedSpace X]
    [LocallyConnectedSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (base : X) :
    ∃ U : ℕ → Set X,
      (∀ n, IsOpen (U n)) ∧
      (∀ n, IsConnected (U n)) ∧
      (∀ n, IsCompact (closure (U n))) ∧
      (∀ n, U n ⊆ U (n + 1)) ∧
      (⋃ n, U n = univ) ∧
      (∀ n, base ∈ U n) :=
  CompactExhaustion.exists_connected_open_exhaustion (CompactExhaustion.choice X) base

end Poincare
