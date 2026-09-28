import PoincareConjecture.Proofs.M07.Topology.Exhaustion
import Mathlib.Topology.Order.Basic











set_option autoImplicit false

open Set Topology



theorem IsOpen.frontier_connectedComponentIn_subset
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {V : Set X} (hV : IsOpen V) (p : X) :
    frontier (connectedComponentIn V p) ⊆ frontier V := by
  intro q hq
  refine ⟨closure_mono (connectedComponentIn_subset V p) hq.1, ?_⟩
  rw [hV.interior_eq]
  intro hqV
  have hqC : q ∈ connectedComponentIn V q := mem_connectedComponentIn hqV
  obtain ⟨y, hyq, hyp⟩ := mem_closure_iff_nhds.mp hq.1
    (connectedComponentIn V q) (hV.connectedComponentIn.mem_nhds hqC)
  have heq : connectedComponentIn V q = connectedComponentIn V p :=
    (connectedComponentIn_eq hyq).trans (connectedComponentIn_eq hyp).symm
  apply hq.2
  rw [hV.connectedComponentIn.interior_eq]
  exact heq ▸ hqC



theorem Continuous.exists_connected_sublevel_exhaustion
    {X α : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [LocallyConnectedSpace X] [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {f : X → α} (hf : Continuous f) (base : X) (r : ℕ → α)
    (hr : StrictMono r) (hbase : ∀ n, f base < r n)
    (hcompact : ∀ n, IsCompact {x | f x ≤ r n})
    (hcofinal : ∀ x, ∃ n, f x < r n) :
    ∃ U : ℕ → Set X,
      (∀ n, IsOpen (U n)) ∧ (∀ n, IsConnected (U n)) ∧
      (∀ n, base ∈ U n) ∧ (∀ n, IsCompact (closure (U n))) ∧
      (∀ n, closure (U n) ⊆ U (n + 1)) ∧ (⋃ n, U n) = univ ∧
      ∀ n x, x ∈ frontier (U n) → f x = r n := by
  let V : ℕ → Set X := fun n => {x | f x < r n}
  have hV (n : ℕ) : IsOpen (V n) := isOpen_lt hf continuous_const
  have hbaseV (n : ℕ) : base ∈ V n := hbase n
  have hVm : Monotone V := fun i j hij _ hx => hx.trans_le (hr.monotone hij)
  have hVc (n : ℕ) : closure (V n) ⊆ {x | f x ≤ r n} :=
    (isClosed_le hf continuous_const).closure_subset_iff.mpr (fun _ hx => hx.le)
  have hcover : (⋃ n, V n) = univ := iUnion_eq_univ_iff.mpr hcofinal
  refine ⟨fun n => connectedComponentIn (V n) base,
    fun n => (hV n).connectedComponentIn,
    fun n => isConnected_connectedComponentIn_iff.mpr (hbaseV n),
    fun n => mem_connectedComponentIn (hbaseV n), ?_, ?_,
    Poincare.iUnion_connectedComponentIn_eq_univ V hV hVm hcover base, ?_⟩
  · intro n
    exact (hcompact n).of_isClosed_subset isClosed_closure
      ((closure_mono (connectedComponentIn_subset _ _)).trans (hVc n))
  · intro n
    apply isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn (hbaseV n)))
    intro x hx
    exact (hVc n (closure_mono (connectedComponentIn_subset _ _) hx)).trans_lt
      (hr (Nat.lt_succ_self n))
  · intro n x hx
    exact frontier_lt_subset_eq hf continuous_const
      ((hV n).frontier_connectedComponentIn_subset base hx)
