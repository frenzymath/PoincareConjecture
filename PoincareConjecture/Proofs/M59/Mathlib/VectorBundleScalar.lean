import Mathlib.Topology.VectorBundle.Basic

set_option autoImplicit false

open Bundle Set Topology

variable {R B F X : Type*} {E : B → Type*}
  [NontriviallyNormedField R] [NormedAddCommGroup F] [NormedSpace R F]
  [TopologicalSpace B] [TopologicalSpace X]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle R F E]

theorem Continuous.totalSpace_smul {f : X → TotalSpace F E} {c : X → R}
    (hf : Continuous f) (hc : Continuous c) :
    Continuous (fun x => (⟨(f x).proj, c x • (f x).2⟩ : TotalSpace F E)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have h := (FiberBundle.continuousAt_totalSpace F f).mp (hf.continuousAt (x := x))
  apply (FiberBundle.continuousAt_totalSpace F _).mpr
  refine ⟨h.1, ?_⟩
  let e := trivializationAt F E (f x).proj
  apply (hc.continuousAt.smul h.2).congr_of_eventuallyEq
  filter_upwards [h.1 (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E (f x).proj))]
    with y hy
  exact (e.linear R hy).map_smul (c y) (f y).2
