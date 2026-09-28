import Mathlib.Dynamics.Flow
import Mathlib.GroupTheory.Archimedean
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith












set_option autoImplicit false

open Set Function

namespace PoincareConjecture.M25.Topology3D

variable {X : Type*} [TopologicalSpace X]



theorem flow_orbit_surjective [PreconnectedSpace X] (φ : Flow ℝ X)
    (hopen : ∀ x, IsOpenMap (fun t : ℝ => φ t x)) (x : X) :
    Surjective (fun t : ℝ => φ t x) := by
  have ho (y : X) : IsOpen (range (fun t : ℝ => φ t y)) := by
    simpa only [image_univ] using hopen y univ isOpen_univ
  have hc : IsClosed (range (fun t : ℝ => φ t x)) := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_forall_mem_open.mpr
    intro y hy
    refine ⟨range (fun t : ℝ => φ t y), ?_, ho y, ⟨0, φ.map_zero_apply y⟩⟩
    rintro z ⟨t, rfl⟩ ⟨s, hs⟩
    change φ s x = φ t y at hs
    apply hy
    refine ⟨-t + s, ?_⟩
    change φ (-t + s) x = y
    rw [φ.map_add, hs, ← φ.map_add]
    simp
  have heq := (show IsClopen (range (fun t : ℝ => φ t x)) from ⟨hc, ho x⟩).eq_univ
    (range_nonempty (fun t : ℝ => φ t x))
  exact range_eq_univ.mp heq



def flowReturnTimes (φ : Flow ℝ X) (x : X) : AddSubgroup ℝ where
  carrier := {t | φ t x = x}
  zero_mem' := φ.map_zero_apply x
  add_mem' := by
    intro s t hs ht
    change φ (s + t) x = x
    rw [φ.map_add, ht, hs]
  neg_mem' := by
    intro t ht
    change φ (-t) x = x
    calc
      φ (-t) x = φ (-t) (φ t x) := congrArg (φ (-t)) ht.symm
      _ = x := by rw [← φ.map_add]; simp



theorem flow_eq_iff_sub_mem_returnTimes (φ : Flow ℝ X) (x : X) (s t : ℝ) :
    φ s x = φ t x ↔ s - t ∈ flowReturnTimes φ x := by
  change φ s x = φ t x ↔ φ (s - t) x = x
  constructor
  · intro h
    rw [sub_eq_add_neg, add_comm, φ.map_add, h, ← φ.map_add]
    simp
  · intro h
    calc
      φ s x = φ t (φ (s - t) x) := by rw [← φ.map_add]; congr 1; ring
      _ = φ t x := congrArg (φ t) h



theorem exists_positive_flow_period [CompactSpace X] [PreconnectedSpace X]
    (φ : Flow ℝ X) (hopen : ∀ y, IsOpenMap (fun t : ℝ => φ t y)) (x : X)
    (ε : ℝ) (hε : 0 < ε) (hinj : InjOn (fun t : ℝ => φ t x) (Ioo (-ε) ε)) :
    ∃ T : ℝ, 0 < T ∧ flowReturnTimes φ x = AddSubgroup.zmultiples T ∧
      Periodic (fun t : ℝ => φ t x) T := by
  have hsurj := flow_orbit_surjective φ hopen x
  have hnotinj : ¬Injective (fun t : ℝ => φ t x) := by
    intro hi
    let e : ℝ ≃ₜ X := (Equiv.ofBijective (fun t : ℝ => φ t x) ⟨hi, hsurj⟩)
      |>.toHomeomorphOfContinuousOpen (φ.continuous continuous_id continuous_const) (hopen x)
    have hcompact := isCompact_univ.image e.symm.continuous
    rw [image_univ, e.symm.surjective.range_eq] at hcompact
    exact noncompact_univ ℝ hcompact
  have hbot : flowReturnTimes φ x ≠ ⊥ := by
    intro h
    apply hnotinj
    intro s t hst
    have hm := (flow_eq_iff_sub_mem_returnTimes φ x s t).mp hst
    rw [h, AddSubgroup.mem_bot] at hm
    exact sub_eq_zero.mp hm
  have hd : Disjoint (flowReturnTimes φ x : Set ℝ) (Ioo 0 ε) := by
    apply disjoint_left.mpr
    intro t ht htI
    have htz := hinj ⟨by linarith [htI.1], htI.2⟩ ⟨by linarith, hε⟩
      (ht.trans (φ.map_zero_apply x).symm)
    exact htI.1.ne' htz
  obtain ⟨T, hT⟩ := AddSubgroup.exists_isLeast_pos hbot hε hd
  refine ⟨T, hT.1.2, ?_, ?_⟩
  · exact (AddSubgroup.cyclic_of_min hT).trans (AddSubgroup.zmultiples_eq_closure T).symm
  · intro t
    change φ (t + T) x = φ t x
    rw [φ.map_add]
    exact congrArg (φ t) hT.1.1



theorem exists_flow_circle_homeomorph [CompactSpace X] [PreconnectedSpace X] [T2Space X]
    (φ : Flow ℝ X) (hopen : ∀ y, IsOpenMap (fun t : ℝ => φ t y)) (x : X)
    (ε : ℝ) (hε : 0 < ε) (hinj : InjOn (fun t : ℝ => φ t x) (Ioo (-ε) ε)) :
    ∃ (T : ℝ), 0 < T ∧ ∃ e : AddCircle T ≃ₜ X,
      ∀ t : ℝ, e (t : AddCircle T) = φ t x := by
  obtain ⟨T, hT, hret, hp⟩ := exists_positive_flow_period φ hopen x ε hε hinj
  let : Fact (0 < T) := ⟨hT⟩
  have hi : Injective hp.lift := by
    intro a b
    induction a using Quotient.inductionOn' with | h s =>
      induction b using Quotient.inductionOn' with | h t =>
        intro hst
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        rw [← hret]
        exact (flow_eq_iff_sub_mem_returnTimes φ x s t).mp hst
  have hs : Surjective hp.lift := by
    intro y
    obtain ⟨t, ht⟩ := flow_orbit_surjective φ hopen x y
    exact ⟨(t : AddCircle T), ht⟩
  have hc : Continuous hp.lift :=
    (φ.continuous continuous_id continuous_const).quotient_lift _
  exact ⟨T, hT, hc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective hp.lift ⟨hi, hs⟩),
    fun _ => rfl⟩

end PoincareConjecture.M25.Topology3D
