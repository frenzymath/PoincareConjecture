import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Boundary
import Mathlib.Topology.Algebra.Module.Cardinality









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface.Euler

theorem eqvGen_of_finite_closed_cover {X I : Type*} [TopologicalSpace X] [Finite I]
    {S : Set X} (hS : IsPreconnected S) (A : I → Set X)
    (hclosed : ∀ i, IsClosed (A i)) (hcover : S ⊆ ⋃ i, A i)
    (hne : ∀ i, (S ∩ A i).Nonempty) (i j : I) :
    Relation.EqvGen (fun a b => (S ∩ (A a ∩ A b)).Nonempty) i j := by
  classical
  let R := Relation.EqvGen (fun a b => (S ∩ (A a ∩ A b)).Nonempty)
  let U : Set X := ⋃ a : {a // R i a}, A a
  let V : Set X := ⋃ a : {a // ¬ R i a}, A a
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun a => hclosed a)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun a => hclosed a)
  have hUV : S ⊆ U ∪ V := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover hx)
    by_cases h : R i a
    · exact Or.inl (mem_iUnion.mpr ⟨⟨a, h⟩, ha⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨a, h⟩, ha⟩)
  by_contra hij
  obtain ⟨x, hxS, hxU, hxV⟩ := isPreconnected_closed_iff.mp hS U V hU hV hUV
    (by obtain ⟨x, hxS, hxi⟩ := hne i
        exact ⟨x, hxS, mem_iUnion.mpr ⟨⟨i, Relation.EqvGen.refl i⟩, hxi⟩⟩)
    (by obtain ⟨x, hxS, hxj⟩ := hne j
        exact ⟨x, hxS, mem_iUnion.mpr ⟨⟨j, hij⟩, hxj⟩⟩)
  obtain ⟨a, ha⟩ := mem_iUnion.mp hxU
  obtain ⟨b, hb⟩ := mem_iUnion.mp hxV
  exact b.property (Relation.EqvGen.trans _ _ _ a.property
    (Relation.EqvGen.rel _ _ ⟨x, hxS, ha, hb⟩))

private theorem isPreconnected_of_dense_local {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {S : Set X} (hS : Dense S)
    (hlocal : ∀ p : X, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ IsPreconnected (U ∩ S)) :
    IsPreconnected S := by
  apply isPreconnected_closed_iff.mpr
  intro A B hA hB hcover hneA hneB
  by_contra hnone
  have hsep : ∀ x ∈ S, x ∈ A → x ∈ B → False :=
    fun x hx ha hb => hnone ⟨x, hx, ha, hb⟩
  have hlocal_side (p : X) : p ∈ interior A ∪ interior B := by
    obtain ⟨U, hU, hpU, hconn⟩ := hlocal p
    have hside : U ∩ S ⊆ A ∨ U ∩ S ⊆ B := by
      by_cases hmeet : (U ∩ S ∩ A).Nonempty
      · left
        intro x hx
        rcases hcover hx.2 with ha | hb
        · exact ha
        · obtain ⟨y, hy, hya, hyb⟩ := isPreconnected_closed_iff.mp hconn A B hA hB
            (fun z hz => hcover hz.2) hmeet ⟨x, hx, hb⟩
          exact (hsep y hy.2 hya hyb).elim
      · right
        intro x hx
        exact (hcover hx.2).resolve_left (fun ha => hmeet ⟨x, hx, ha⟩)
    have hclosure : U ⊆ closure (U ∩ S) := by
      intro x hx
      apply _root_.mem_closure_iff.mpr
      intro W hW hxW
      obtain ⟨y, ⟨hyW, hyU⟩, hyS⟩ :=
        hS.inter_open_nonempty (W ∩ U) (hW.inter hU) ⟨x, hxW, hx⟩
      exact ⟨y, hyW, hyU, hyS⟩
    rcases hside with ha | hb
    · exact Or.inl (interior_maximal (hclosure.trans (closure_minimal ha hA)) hU hpU)
    · exact Or.inr (interior_maximal (hclosure.trans (closure_minimal hb hB)) hU hpU)
  have hinter : (interior A ∩ interior B).Nonempty := by
    apply nonempty_inter isOpen_interior isOpen_interior
    · exact eq_univ_of_forall hlocal_side
    · obtain ⟨x, hxS, hxA⟩ := hneA
      exact ⟨x, (hlocal_side x).resolve_right (fun hxB => hsep x hxS hxA (interior_subset hxB))⟩
    · obtain ⟨x, hxS, hxB⟩ := hneB
      exact ⟨x, (hlocal_side x).resolve_left (fun hxA => hsep x hxS (interior_subset hxA) hxB)⟩
  obtain ⟨x, ⟨hxA, hxB⟩, hxS⟩ :=
    hS.inter_open_nonempty _ (isOpen_interior.inter isOpen_interior) hinter
  exact hsep x hxS (interior_subset hxA) (interior_subset hxB)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

theorem dense_compl_finite {V : Set M} (hV : V.Finite) : Dense Vᶜ := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨p, hp⟩
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) p
  have hpc : p ∈ c.source := mem_chart_source _ p
  have hO : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.symm.isOpen_inter_preimage hU
  have hpO : c p ∈ c.target ∩ c.symm ⁻¹' U := by
    exact ⟨c.map_source hpc, by simpa only [mem_preimage, c.left_inv hpc] using hp⟩
  obtain ⟨z, hzO, hzV⟩ := ((hV.image c).countable.dense_compl (𝕜 := ℝ)).inter_open_nonempty
    _ hO ⟨c p, hpO⟩
  refine ⟨c.symm z, hzO.2, ?_⟩
  intro hz
  exact hzV ⟨c.symm z, hz, c.right_inv hzO.1⟩

theorem isPreconnected_compl_finite [PreconnectedSpace M] {V : Set M} (hV : V.Finite) :
    IsPreconnected Vᶜ := by
  apply isPreconnected_of_dense_local (dense_compl_finite hV)
  intro p
  obtain ⟨r, hr, htarget⟩ := exists_chart_closedBall_subset p
  let U := (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
    ball (chartAt (EuclideanSpace ℝ (Fin 2)) p p) r
  exact ⟨U, isOpen_chart_ball p htarget, mem_chart_ball p hr,
    isPreconnected_chart_ball_sdiff_finite p hr (ball_subset_closedBall.trans htarget) hV⟩

end PoincareConjecture.Topology.Surface.Euler
