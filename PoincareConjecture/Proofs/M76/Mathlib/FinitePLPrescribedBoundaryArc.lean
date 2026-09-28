import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.eq_of_subset_with_same_endpoints
    {U V : Set E} {a b : E}
    (hU : IsFinitePLBallPair ℝ U {a, b})
    (hV : IsFinitePLBallPair ℝ V {a, b})
    (hUV : U ⊆ V) (hab : a ≠ b) : U = V := by
  obtain ⟨e, _, hea, heb⟩ := hV.exists_unitInterval_chart_with_endpoints hab
  let f : U → ℝ := fun x => (e.symm ⟨x, hUV x.property⟩ : ℝ)
  have hf : Continuous f := continuous_subtype_val.comp
    (e.symm.continuous.comp (continuous_subtype_val.subtype_mk fun x => hUV x.property))
  letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU.isConnected
  have hcoordinate (t : Icc (0 : ℝ) 1) (ht : (e t : E) ∈ U) :
      (t : ℝ) ∈ range f := by
    refine ⟨⟨e t, ht⟩, ?_⟩
    change ((e.symm (e t) : Icc (0 : ℝ) 1) : ℝ) = t
    rw [e.symm_apply_apply]
  have hzero : (0 : ℝ) ∈ range f :=
    hcoordinate ⟨0, ⟨le_rfl, zero_le_one⟩⟩ (hea.symm ▸ hU.1 (by simp))
  have hone : (1 : ℝ) ∈ range f :=
    hcoordinate ⟨1, ⟨zero_le_one, le_rfl⟩⟩ (heb.symm ▸ hU.1 (by simp))
  have hall : Icc (0 : ℝ) 1 ⊆ range f :=
    (isPreconnected_range hf).Icc_subset hzero hone
  apply Subset.antisymm hUV
  intro x hx
  obtain ⟨u, hu⟩ := hall (e.symm ⟨x, hx⟩).property
  have heq : e.symm ⟨u, hUV u.property⟩ = e.symm ⟨x, hx⟩ := Subtype.ext hu
  have hux : (u : E) = x := congrArg Subtype.val (e.symm.injective heq)
  exact hux ▸ u.property

theorem IsFinitePLBallPair.exists_boundary_arc_complement
    {s q U : Set E} {a b : E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hU : IsFinitePLBallPair ℝ U {a, b})
    (hUq : U ⊆ q) (hab : a ≠ b) :
    ∃ V : Set E, IsFinitePLBallPair ℝ V {a, b} ∧
      U ∪ V = q ∧ U ∩ V = {a, b} := by
  obtain ⟨V, W, hV, hW, hVW, hinter⟩ := hs.exists_boundary_arcs
    (hUq (hU.1 (by simp))) (hUq (hU.1 (by simp))) hab
  have hcover : U \ {a, b} ⊆ V ∪ W := sdiff_subset.trans (hUq.trans hVW.symm.subset)
  have hside : U ⊆ V ∨ U ⊆ W := by
    by_cases hsub : U \ {a, b} ⊆ V
    · left
      intro x hx
      by_cases hm : x ∈ ({a, b} : Set E)
      · exact hV.1 hm
      · exact hsub ⟨hx, hm⟩
    · right
      obtain ⟨x, hx, hxV⟩ := not_subset.mp hsub
      have hxW : x ∈ W := (hcover hx).resolve_left hxV
      intro y hy
      by_cases hym : y ∈ ({a, b} : Set E)
      · exact hW.1 hym
      · by_contra hyW
        have hyV : y ∈ V := (hcover ⟨hy, hym⟩).resolve_right hyW
        obtain ⟨z, hz, hzVW⟩ :=
          isPreconnected_closed_iff.mp hU.isConnected_sdiff.isPreconnected V W
            hV.isCompact.isClosed hW.isCompact.isClosed hcover
            ⟨y, ⟨hy, hym⟩, hyV⟩ ⟨x, hx, hxW⟩
        exact hz.2 (hinter.subset hzVW)
  rcases hside with hUV | hUW
  · have heq := hU.eq_of_subset_with_same_endpoints hV hUV hab
    exact ⟨W, hW, heq.symm ▸ hVW, heq.symm ▸ hinter⟩
  · have heq := hU.eq_of_subset_with_same_endpoints hW hUW hab
    refine ⟨V, hV, ?_, ?_⟩
    · rw [heq, union_comm]
      exact hVW
    · rw [heq, inter_comm]
      exact hinter

end Set
