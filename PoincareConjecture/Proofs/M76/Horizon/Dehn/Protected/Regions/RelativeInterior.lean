import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import Mathlib.Analysis.Convex.Topology









set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.Dehn

theorem mem_relative_interior_closure_of_frontier_patch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R U V : Set E} (hR : IsClosed R) (hcR : Convex ℝ R)
    (hiR : (interior R).Nonempty) (hU : IsOpen U) (hUR : U ⊆ R)
    (hV : IsOpen V) {q : R} (hqV : (q : E) ∈ V)
    (hq : (q : E) ∈ closure U)
    (hfront : frontier U ∩ V ⊆ frontier R) :
    q ∈ interior (Subtype.val ⁻¹' closure U : Set R) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV q hqV
  have hUI : U ⊆ interior R := interior_maximal hUR hU
  have hconn : IsPreconnected (ball (q : E) r ∩ interior R) :=
    ((convex_ball (q : E) r).inter hcR.interior).isPreconnected
  have hdis : Disjoint (frontier U) (ball (q : E) r ∩ interior R) := by
    apply Set.disjoint_left.mpr
    intro x hx hxN
    exact (hfront ⟨hx, hball hxN.1⟩).2 hxN.2
  have hmeet : ((ball (q : E) r ∩ interior R) ∩ U).Nonempty := by
    obtain ⟨x, hxN, hxU⟩ := mem_closure_iff.mp hq _ isOpen_ball (mem_ball_self hr)
    exact ⟨x, ⟨hxN, hUI hxU⟩, hxU⟩
  have hsub : ball (q : E) r ∩ interior R ⊆ U :=
    hconn.m76_subset_of_disjoint_frontier hU hdis hmeet
  have hdense : closure (interior R) = R := by
    rw [hcR.closure_interior_eq_closure_of_nonempty_interior hiR, hR.closure_eq]
  have hclosed : ball (q : E) r ∩ R ⊆ closure U := by
    intro x hx
    apply closure_mono hsub
    apply _root_.mem_closure_iff.mpr
    intro W hW hxW
    have hxI : x ∈ closure (interior R) := hdense.symm.subset hx.2
    obtain ⟨y, hy, hyI⟩ := mem_closure_iff.mp hxI _ (hW.inter isOpen_ball) ⟨hxW, hx.1⟩
    exact ⟨y, hy.1, hy.2, hyI⟩
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset
    ((isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hr))
  intro x hx
  exact hclosed ⟨hx, x.property⟩

end PoincareConjecture.M76.Dehn
