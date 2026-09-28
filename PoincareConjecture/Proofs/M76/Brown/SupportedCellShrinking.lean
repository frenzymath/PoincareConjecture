import PoincareConjecture.Proofs.M76.Brown.ClosedBallCompression
import PoincareConjecture.Proofs.M76.Mathlib.ClosedExtension
import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas











set_option autoImplicit false

open Set Metric

namespace Set

variable {X E Y : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [PseudoMetricSpace Y]





theorem IsUnitBallPair.exists_supported_shrinking
    {Q T : Set X} (hpair : IsUnitBallPair E Q (frontier Q))
    (hQ : IsClosed Q) (hT : IsCompact T) (hTQ : T ⊆ interior Q)
    (F : X → Y) (hF : ContinuousOn F Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : X ≃ₜ X, EqOn h id (interior Q)ᶜ ∧
      ∀ x ∈ T, ∀ y ∈ T, dist (F (h x)) (F (h y)) < ε := by
  obtain ⟨_, e, he⟩ := hpair
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let j : T → Q := fun x => ⟨x, interior_subset (hTQ x.property)⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let f : T → E := fun x => (e (j x) : E)
  have hf : Continuous f := continuous_subtype_val.comp (e.continuous.comp hj)
  have hfb : range f ⊆ ball (0 : E) 1 := by
    rintro _ ⟨x, rfl⟩
    apply mem_ball_zero_iff.mpr
    have hn : ‖f x‖ ≤ 1 := mem_closedBall_zero_iff.mp (e (j x)).property
    apply lt_of_le_of_ne hn
    intro hnorm
    have hfront : (x : X) ∈ frontier Q := (he (j x)).mpr
      (mem_sphere_zero_iff_norm.mpr hnorm)
    exact (mem_frontier_iff_notMem_interior (interior_subset (hTQ x.property))).mp
      hfront (hTQ x.property)
  obtain ⟨r, hr, hfr⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ) < 1)
    (isCompact_range hf).isClosed hfb
  let G : closedBall (0 : E) 1 → Y := fun x => F (e.symm x)
  have hG : Continuous G := hF.domRestrict.comp e.symm.continuous
  let z : closedBall (0 : E) 1 := ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨η, hη, hGη⟩ := Metric.continuousAt_iff.mp (hG.continuousAt (x := z))
    (ε / 2) (half_pos hε)
  obtain ⟨c, hcfix, hcsmall⟩ := Homeomorph.exists_closedBallCompression (E := E) hr.2 hη
  let g : Q ≃ₜ Q := (e.trans c).trans e.symm
  have hgfix (x : Q) (hx : (x : X) ∈ frontier Q) : g x = x := by
    apply e.injective
    change e (e.symm (c (e x))) = e x
    rw [e.apply_symm_apply, hcfix (e x) ((he x).mp hx)]
  let h := g.closedExtension hQ hgfix
  have hcoord {x : X} (hx : x ∈ T) :
      F (h x) = G (c (e ⟨x, interior_subset (hTQ hx)⟩)) := by
    rw [show h x = (g ⟨x, interior_subset (hTQ hx)⟩ : X) from
      g.closedExtension_apply_mem hQ hgfix (interior_subset (hTQ hx))]
    rfl
  have hsmall {x : X} (hx : x ∈ T) : dist (F (h x)) (G z) < ε / 2 := by
    rw [hcoord hx]
    apply hGη
    have hxr : ‖(e ⟨x, interior_subset (hTQ hx)⟩ : E)‖ ≤ r :=
      (mem_ball_zero_iff.mp (hfr (mem_range_self (⟨x, hx⟩ : T)))).le
    have hc := hcsmall (e ⟨x, interior_subset (hTQ hx)⟩) hxr
    simpa only [Subtype.dist_eq, z, dist_zero_right] using hc
  refine ⟨h, ?_, ?_⟩
  · intro x hx
    by_cases hxQ : x ∈ Q
    · exact g.closedExtension_apply_frontier hQ hgfix
        ((mem_frontier_iff_notMem_interior hxQ).mpr hx)
    · exact g.closedExtension_apply_notMem hQ hgfix hxQ
  · intro x hx y hy
    have hy' : dist (G z) (F (h y)) < ε / 2 := by
      rw [dist_comm]
      exact hsmall hy
    calc
      dist (F (h x)) (F (h y)) ≤ dist (F (h x)) (G z) + dist (G z) (F (h y)) :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hsmall hx) hy'
      _ = ε := by ring

end Set
