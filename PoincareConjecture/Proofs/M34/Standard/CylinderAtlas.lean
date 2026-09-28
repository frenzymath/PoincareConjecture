import PoincareConjecture.Definitions.Ch12.StandardCap










set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture

set_option maxHeartbeats 800000 in



theorem nonempty_standardCylinderAtlas : Nonempty StandardCylinderAtlas := by
  classical
  let E := EuclideanSpace ℝ (Fin 2)
  let c := fun q : UnitTwoSphere => chartAt E q
  have hballs : ∀ q : UnitTwoSphere, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (c q q) r ⊆ (c q).target := by
    intro q
    exact Metric.nhds_basis_closedBall.mem_iff.mp
      ((c q).open_target.mem_nhds ((c q).map_source (mem_chart_source E q)))
  choose r hr htarget using hballs
  let U : UnitTwoSphere → Set UnitTwoSphere := fun q =>
    (c q).source ∩ (c q) ⁻¹' Metric.ball (c q q) (r q)
  have hUopen : ∀ q, IsOpen (U q) := fun q =>
    (c q).continuousOn.isOpen_inter_preimage (c q).open_source Metric.isOpen_ball
  have hcover : (univ : Set UnitTwoSphere) ⊆ ⋃ q, U q := by
    intro q _
    refine mem_iUnion.mpr ⟨q, ?_⟩
    change q ∈ (c q).source ∧ c q q ∈ Metric.ball (c q q) (r q)
    exact ⟨mem_chart_source E q, Metric.mem_ball_self (hr q)⟩
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (univ : Set UnitTwoSphere)).elim_finite_subcover
    U hUopen hcover
  let e := (Fintype.equivFin s).symm
  refine ⟨{
    count := Fintype.card s
    chart := fun i => c (e i)
    chart_mem := fun i => chart_mem_atlas E (e i).val
    domain := fun i => Metric.closedBall (c (e i) (e i)) (r (e i))
    domain_compact := fun i => isCompact_closedBall _ _
    domain_subset := fun i => htarget (e i)
    covers := ?_
  }⟩
  intro x
  obtain ⟨q, hq, hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  let j : s := ⟨q, hq⟩
  refine ⟨e.symm j, ?_⟩
  simpa only [Equiv.apply_symm_apply] using
    (show x ∈ (c j).source ∧ c j x ∈ interior (Metric.closedBall (c j j) (r j)) from
      ⟨hx.1, Metric.ball_subset_interior_closedBall hx.2⟩)

end PoincareConjecture
