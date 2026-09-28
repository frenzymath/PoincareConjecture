import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.Compact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric.RadialHomeomorph

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {p : M}

theorem not_isLocalMax_distance (H : RadialHomeomorph g p)
    {x : M} (hxp : x ≠ p) :
    ¬IsLocalMax (fun y => (g.edist p y).toReal) x := by
  intro hmax
  let z := H.toHomeomorph.symm ⟨x, hxp⟩
  let c : {r : ℝ // r ∈ Ioi (0 : ℝ)} → M :=
    fun r => H.toHomeomorph (z.1, r)
  have hc : Continuous c := continuous_subtype_val.comp
    (H.toHomeomorph.continuous.comp (continuous_const.prodMk continuous_id))
  have hcz : c z.2 = x :=
    congrArg Subtype.val (H.toHomeomorph.apply_symm_apply ⟨x, hxp⟩)
  rw [← hcz] at hmax
  have hbound : ∀ᶠ (r : {r : ℝ // r ∈ Ioi (0 : ℝ)}) in 𝓝 z.2,
      (r : ℝ) ≤ (z.2 : ℝ) := by
    have h := hmax.comp_continuous hc.continuousAt
    change ∀ᶠ r in 𝓝 z.2,
      (g.edist p (c r)).toReal ≤ (g.edist p (c z.2)).toReal at h
    simpa only [c, H.distance_eq] using h
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hbound
  let t : {r : ℝ // r ∈ Ioi (0 : ℝ)} :=
    ⟨(z.2 : ℝ) + δ / 2, add_pos z.2.property (half_pos hδ)⟩
  have ht : t ∈ Metric.ball z.2 δ := by
    change dist ((z.2 : ℝ) + δ / 2) (z.2 : ℝ) < δ
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    linarith
  have hle := hball ht
  change (z.2 : ℝ) + δ / 2 ≤ (z.2 : ℝ) at hle
  linarith

theorem exists_isMaxOn_distance_frontier
    [T3Space M] [PreconnectedSpace M]
    (H : RadialHomeomorph g p) {A : Set M}
    (hcompact : IsCompact (closure A)) (hne : A.Nonempty)
    (hp : p ∉ interior A) :
    ∃ x ∈ frontier A, IsMaxOn (fun y => (g.edist p y).toReal) (closure A) x := by
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hne.closure
    (g.continuous_toReal_edist p).continuousOn
  refine ⟨x, ⟨hx, ?_⟩, hmax⟩
  intro hxint
  have hxp : x ≠ p := fun heq => hp (heq ▸ hxint)
  apply H.not_isLocalMax_distance hxp
  exact hmax.isLocalMax (Filter.mem_of_superset
    (isOpen_interior.mem_nhds hxint) (interior_subset.trans subset_closure))

theorem exists_distance_le_frontier
    [T3Space M] [PreconnectedSpace M]
    (H : RadialHomeomorph g p) {A : Set M}
    (hcompact : IsCompact (closure A)) (hp : p ∉ interior A)
    {x : M} (hx : x ∈ closure A) :
    ∃ y ∈ frontier A, (g.edist p x).toReal ≤ (g.edist p y).toReal := by
  have hne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, closure_empty] at hx
    exact hx
  obtain ⟨y, hy, hmax⟩ := H.exists_isMaxOn_distance_frontier hcompact hne hp
  exact ⟨y, hy, hmax hx⟩

end PoincareConjecture.RiemannianMetric.RadialHomeomorph
