import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem signed_collar_mem_connectedComponentIn_iff
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {K : Set E} {R : Set X} (c : E × ℝ → X) {r : ℝ}
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    {x : X} {z : E} (hz : z ∈ K)
    (hbase : c (z, 0) ∈ connectedComponentIn R x)
    {t : ℝ} (ht : t ∈ Icc (-r) r) :
    c (z, t) ∈ connectedComponentIn R x ↔ 0 ≤ t := by
  constructor
  · intro h
    exact (hside (z, t) ⟨hz, ht⟩).mp (connectedComponentIn_subset R x h)
  · intro ht0
    have hmap : MapsTo (fun s : ℝ => (z, s)) (Icc 0 t) (K ×ˢ Icc (-r) r) := by
      intro s hs
      exact ⟨hz, by linarith [hs.1, ht.2], hs.2.trans ht.2⟩
    have hcont : ContinuousOn (fun s : ℝ => c (z, s)) (Icc 0 t) :=
      hc.comp (continuous_const.prodMk continuous_id).continuousOn hmap
    have hconn : IsPreconnected ((fun s : ℝ => c (z, s)) '' Icc 0 t) :=
      isPreconnected_Icc.image _ hcont
    have hinside : (fun s : ℝ => c (z, s)) '' Icc 0 t ⊆ R := by
      rintro _ ⟨s, hs, rfl⟩
      exact (hside (z, s) (hmap hs)).mpr hs.1
    have hsub := hconn.subset_connectedComponentIn
      (mem_image_of_mem (fun s : ℝ => c (z, s)) (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl, ht0⟩))
      hinside
    rw [← connectedComponentIn_eq hbase] at hsub
    exact hsub (mem_image_of_mem (fun s : ℝ => c (z, s)) ⟨ht0, le_rfl⟩)

theorem signed_collar_side_on_connectedComponentIn
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {K : Set E} {R : Set X} (c : E × ℝ → X) {r : ℝ}
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    {x : X} (hbase : ∀ z ∈ K, c (z, 0) ∈ connectedComponentIn R x) :
    ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ connectedComponentIn R x ↔ 0 ≤ z.2 := by
  rintro ⟨z, t⟩ ⟨hz, ht⟩
  exact signed_collar_mem_connectedComponentIn_iff c hc hside hz (hbase z hz) ht

end PoincareConjecture.M76
