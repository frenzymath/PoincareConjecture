import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.GeneralPosition.ConvexSegmentNeighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Basic











set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph

theorem exists_finite_edge_control
    {X E κ ν : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Finite κ]
    (B : κ → OpenPartialHomeomorph X E) (src dst : κ → ν) (f : ν → X)
    (U : κ → Set X) (hU : ∀ k, IsOpen (U k))
    (hsrc : ∀ k, f (src k) ∈ (B k).source)
    (hdst : ∀ k, f (dst k) ∈ (B k).source)
    (hedge : ∀ k, segment ℝ (B k (f (src k))) (B k (f (dst k))) ⊆
      (B k).target ∩ (B k).symm ⁻¹' U k) :
    ∃ (O : ν → Set X) (V : κ → Set E),
      (∀ v, IsOpen (O v) ∧ f v ∈ O v) ∧
      (∀ k, IsOpen (V k) ∧ Convex ℝ (V k) ∧
        V k ⊆ (B k).target ∧ MapsTo (B k).symm (V k) (U k)) ∧
      ∀ g : ν → X, (∀ v, g v ∈ O v) → ∀ k,
        g (src k) ∈ (B k).source ∧ g (dst k) ∈ (B k).source ∧
        segment ℝ (B k (g (src k))) (B k (g (dst k))) ⊆ V k := by
  classical
  choose δ V hδ hVo hVc hseg hVsub hleft hright using fun k =>
    exists_convex_segment_neighborhood ((B k).isOpen_inter_preimage_symm (hU k))
      (hedge k)
  let O : ν → Set X := fun v =>
    (⋂ k, if src k = v then
      (B k).source ∩ (B k) ⁻¹' ball (B k (f v)) (δ k) else univ) ∩
    (⋂ k, if dst k = v then
      (B k).source ∩ (B k) ⁻¹' ball (B k (f v)) (δ k) else univ)
  have hO (v : ν) : IsOpen (O v) ∧ f v ∈ O v := by
    constructor
    · apply IsOpen.inter <;> apply isOpen_iInter_of_finite <;> intro k
      · split_ifs
        · exact (B k).isOpen_inter_preimage isOpen_ball
        · exact isOpen_univ
      · split_ifs
        · exact (B k).isOpen_inter_preimage isOpen_ball
        · exact isOpen_univ
    · constructor <;> apply mem_iInter.mpr <;> intro k
      · split_ifs with h
        · exact ⟨h ▸ hsrc k, mem_ball_self (hδ k)⟩
        · exact mem_univ _
      · split_ifs with h
        · exact ⟨h ▸ hdst k, mem_ball_self (hδ k)⟩
        · exact mem_univ _
  refine ⟨O, V, hO, fun k => ⟨hVo k, hVc k,
    fun x hx => (hVsub k hx).1, fun x hx => (hVsub k hx).2⟩, ?_⟩
  intro g hg k
  have hs : g (src k) ∈ (B k).source ∩
      (B k) ⁻¹' ball (B k (f (src k))) (δ k) := by
    simpa only [ite_true] using mem_iInter.mp (hg (src k)).1 k
  have ht : g (dst k) ∈ (B k).source ∩
      (B k) ⁻¹' ball (B k (f (dst k))) (δ k) := by
    simpa only [ite_true] using mem_iInter.mp (hg (dst k)).2 k
  exact ⟨hs.1, ht.1, (hVc k).segment_subset (hleft k hs.2) (hright k ht.2)⟩

end OpenPartialHomeomorph
