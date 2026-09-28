import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Band.GraphSlab










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem extend_compact_band_through_neck (f k : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hk : Continuous k)
    (hfdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hkdom : ∀ q, k q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hfk : ∀ q, f q < k q) (K S : Set M) (hK : IsCompact K)
    (hfront : frontier K ⊆ S ∪ range (fun q => N.coordinate_map (q, f q)))
    (r : ℝ) (hr : 0 < r)
    (hcollar : ∀ (q : UnitTwoSphere) (t : ℝ),
      t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → f q - r < t → t ≤ f q →
        N.coordinate_map (q, t) ∈ K) :
    IsCompact (K ∪ N.closedGraphSlab f k) ∧
    frontier (K ∪ N.closedGraphSlab f k) ⊆
      S ∪ range (fun q => N.coordinate_map (q, k q)) ∧
    ∃ r' : ℝ, 0 < r' ∧ ∀ (q : UnitTwoSphere) (t : ℝ),
      t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → k q - r' < t → t ≤ k q →
        N.coordinate_map (q, t) ∈ K ∪ N.closedGraphSlab f k := by
  let V := N.aboveGraph (fun q => f q - r) ∩ N.belowGraph k
  have hV : IsOpen V :=
    (N.isOpen_aboveGraph _ (hf.sub continuous_const)).inter (N.isOpen_belowGraph k hk)
  have hsub : V ⊆ K ∪ N.closedGraphSlab f k := by
    intro x hx
    have hxN := hx.1.1
    by_cases hlow : (N.coordinate_inverse x).2 ≤ f (N.coordinate_inverse x).1
    · apply Or.inl
      have h := hcollar (N.coordinate_inverse x).1 (N.coordinate_inverse x).2
        (N.coordinate_inverse_mem x hxN).2 hx.1.2 hlow
      simpa only [Prod.mk.eta, N.coordinate_map_coordinate_inverse hxN] using h
    · exact Or.inr ⟨hxN, (lt_of_not_ge hlow).le, hx.2.2.le⟩
  have hcommon : range (fun q => N.coordinate_map (q, f q)) ⊆
      interior (K ∪ N.closedGraphSlab f k) := by
    rintro x ⟨q, rfl⟩
    apply interior_mono hsub
    rw [hV.interior_eq]
    have hz : (q, f q) ∈ N.cylinderDomain := ⟨mem_univ _, hfdom q⟩
    have hxN := N.coordinate_map_mem hz
    change (_ ∧ _) ∧ (_ ∧ _)
    simp only [N.coordinate_inverse_coordinate_map hz]
    exact ⟨⟨hxN, sub_lt_self _ hr⟩, ⟨hxN, hfk q⟩⟩
  refine ⟨hK.union (N.isCompact_closedGraphSlab f k hf hk hfdom hkdom hfk), ?_, ?_⟩
  · intro x hx
    rcases frontier_union_subset K (N.closedGraphSlab f k) hx with
      ⟨hfirst, _⟩ | ⟨_, hsecond⟩
    · rcases hfront hfirst with hs | hs
      · exact Or.inl hs
      · exact False.elim (hx.2 (hcommon hs))
    · rcases N.frontier_closedGraphSlab_subset f k hf hk hfdom hkdom hfk hsecond with
        hs | hs
      · exact False.elim (hx.2 (hcommon hs))
      · exact Or.inr hs
  · obtain ⟨d, hd, hgap⟩ :=
      (isCompact_univ : IsCompact (univ : Set UnitTwoSphere)).exists_forall_le'
        (hk.sub hf).continuousOn (a := 0) (fun q _ => sub_pos.mpr (hfk q))
    refine ⟨d, hd, ?_⟩
    intro q t ht hlow hhigh
    apply Or.inr
    apply (N.mem_closedGraphSlab_coordinate_map_iff f k ht).mpr
    have hgapq : d ≤ k q - f q := hgap q (mem_univ q)
    exact ⟨by linarith, hhigh⟩

omit [T2Space M] in

theorem extend_compact_band_upper_exclusion (f k : UnitTwoSphere → ℝ)
    (hfk : ∀ q, f q < k q) (K : Set M)
    (hupper : ∀ (q : UnitTwoSphere) (t : ℝ),
      t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → f q < t →
        N.coordinate_map (q, t) ∉ K) :
    ∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      k q < t → N.coordinate_map (q, t) ∉ K ∪ N.closedGraphSlab f k := by
  intro q t ht hgt hx
  rcases hx with hx | hx
  · exact hupper q t ht ((hfk q).trans hgt) hx
  · exact not_le_of_gt hgt ((N.mem_closedGraphSlab_coordinate_map_iff f k ht).mp hx).2

end PoincareConjecture.EpsilonNeck
