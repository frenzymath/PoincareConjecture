import PoincareConjecture.Proofs.M25.Topology3D.Plane.ChordEstimates
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ChordContainment

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

theorem exists_uniform_short_chord_direction_mem_open
    {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set X} (hK : IsCompact K) {c d : X → ℝ → E} {l u : ℝ}
    (hc : ContinuousOn (fun p : X × ℝ => c p.1 p.2) (K ×ˢ Icc l u))
    (hd : ∀ z ∈ K, ∀ s ∈ Icc l u, HasDerivWithinAt (c z) (d z s) (Icc l u) s)
    (hcont : ContinuousOn (fun p : X × ℝ => d p.1 p.2) (K ×ˢ Icc l u))
    {W : Set ((X × ℝ) × (E × E))} (hW : IsOpen W)
    (hbase : ∀ z ∈ K, ∀ s ∈ Icc l u, ((z, s), (c z s, d z s)) ∈ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ a ∈ Icc l u, ∀ b ∈ Icc l u,
      a < b → b - a < δ → ∀ t ∈ Icc (0 : ℝ) 1,
        ((z, a), (AffineMap.lineMap (c z a) (c z b) t, slope (c z) a b)) ∈ W := by
  let F : X × ℝ → (X × ℝ) × (E × E) := fun p => (p, (c p.1 p.2, d p.1 p.2))
  have hF : ContinuousOn F (K ×ˢ Icc l u) := continuousOn_id.prodMk (hc.prodMk hcont)
  have hcompact : IsCompact (F '' (K ×ˢ Icc l u)) :=
    (hK.prod isCompact_Icc).image_of_continuousOn hF
  have hsub : F '' (K ×ˢ Icc l u) ⊆ W := by
    rintro y ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩
    exact hbase z hz s hs
  obtain ⟨ρ, hρ, hthick⟩ := hcompact.exists_thickening_subset_open hW hsub
  obtain ⟨δc, hδc, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hc) ρ hρ
  obtain ⟨δd, hδd, hsec⟩ := exists_uniform_chord_estimates hK hd hcont (half_pos hρ)
  refine ⟨min δc δd, lt_min hδc hδd, ?_⟩
  intro z hz a ha b hb hab hmesh t ht
  have hend : dist (c z a) (c z b) < ρ := hclose (z, a) ⟨hz, ha⟩ (z, b) ⟨hz, hb⟩ (by
    rw [dist_prod_same_left, Real.dist_eq, abs_sub_comm,
      abs_of_pos (sub_pos.mpr hab)]
    exact hmesh.trans_le (min_le_left _ _))
  have hdir : dist (slope (c z) a b) (d z a) < ρ := by
    rw [dist_eq_norm]
    exact (hsec z hz a ha b hb hab (hmesh.trans_le (min_le_right _ _))).1.trans_lt
      (half_lt_self hρ)
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  refine ⟨F (z, a), ⟨(z, a), ⟨hz, ha⟩, rfl⟩, ?_⟩
  change dist ((z, a), (AffineMap.lineMap (c z a) (c z b) t, slope (c z) a b))
    ((z, a), (c z a, d z a)) < ρ
  rw [dist_prod_same_left, Prod.dist_eq]
  refine max_lt ?_ hdir
  rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left dist_nonneg ht.2).trans_lt hend

end PoincareConjecture.M25.Topology3D
