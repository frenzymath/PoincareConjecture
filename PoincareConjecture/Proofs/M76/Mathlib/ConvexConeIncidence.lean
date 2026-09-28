import PoincareConjecture.Proofs.M76.Mathlib.RadialConeBoundary
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryRadial

set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Convex.convexJoin_zero_inter_frontier {Q d : Set E} (hQ : Convex ℝ Q)
    (hzero : (0 : E) ∈ interior Q) (hd : d ⊆ frontier Q) :
    convexJoin ℝ {0} d ∩ frontier Q = d := by
  apply Subset.antisymm
  · rintro x ⟨hxd, hxf⟩
    obtain ⟨y, hy, r, hr, hxy⟩ := (mem_convexJoin_zero_iff d x).mp hxd
    have hrpos : 0 < r := lt_of_le_of_ne hr.1 (by
      intro he
      have hx0 : x = 0 := by simpa only [← he, zero_smul] using hxy
      exact hxf.2 (hx0 ▸ hzero))
    have hnorm : NormedSpace.normalize x = NormedSpace.normalize y := by
      rw [hxy, NormedSpace.normalize_smul_of_pos hrpos]
    have hxeq : x = y := hQ.injOn_normalize_frontier hzero hxf (hd hy) hnorm
    exact hxeq.symm ▸ hy
  · intro x hx
    exact ⟨subset_convexJoin_right (singleton_nonempty (0 : E)) hx, hd hx⟩

theorem Convex.convexJoin_zero_inter_of_nonempty {Q d e : Set E}
    (hQ : Convex ℝ Q) (hzero : (0 : E) ∈ interior Q)
    (hd : d ⊆ frontier Q) (he : e ⊆ frontier Q) (hne : (d ∩ e).Nonempty) :
    convexJoin ℝ {0} d ∩ convexJoin ℝ {0} e = convexJoin ℝ {0} (d ∩ e) := by
  apply Subset.antisymm
  · rintro x ⟨hxd, hxe⟩
    by_cases hx0 : x = 0
    · obtain ⟨y, hy⟩ := hne
      exact (mem_convexJoin_zero_iff _ _).mpr
        ⟨y, hy, 0, ⟨le_rfl, zero_le_one⟩, by simp [hx0]⟩
    obtain ⟨y, hy, r, hr, hxy⟩ := (mem_convexJoin_zero_iff d x).mp hxd
    obtain ⟨z, hz, t, ht, hxz⟩ := (mem_convexJoin_zero_iff e x).mp hxe
    have hrpos : 0 < r := lt_of_le_of_ne hr.1 (by
      intro heq
      exact hx0 (by simpa only [← heq, zero_smul] using hxy))
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
      intro heq
      exact hx0 (by simpa only [← heq, zero_smul] using hxz))
    have hyz : y = z := hQ.injOn_normalize_frontier hzero (hd hy) (he hz) (by
      have hh := congrArg (NormedSpace.normalize : E → E) (hxy.symm.trans hxz)
      rwa [NormedSpace.normalize_smul_of_pos hrpos,
        NormedSpace.normalize_smul_of_pos htpos] at hh)
    exact (mem_convexJoin_zero_iff _ _).mpr ⟨y, ⟨hy, hyz.symm ▸ hz⟩, r, hr, hxy⟩
  · exact fun _ hx => ⟨convexJoin_mono_right inter_subset_left hx,
      convexJoin_mono_right inter_subset_right hx⟩

theorem IsCompact.convexJoin_zero_frontier_eq {Q : Set E} (hQ : IsCompact Q)
    (hcv : Convex ℝ Q) (hzero : (0 : E) ∈ interior Q)
    (hne : (frontier Q).Nonempty) : convexJoin ℝ {0} (frontier Q) = Q := by
  apply Subset.antisymm
  · exact convexJoin_subset (singleton_subset_iff.mpr (interior_subset hzero))
      hQ.isClosed.frontier_subset hcv
  · intro x hx
    by_cases hx0 : x = 0
    · obtain ⟨y, hy⟩ := hne
      exact (mem_convexJoin_zero_iff _ _).mpr
        ⟨y, hy, 0, ⟨le_rfl, zero_le_one⟩, by simp [hx0]⟩
    · obtain ⟨y, hy, r, hr, hxy⟩ := hQ.exists_frontier_pos_smul hcv hzero hx hx0
      exact (mem_convexJoin_zero_iff _ _).mpr ⟨y, hy, r, ⟨hr.1.le, hr.2⟩, hxy⟩
