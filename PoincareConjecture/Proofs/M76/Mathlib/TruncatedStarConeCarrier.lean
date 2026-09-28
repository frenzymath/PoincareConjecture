import PoincareConjecture.Proofs.M76.Mathlib.TruncatedStarRadialBoundary
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeCarriers

set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

theorem smul_mem_closedStar_zero (K : SimplicialComplex ℝ E)
    {x : E} (hx : x ∈ (K.closedStar 0).space)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    r • x ∈ (K.closedStar 0).space := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  have his : insert (0 : E) s ∈ (K.closedStar 0).faces :=
    ⟨hs.2, by simpa only [Finset.insert_idem] using hs.2⟩
  apply convexHull_subset_space his
  rw [Finset.coe_insert]
  exact smul_mem_convexHull_insert_zero hxs hr

theorem exists_truncatedStarBoundary_rayEndpoint
    (K : SimplicialComplex ℝ E) (L : E →ₗ[ℝ] ℝ)
    {α β : ℝ} (hα : α < 0) (hβ : 0 < β)
    {y : E} (hy : y ∈ (K.link 0).space) :
    ∃ r ∈ Ioc (0 : ℝ) 1, r • y ∈ K.truncatedStarBoundary L α β ∧
      ∀ t ∈ Icc (0 : ℝ) 1, L (t • y) ∈ Icc α β → t ≤ r := by
  have hys : y ∈ (K.closedStar 0).space := by
    obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy
    exact convexHull_subset_space (K.link_le_closedStar 0 hs) hys
  by_cases hlo : L y < α
  · have hyneg : L y < 0 := hlo.trans hα
    have hr : α / L y ∈ Ioc (0 : ℝ) 1 :=
      ⟨div_pos_of_neg_of_neg hα hyneg, (div_le_one_of_neg hyneg).mpr hlo.le⟩
    have hlevel : L ((α / L y) • y) = α := by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hyneg.ne]
    refine ⟨α / L y, hr, Or.inl (Or.inl
      ⟨K.smul_mem_closedStar_zero hys ⟨hr.1.le, hr.2⟩, hlevel⟩), ?_⟩
    intro t _ ht
    apply (le_div_iff_of_neg hyneg).mpr
    simpa only [map_smul, smul_eq_mul] using ht.1
  · by_cases hhi : β < L y
    · have hypos : 0 < L y := hβ.trans hhi
      have hr : β / L y ∈ Ioc (0 : ℝ) 1 :=
        ⟨div_pos hβ hypos, (div_le_one hypos).mpr hhi.le⟩
      have hlevel : L ((β / L y) • y) = β := by
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hypos.ne']
      refine ⟨β / L y, hr, Or.inl (Or.inr
        ⟨K.smul_mem_closedStar_zero hys ⟨hr.1.le, hr.2⟩, hlevel⟩), ?_⟩
      intro t _ ht
      apply (le_div_iff₀ hypos).mpr
      simpa only [map_smul, smul_eq_mul] using ht.2
    · refine ⟨1, ⟨zero_lt_one, le_rfl⟩, ?_, fun _ ht _ => ht.2⟩
      rw [one_smul]
      change (y ∈ (K.closedStar 0).space ∩ {x | L x = α} ∪
        (K.closedStar 0).space ∩ {x | L x = β}) ∨
          y ∈ (K.link 0).space ∩ {x | L x ∈ Icc α β}
      exact Or.inr ⟨hy, not_lt.mp hlo, not_lt.mp hhi⟩

theorem truncatedStarBoundary_nonempty (K : SimplicialComplex ℝ E)
    (L : E →ₗ[ℝ] ℝ) {α β : ℝ} (hα : α < 0) (hβ : 0 < β)
    (hne : (K.link 0).space.Nonempty) :
    (K.truncatedStarBoundary L α β).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨r, _, hr, _⟩ := K.exists_truncatedStarBoundary_rayEndpoint L hα hβ hy
  exact ⟨r • y, hr⟩

theorem convexJoin_truncatedStarBoundary_eq_band
    (K : SimplicialComplex ℝ E) (L : E →ₗ[ℝ] ℝ)
    {α β : ℝ} (hα : α < 0) (hβ : 0 < β)
    (hne : (K.link 0).space.Nonempty) :
    convexJoin ℝ {0} (K.truncatedStarBoundary L α β) =
      (K.closedStar 0).space ∩ {x | L x ∈ Icc α β} := by
  ext x
  rw [mem_convexJoin_zero_iff]
  constructor
  · rintro ⟨y, hy, r, hr, rfl⟩
    have hyband := K.truncatedStarBoundary_subset_band L (hα.trans hβ).le hy
    refine ⟨K.smul_mem_closedStar_zero hyband.1 hr, ?_⟩
    have hh := (convex_Icc α β).smul_mem_of_zero_mem
      (show (0 : ℝ) ∈ Icc α β from ⟨hα.le, hβ.le⟩) hyband.2 hr
    change L (r • y) ∈ Icc α β
    simpa only [map_smul, smul_eq_mul] using hh
  · intro hx
    by_cases hx0 : x = 0
    · obtain ⟨y, hy⟩ := K.truncatedStarBoundary_nonempty L hα hβ hne
      exact ⟨y, hy, 0, ⟨le_rfl, zero_le_one⟩, by simp [hx0]⟩
    · obtain ⟨y, hy, a, ha, hxy⟩ := exists_linkPoint_smul hx.1 hx0
      obtain ⟨r, hr, hrb, hrmax⟩ :=
        K.exists_truncatedStarBoundary_rayEndpoint L hα hβ hy
      have har : a ≤ r := hrmax a ⟨ha.1.le, ha.2⟩ (hxy ▸ hx.2)
      refine ⟨r • y, hrb, a / r,
        ⟨div_nonneg ha.1.le hr.1.le, (div_le_one hr.1).mpr har⟩, ?_⟩
      rw [smul_smul, div_mul_cancel₀ _ hr.1.ne']
      exact hxy

end Geometry.SimplicialComplex
