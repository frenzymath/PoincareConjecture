import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeCarriers
import PoincareConjecture.Proofs.M76.Mathlib.ConicalAffineExtension

set_option autoImplicit false

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_base_union_convexJoin_iff_of_radial
    {s b : Set E} (hb : b ⊆ s) (hbne : b.Nonempty)
    (hs0 : (0 : E) ∉ s) (hrad : InjOn (normalize : E → E) s)
    {y : E} (hy : y ∈ s) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    r • y ∈ s ∪ convexJoin ℝ {0} b ↔ r = 0 ∨ r = 1 ∨ y ∈ b := by
  have hy0 : y ≠ 0 := fun he => hs0 (he ▸ hy)
  constructor
  · intro h
    by_cases hr0 : r = 0
    · exact Or.inl hr0
    have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    rcases h with hs | hs
    · have heq : r • y = y := hrad hs hy (normalize_smul_of_pos hrpos y)
      exact Or.inr (Or.inl (smul_left_injective ℝ hy0
        (by simpa only [one_smul] using heq)))
    · obtain ⟨z, hz, t, ht, heq⟩ := (mem_convexJoin_zero_iff b _).mp hs
      have ht0 : t ≠ 0 := by
        intro he
        rw [he, zero_smul] at heq
        exact hy0 ((smul_eq_zero.mp heq).resolve_left hr0)
      have htpos : 0 < t := lt_of_le_of_ne ht.1 ht0.symm
      have hyz : y = z := hrad hy (hb hz) (by
        have h := congrArg (NormedSpace.normalize : E → E) heq
        rwa [normalize_smul_of_pos hrpos, normalize_smul_of_pos htpos] at h)
      exact Or.inr (Or.inr (hyz.symm ▸ hz))
  · rintro (hr0 | hr1 | hyb)
    · right
      obtain ⟨z, hz⟩ := hbne
      exact (mem_convexJoin_zero_iff b _).mpr
        ⟨z, hz, 0, ⟨le_rfl, zero_le_one⟩, by simp [hr0]⟩
    · left
      simpa only [hr1, one_smul] using hy
    · right
      exact (mem_convexJoin_zero_iff b _).mpr ⟨y, hyb, r, hr, rfl⟩

namespace Geometry.SimplicialComplex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [DecidableEq E] {K : SimplicialComplex ℝ E} {f g : E → F}

theorem AffineOnFaces.cone_extension_smul
    {hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E)}
    {hrad : InjOn (normalize : E → E) K.space}
    (hg : (K.coneAtZero hlin hrad).AffineOnFaces g)
    (hg0 : g 0 = 0) (hbase : EqOn g f K.space)
    {y : E} (hy : y ∈ K.space) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    g (r • y) = r • f y := by
  obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy
  obtain ⟨a, ha⟩ := hg _ (insert_zero_mem_coneAtZero_faces hlin hrad hs)
  have hz : (0 : E) ∈ convexHull ℝ (insert 0 s : Finset E) :=
    subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
  have hy' : y ∈ convexHull ℝ (insert 0 s : Finset E) :=
    convexHull_mono (by simp only [Finset.coe_insert]; exact subset_insert _ _) hys
  have hray : r • y ∈ convexHull ℝ (insert 0 s : Finset E) := by
    rw [Finset.coe_insert]
    exact smul_mem_convexHull_insert_zero hys hr
  have ha0 : a 0 = 0 := (ha hz).symm.trans hg0
  have hay : a y = f y := (ha hy').symm.trans (hbase hy)
  have hline : r • y = AffineMap.lineMap 0 y r := by
    simp [AffineMap.lineMap_apply]
  rw [ha hray, hline]
  change a.toAffineMap (AffineMap.lineMap 0 y r) = _
  rw [AffineMap.apply_lineMap]
  change AffineMap.lineMap (a 0) (a y) r = _
  rw [ha0, hay]
  simp [AffineMap.lineMap_apply]

end Geometry.SimplicialComplex
