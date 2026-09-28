import PoincareConjecture.Proofs.M38.ProjectiveDoublePeriod
import PoincareConjecture.Proofs.M38.CylinderDeckRelation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} (C : SmoothProjectiveDoubleModel A.carrier)
  (f g : RoundCylinderSpace → A.carrier)


theorem projectiveDoubleProjection4_three (z : UnitTwoSphere) :
    projectiveDoubleProjection4 C f g (z, 3) = C.collar (-z, 0) := by
  rw [projectiveDoubleProjection4_fundamental C f g (by norm_num), projectiveDoubleCycle_three]

private theorem projection_neg_shift (z : UnitTwoSphere) (t : ℝ) :
    projectiveDoubleProjection4 C f g (-z, -t) =
      projectiveDoubleProjection4 C f g (-z, 4 - t) := by
  have h := projectiveDoubleProjection4_translate C f g (-z) (-t) 1
  simp only [one_smul] at h
  have harg : -t + 4 = 4 - t := by ring
  simpa only [harg] using h.symm


theorem projectiveDoubleProjection4_reflection
    (hfr : ∀ p, f (-p.1, -p.2) = f p) (hgr : ∀ p, g (-p.1, -p.2) = g p)
    (p : RoundCylinderSpace) :
    projectiveDoubleProjection4 C f g (-p.1, -p.2) = projectiveDoubleProjection4 C f g p := by
  have hfund (z : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 4) :
      projectiveDoubleProjection4 C f g (-z, -t) = projectiveDoubleProjection4 C f g (z, t) := by
    rcases lt_trichotomy t 1 with ht₁ | ht₁ | ht₁
    · rw [projectiveDoubleProjection4_first C f g
        ⟨by linarith, by linarith [ht.1]⟩,
        projectiveDoubleProjection4_first C f g ⟨by linarith [ht.1], ht₁⟩]
      exact hfr (z, t)
    · subst t
      rw [projection_neg_shift C f g, show (4 : ℝ) - 1 = 3 by norm_num,
        projectiveDoubleProjection4_three, neg_neg, projectiveDoubleProjection4_one]
    · rw [projection_neg_shift C f g]
      rcases lt_trichotomy t 3 with ht₃ | ht₃ | ht₃
      · rw [projectiveDoubleProjection4_second C f g ⟨by linarith, by linarith⟩,
          projectiveDoubleProjection4_second C f g ⟨ht₁, ht₃⟩]
        convert hgr (z, 2 - t) using 1
        congr 2
        ring
      · subst t
        rw [show (4 : ℝ) - 3 = 1 by norm_num,
          projectiveDoubleProjection4_one, projectiveDoubleProjection4_three]
      · rw [projectiveDoubleProjection4_first C f g
          ⟨by linarith [ht.2], by linarith⟩,
          projectiveDoubleProjection4_fundamental C f g ht,
          projectiveDoubleCycle_last C f g ht₃]
        convert hfr (z, t - 4) using 1
        congr 2
        ring
  let r := toIcoMod (by norm_num : (0 : ℝ) < 4) 0 p.2
  let n := toIcoDiv (by norm_num : (0 : ℝ) < 4) 0 p.2
  have hr : r ∈ Ico (0 : ℝ) 4 := toIcoMod_mem_Ico' _ _
  have he : p.2 = r + n • (4 : ℝ) := (toIcoMod_add_toIcoDiv_zsmul _ _ _).symm
  have hne : -p.2 = -r + (-n) • (4 : ℝ) := by rw [he, neg_smul]; ring
  change projectiveDoubleProjection4 C f g (-p.1, -p.2) =
    projectiveDoubleProjection4 C f g (p.1, p.2)
  rw [hne, he, projectiveDoubleProjection4_translate, projectiveDoubleProjection4_translate]
  exact hfund p.1 r hr


theorem projectiveDoubleProjection4_eq_of_deck
    (hfr : ∀ p, f (-p.1, -p.2) = f p) (hgr : ∀ p, g (-p.1, -p.2) = g p)
    {x y : RoundCylinderSpace} (h : CylinderDeckRelated 4 x y) :
    projectiveDoubleProjection4 C f g x = projectiveDoubleProjection4 C f g y := by
  rcases h with ⟨n, h | h⟩
  · have he : x = (y.1, y.2 + n • (4 : ℝ)) := by
      apply Prod.ext
      · exact h.1
      · simpa only [zsmul_eq_mul] using h.2
    rw [he, projectiveDoubleProjection4_translate]
  · have he : x = (-y.1, -y.2 + n • (4 : ℝ)) := by
      apply Prod.ext
      · exact h.1
      · simpa only [zsmul_eq_mul, sub_eq_add_neg, add_comm] using h.2
    rw [he, projectiveDoubleProjection4_translate]
    exact projectiveDoubleProjection4_reflection C f g hfr hgr y



theorem projectiveDoubleProjection4_cases (x : RoundCylinderSpace) :
    (∃ p ∈ univ ×ˢ Ioo (-1 : ℝ) 1,
      projectiveDoubleProjection4 C f g x = f p ∧ CylinderDeckRelated 4 x p) ∨
    (∃ p ∈ univ ×ˢ Ioo (-1 : ℝ) 1,
      projectiveDoubleProjection4 C f g x = g p ∧
        CylinderDeckRelated 4 x (p.1, 2 - p.2)) ∨
    (∃ z : UnitTwoSphere, projectiveDoubleProjection4 C f g x = C.collar (z, 0) ∧
      CylinderDeckRelated 4 x (z, 1)) := by
  let r := toIcoMod (by norm_num : (0 : ℝ) < 4) 0 x.2
  let n := toIcoDiv (by norm_num : (0 : ℝ) < 4) 0 x.2
  have hr : r ∈ Ico (0 : ℝ) 4 := toIcoMod_mem_Ico' _ _
  have he : x.2 = r + (n : ℝ) * 4 := by
    simpa only [zsmul_eq_mul] using (toIcoMod_add_toIcoDiv_zsmul
      (by norm_num : (0 : ℝ) < 4) 0 x.2).symm
  have hx : CylinderDeckRelated 4 x (x.1, r) := ⟨n, Or.inl ⟨rfl, he⟩⟩
  have hq : projectiveDoubleProjection4 C f g x = projectiveDoubleCycle C f g (x.1, r) := rfl
  rcases lt_trichotomy r 1 with hr₁ | hr₁ | hr₁
  · exact Or.inl ⟨(x.1, r), ⟨mem_univ _, by constructor <;> linarith [hr.1]⟩,
      hq.trans (projectiveDoubleCycle_first C f g hr₁), hx⟩
  · right; right
    refine ⟨x.1, ?_, ?_⟩
    · rw [hq, hr₁, projectiveDoubleCycle_one]
    · simpa only [hr₁] using hx
  · rcases lt_trichotomy r 3 with hr₃ | hr₃ | hr₃
    · right; left
      refine ⟨(x.1, 2 - r), ⟨mem_univ _, by constructor <;> linarith⟩,
        hq.trans (projectiveDoubleCycle_second C f g ⟨hr₁, hr₃⟩), ?_⟩
      simpa only [sub_sub_cancel] using hx
    · right; right
      refine ⟨-x.1, ?_, hx.trans ?_⟩
      · rw [hq, hr₃, projectiveDoubleCycle_three]
      · exact ⟨1, Or.inr ⟨by simp, by dsimp; rw [hr₃]; norm_num⟩⟩
    · left
      refine ⟨(x.1, r - 4), ⟨mem_univ _, by constructor <;> linarith [hr.2]⟩,
        hq.trans (projectiveDoubleCycle_last C f g hr₃), hx.trans ?_⟩
      exact ⟨1, Or.inl ⟨rfl, by dsimp; norm_num⟩⟩



theorem projectiveDoubleProjection4_deck_of_eq
    (hfi : f '' (univ ×ˢ Ioo (-1 : ℝ) 1) = C.first_region)
    (hgi : g '' (univ ×ˢ Ioo (-1 : ℝ) 1) = C.second_region)
    (hff : ∀ x ∈ univ ×ˢ Ioo (-1 : ℝ) 1, ∀ y ∈ univ ×ˢ Ioo (-1 : ℝ) 1,
      f x = f y ↔ x = y ∨ x = (-y.1, -y.2))
    (hgf : ∀ x ∈ univ ×ˢ Ioo (-1 : ℝ) 1, ∀ y ∈ univ ×ˢ Ioo (-1 : ℝ) 1,
      g x = g y ↔ x = y ∨ x = (-y.1, -y.2))
    {x y : RoundCylinderSpace}
    (he : projectiveDoubleProjection4 C f g x = projectiveDoubleProjection4 C f g y) :
    CylinderDeckRelated 4 x y := by
  have hF (p : RoundCylinderSpace) (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
      f p ∈ C.first_region := hfi.subset (mem_image_of_mem _ hp)
  have hG (p : RoundCylinderSpace) (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
      g p ∈ C.second_region := hgi.subset (mem_image_of_mem _ hp)
  have hS (z : UnitTwoSphere) : C.collar (z, 0) ∈ C.sphere :=
    C.collar_sphere.subset ⟨(z, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  rcases projectiveDoubleProjection4_cases C f g x with
    ⟨p, hp, hpx, hxr⟩ | ⟨p, hp, hpx, hxr⟩ | ⟨z, hpx, hxr⟩
  · rcases projectiveDoubleProjection4_cases C f g y with
      ⟨q, hq, hqy, hyr⟩ | ⟨q, hq, hqy, hyr⟩ | ⟨w, hqy, hyr⟩
    · have hpq := (hff p hp q hq).mp (hpx.symm.trans (he.trans hqy))
      apply hxr.trans
      apply CylinderDeckRelated.trans _ hyr.symm
      rcases hpq with hpq | hpq
      · exact hpq ▸ CylinderDeckRelated.refl 4 q
      · exact ⟨0, Or.inr ⟨congrArg Prod.fst hpq, by simpa using congrArg Prod.snd hpq⟩⟩
    · exact False.elim (disjoint_left.mp C.disjoint (hF p hp)
        ((hpx.symm.trans (he.trans hqy)).symm ▸ hG q hq))
    · exact False.elim (disjoint_left.mp C.sphere_disjoint (hS w)
        (Or.inl ((hpx.symm.trans (he.trans hqy)) ▸ hF p hp)))
  · rcases projectiveDoubleProjection4_cases C f g y with
      ⟨q, hq, hqy, hyr⟩ | ⟨q, hq, hqy, hyr⟩ | ⟨w, hqy, hyr⟩
    · exact False.elim (disjoint_left.mp C.disjoint (hF q hq)
        ((hpx.symm.trans (he.trans hqy)) ▸ hG p hp))
    · have hpq := (hgf p hp q hq).mp (hpx.symm.trans (he.trans hqy))
      apply hxr.trans
      apply CylinderDeckRelated.trans _ hyr.symm
      rcases hpq with hpq | hpq
      · subst p
        exact CylinderDeckRelated.refl 4 _
      · refine ⟨1, Or.inr ⟨congrArg Prod.fst hpq, ?_⟩⟩
        have ht := congrArg Prod.snd hpq
        simp only [Int.cast_one, one_mul]
        change p.2 = -q.2 at ht
        linarith
    · exact False.elim (disjoint_left.mp C.sphere_disjoint (hS w)
        (Or.inr ((hpx.symm.trans (he.trans hqy)) ▸ hG p hp)))
  · rcases projectiveDoubleProjection4_cases C f g y with
      ⟨q, hq, hqy, hyr⟩ | ⟨q, hq, hqy, hyr⟩ | ⟨w, hqy, hyr⟩
    · exact False.elim (disjoint_left.mp C.sphere_disjoint (hS z)
        (Or.inl ((hpx.symm.trans (he.trans hqy)).symm ▸ hF q hq)))
    · exact False.elim (disjoint_left.mp C.sphere_disjoint (hS z)
        (Or.inr ((hpx.symm.trans (he.trans hqy)).symm ▸ hG q hq)))
    · have hzw := C.collar_injective (x₁ := (z, 0)) (x₂ := (w, 0))
        (by norm_num) (by norm_num) (hpx.symm.trans (he.trans hqy))
      have hangle : z = w := congrArg Prod.fst hzw
      exact hxr.trans (hangle ▸ hyr.symm)


theorem projectiveDoubleProjection4_fibers
    (hfi : f '' (univ ×ˢ Ioo (-1 : ℝ) 1) = C.first_region)
    (hgi : g '' (univ ×ˢ Ioo (-1 : ℝ) 1) = C.second_region)
    (hfr : ∀ p, f (-p.1, -p.2) = f p) (hgr : ∀ p, g (-p.1, -p.2) = g p)
    (hff : ∀ x ∈ univ ×ˢ Ioo (-1 : ℝ) 1, ∀ y ∈ univ ×ˢ Ioo (-1 : ℝ) 1,
      f x = f y ↔ x = y ∨ x = (-y.1, -y.2))
    (hgf : ∀ x ∈ univ ×ˢ Ioo (-1 : ℝ) 1, ∀ y ∈ univ ×ˢ Ioo (-1 : ℝ) 1,
      g x = g y ↔ x = y ∨ x = (-y.1, -y.2)) (x y : RoundCylinderSpace) :
    projectiveDoubleProjection4 C f g x = projectiveDoubleProjection4 C f g y ↔
      CylinderDeckRelated 4 x y :=
  ⟨projectiveDoubleProjection4_deck_of_eq C f g hfi hgi hff hgf,
    projectiveDoubleProjection4_eq_of_deck C f g hfr hgr⟩

end PoincareConjecture.M38
