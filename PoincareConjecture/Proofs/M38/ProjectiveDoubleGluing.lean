import PoincareConjecture.Proofs.M38.ProjectiveDoubleSideCovers










set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} (C : SmoothProjectiveDoubleModel A.carrier)
  (f g : RoundCylinderSpace → A.carrier)


noncomputable def projectiveDoubleCycle (p : RoundCylinderSpace) : A.carrier :=
  if p.2 < 1 then f p else if p.2 = 1 then C.collar (p.1, 0)
  else if p.2 < 3 then g (p.1, 2 - p.2)
  else if p.2 = 3 then C.collar (-p.1, 0) else f (p.1, p.2 - 4)


theorem projectiveDoubleCycle_first {p : RoundCylinderSpace} (hp : p.2 < 1) :
    projectiveDoubleCycle C f g p = f p := by simp only [projectiveDoubleCycle, if_pos hp]


theorem projectiveDoubleCycle_one (z : UnitTwoSphere) :
    projectiveDoubleCycle C f g (z, 1) = C.collar (z, 0) := by
  simp only [projectiveDoubleCycle, lt_self_iff_false, if_false, if_true]


theorem projectiveDoubleCycle_second {p : RoundCylinderSpace} (hp : p.2 ∈ Ioo (1 : ℝ) 3) :
    projectiveDoubleCycle C f g p = g (p.1, 2 - p.2) := by
  simp only [projectiveDoubleCycle, if_neg (not_lt.mpr hp.1.le),
    if_neg (ne_of_gt hp.1), if_pos hp.2]


theorem projectiveDoubleCycle_three (z : UnitTwoSphere) :
    projectiveDoubleCycle C f g (z, 3) = C.collar (-z, 0) := by
  norm_num [projectiveDoubleCycle]


theorem projectiveDoubleCycle_last {p : RoundCylinderSpace} (hp : 3 < p.2) :
    projectiveDoubleCycle C f g p = f (p.1, p.2 - 4) := by
  simp only [projectiveDoubleCycle, if_neg (show ¬p.2 < 1 by linarith),
    if_neg (show p.2 ≠ 1 by linarith), if_neg (not_lt.mpr hp.le), if_neg (ne_of_gt hp)]

variable {r : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 32)
  (hf : ∀ (z : UnitTwoSphere) (t : ℝ), t ∈ Ioo (1 - r) 1 →
    f (z, t) = C.collar (z, 2 * (t - 1)))
  (hg : ∀ (z : UnitTwoSphere) (t : ℝ), t ∈ Ioo (1 - r) 1 →
    g (z, t) = C.collar (z, 2 * (1 - t)))

include hrsmall hf hg in

theorem projectiveDoubleCycle_first_collar (z : UnitTwoSphere) {t : ℝ}
    (ht : t ∈ Ioo (1 - r) (1 + r)) :
    projectiveDoubleCycle C f g (z, t) = C.collar (z, 2 * (t - 1)) := by
  rcases lt_trichotomy t 1 with ht₁ | ht₁ | ht₁
  · rw [projectiveDoubleCycle_first C f g ht₁, hf z t ⟨ht.1, ht₁⟩]
  · subst t
    rw [projectiveDoubleCycle_one]
    norm_num
  · rw [projectiveDoubleCycle_second C f g ⟨ht₁, by linarith [ht.2]⟩,
      hg z (2 - t) ⟨by linarith [ht.2], by linarith⟩]
    congr 2
    ring

include hrsmall hf hg in

theorem projectiveDoubleCycle_second_collar
    (hfr : ∀ p, f (-p.1, -p.2) = f p) (hgr : ∀ p, g (-p.1, -p.2) = g p)
    (z : UnitTwoSphere) {t : ℝ} (ht : t ∈ Ioo (3 - r) (3 + r)) :
    projectiveDoubleCycle C f g (z, t) = C.collar (-z, 2 * (3 - t)) := by
  rcases lt_trichotomy t 3 with ht₃ | ht₃ | ht₃
  · rw [projectiveDoubleCycle_second C f g ⟨by linarith [ht.1], ht₃⟩,
      ← hgr (z, 2 - t)]
    change g (-z, -(2 - t)) = _
    rw [hg (-z) (-(2 - t)) ⟨by linarith [ht.1], by linarith⟩]
    congr 2
    ring
  · subst t
    rw [projectiveDoubleCycle_three]
    norm_num
  · rw [projectiveDoubleCycle_last C f g ht₃, ← hfr (z, t - 4)]
    change f (-z, -(t - 4)) = _
    rw [hf (-z) (-(t - 4)) ⟨by linarith [ht.2], by linarith⟩]
    congr 2
    ring


theorem projectiveDoubleCycle_closing (z : UnitTwoSphere) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    projectiveDoubleCycle C f g (z, 4 + t) = projectiveDoubleCycle C f g (z, t) := by
  rw [projectiveDoubleCycle_last C f g (by linarith [ht.1]),
    projectiveDoubleCycle_first C f g ht.2]
  congr 1
  apply Prod.ext
  · rfl
  · change 4 + t - 4 = t
    ring


noncomputable def cylinderAffineChange (a b : ℝ) (ha : a ≠ 0) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun p := (p.1, a * p.2 + b)
  invFun p := (p.1, (p.2 - b) / a)
  left_inv p := by
    apply Prod.ext
    · rfl
    · change (a * p.2 + b - b) / a = p.2
      field_simp
      ring
  right_inv p := by
    apply Prod.ext
    · rfl
    · change a * ((p.2 - b) / a) + b = p.2
      field_simp
      ring
  contMDiff_toFun := contMDiff_fst.prodMk
    (((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff.comp contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    (((contDiff_id.sub contDiff_const).div_const a).contMDiff.comp contMDiff_snd)

private instance sphereDimension : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp⟩


noncomputable def cylinderAngularAntipode :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv _p := by simp
  right_inv _p := by simp
  contMDiff_toFun := (contMDiff_neg_sphere.comp contMDiff_fst).prodMk contMDiff_snd
  contMDiff_invFun := (contMDiff_neg_sphere.comp contMDiff_fst).prodMk contMDiff_snd

include hr hrsmall hf hg in


theorem projectiveDoubleCycle_localDiffeomorph
    (hfl : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-1 : ℝ) 1))
    (hgl : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g
      (univ ×ˢ Ioo (-1 : ℝ) 1))
    (hfr : ∀ p, f (-p.1, -p.2) = f p) (hgr : ∀ p, g (-p.1, -p.2) = g p)
    (p : RoundCylinderSpace) (hp : p.2 ∈ Icc (0 : ℝ) 4) :
    IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (projectiveDoubleCycle C f g) p := by
  rcases lt_trichotomy p.2 1 with ht | ht | ht
  · apply (hfl ⟨p, ⟨mem_univ _, by constructor <;> linarith [hp.1]⟩⟩).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds ht] with x hx
    exact projectiveDoubleCycle_first C f g hx
  · let D := cylinderAffineChange 2 (-2) (by norm_num)
    have hD : D p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := by
      change p.1 ∈ univ ∧ 2 * p.2 + -2 ∈ Ioo (-1 : ℝ) 1
      rw [ht]
      norm_num
    apply ((D.isLocalDiffeomorph p).comp (𝓡 3) A.carrier
      (C.collar_local_diffeomorph ⟨D p, hD⟩)).congr_of_eventuallyEq
    filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds
      (show p.2 ∈ Ioo (1 - r) (1 + r) by rw [ht]; constructor <;> linarith)] with x hx
    change projectiveDoubleCycle C f g x = C.collar (x.1, 2 * x.2 + -2)
    rw [projectiveDoubleCycle_first_collar C f g hrsmall hf hg x.1 hx]
    congr 2
    ring
  · rcases lt_trichotomy p.2 3 with ht₃ | ht₃ | ht₃
    · let D := cylinderAffineChange (-1) 2 (by norm_num)
      have hD : D p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := by
        change p.1 ∈ univ ∧ -1 * p.2 + 2 ∈ Ioo (-1 : ℝ) 1
        exact ⟨mem_univ _, by constructor <;> linarith⟩
      apply ((D.isLocalDiffeomorph p).comp (𝓡 3) A.carrier
        (hgl ⟨D p, hD⟩)).congr_of_eventuallyEq
      filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds
        (show p.2 ∈ Ioo (1 : ℝ) 3 from ⟨ht, ht₃⟩)] with x hx
      change projectiveDoubleCycle C f g x = g (x.1, -1 * x.2 + 2)
      rw [projectiveDoubleCycle_second C f g hx]
      congr 2
      ring
    · let D := cylinderAngularAntipode.trans (cylinderAffineChange (-2) 6 (by norm_num))
      have hD : D p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := by
        change -p.1 ∈ univ ∧ -2 * p.2 + 6 ∈ Ioo (-1 : ℝ) 1
        rw [ht₃]
        norm_num
      apply ((D.isLocalDiffeomorph p).comp (𝓡 3) A.carrier
        (C.collar_local_diffeomorph ⟨D p, hD⟩)).congr_of_eventuallyEq
      filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds
        (show p.2 ∈ Ioo (3 - r) (3 + r) by rw [ht₃]; constructor <;> linarith)] with x hx
      change projectiveDoubleCycle C f g x = C.collar (-x.1, -2 * x.2 + 6)
      rw [projectiveDoubleCycle_second_collar C f g hrsmall hf hg hfr hgr x.1 hx]
      congr 2
      ring
    · let D := cylinderAffineChange 1 (-4) (by norm_num)
      have hD : D p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := by
        change p.1 ∈ univ ∧ 1 * p.2 + -4 ∈ Ioo (-1 : ℝ) 1
        exact ⟨mem_univ _, by constructor <;> linarith [hp.2]⟩
      apply ((D.isLocalDiffeomorph p).comp (𝓡 3) A.carrier
        (hfl ⟨D p, hD⟩)).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds ht₃] with x hx
      change projectiveDoubleCycle C f g x = f (x.1, 1 * x.2 + -4)
      rw [projectiveDoubleCycle_last C f g hx]
      congr 2
      ring

end PoincareConjecture.M38
