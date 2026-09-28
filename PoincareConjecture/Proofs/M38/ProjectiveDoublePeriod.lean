import PoincareConjecture.Proofs.M38.ProjectiveDoubleGluing
import Mathlib.Algebra.Order.ToIntervalMod











set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} (C : SmoothProjectiveDoubleModel A.carrier)
  (f g : RoundCylinderSpace → A.carrier)


noncomputable def projectiveDoubleProjection4 (p : RoundCylinderSpace) : A.carrier :=
  projectiveDoubleCycle C f g (p.1, toIcoMod (by norm_num : (0 : ℝ) < 4) 0 p.2)


theorem projectiveDoubleProjection4_translate (z : UnitTwoSphere) (t : ℝ) (n : ℤ) :
    projectiveDoubleProjection4 C f g (z, t + n • (4 : ℝ)) =
      projectiveDoubleProjection4 C f g (z, t) := by
  simp only [projectiveDoubleProjection4, toIcoMod_add_zsmul]


theorem projectiveDoubleProjection4_fundamental {p : RoundCylinderSpace}
    (hp : p.2 ∈ Ico (0 : ℝ) 4) :
    projectiveDoubleProjection4 C f g p = projectiveDoubleCycle C f g p := by
  unfold projectiveDoubleProjection4
  rw [(toIcoMod_eq_self (by norm_num : (0 : ℝ) < 4)).mpr (by simpa using hp)]


theorem projectiveDoubleProjection4_first {p : RoundCylinderSpace}
    (hp : p.2 ∈ Ioo (-1 : ℝ) 1) : projectiveDoubleProjection4 C f g p = f p := by
  by_cases ht : 0 ≤ p.2
  · rw [projectiveDoubleProjection4_fundamental C f g ⟨ht, by linarith [hp.2]⟩,
      projectiveDoubleCycle_first C f g hp.2]
  · have htneg : p.2 < 0 := lt_of_not_ge ht
    have hmod : toIcoMod (by norm_num : (0 : ℝ) < 4) 0 p.2 = 4 + p.2 := by
      apply (toIcoMod_eq_iff (by norm_num : (0 : ℝ) < 4)).mpr
      refine ⟨⟨by linarith [hp.1], by linarith⟩, -1, ?_⟩
      simp only [neg_smul, one_smul]
      ring
    rw [projectiveDoubleProjection4, hmod,
      projectiveDoubleCycle_last C f g (by linarith [hp.1])]
    congr 1
    apply Prod.ext
    · rfl
    · change 4 + p.2 - 4 = p.2
      ring


theorem projectiveDoubleProjection4_second {p : RoundCylinderSpace}
    (hp : p.2 ∈ Ioo (1 : ℝ) 3) :
    projectiveDoubleProjection4 C f g p = g (p.1, 2 - p.2) := by
  rw [projectiveDoubleProjection4_fundamental C f g ⟨by linarith [hp.1], by linarith [hp.2]⟩,
    projectiveDoubleCycle_second C f g hp]


theorem projectiveDoubleProjection4_one (z : UnitTwoSphere) :
    projectiveDoubleProjection4 C f g (z, 1) = C.collar (z, 0) := by
  rw [projectiveDoubleProjection4_fundamental C f g (by norm_num), projectiveDoubleCycle_one]



theorem projectiveDoubleProjection4_germ {p : RoundCylinderSpace}
    (hp : p.2 ∈ Ico (0 : ℝ) 4) :
    projectiveDoubleProjection4 C f g =ᶠ[𝓝 p] projectiveDoubleCycle C f g := by
  rcases eq_or_lt_of_le hp.1 with ht | ht
  · filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds
      (show p.2 ∈ Ioo (-1 : ℝ) 1 by rw [← ht]; norm_num)] with x hx
    rw [projectiveDoubleProjection4_first C f g hx, projectiveDoubleCycle_first C f g hx.2]
  · filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds
      (show p.2 ∈ Ioo (0 : ℝ) 4 from ⟨ht, hp.2⟩)] with x hx
    exact projectiveDoubleProjection4_fundamental C f g ⟨hx.1.le, hx.2⟩



theorem projectiveDoubleProjection4_localDiffeomorph
    (hcycle : ∀ p : RoundCylinderSpace, p.2 ∈ Icc (0 : ℝ) 4 →
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (projectiveDoubleCycle C f g) p) :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (projectiveDoubleProjection4 C f g) := by
  intro p
  let n := toIcoDiv (by norm_num : (0 : ℝ) < 4) 0 p.2
  let D := cylinderAffineChange 1 (-(n • (4 : ℝ))) (by norm_num)
  have hD : (D p).2 ∈ Ico (0 : ℝ) 4 := by
    change 1 * p.2 + -(n • (4 : ℝ)) ∈ Ico (0 : ℝ) 4
    simpa only [one_mul, ← sub_eq_add_neg, zero_add] using
      sub_toIcoDiv_zsmul_mem_Ico (by norm_num : (0 : ℝ) < 4) 0 p.2
  have hl := (hcycle (D p) (Ico_subset_Icc_self hD)).congr_of_eventuallyEq
    (projectiveDoubleProjection4_germ C f g hD)
  apply ((D.isLocalDiffeomorph p).comp (𝓡 3) A.carrier hl).congr_of_eventuallyEq
  apply Eventually.of_forall
  intro x
  change projectiveDoubleProjection4 C f g x =
    projectiveDoubleProjection4 C f g (x.1, 1 * x.2 + -(n • (4 : ℝ)))
  rw [one_mul, ← neg_smul]
  exact (projectiveDoubleProjection4_translate C f g x.1 x.2 (-n)).symm


theorem projectiveDoubleProjection4_surjective
    (hf : f '' (univ ×ˢ Ioo (-1 : ℝ) 1) = C.first_region)
    (hg : g '' (univ ×ˢ Ioo (-1 : ℝ) 1) = C.second_region) :
    Function.Surjective (projectiveDoubleProjection4 C f g) := by
  intro y
  have hy : y ∈ C.first_region ∪ C.second_region ∪ C.sphere := C.cover.symm ▸ mem_univ y
  rcases hy with (hy | hy) | hy
  · obtain ⟨p, hp, rfl⟩ := hf.symm ▸ hy
    exact ⟨p, projectiveDoubleProjection4_first C f g hp.2⟩
  · obtain ⟨p, hp, rfl⟩ := hg.symm ▸ hy
    refine ⟨(p.1, 2 - p.2), ?_⟩
    rw [projectiveDoubleProjection4_second C f g
      ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩]
    simp only [sub_sub_cancel, Prod.mk.eta]
  · obtain ⟨p, hp, rfl⟩ := C.collar_sphere.symm ▸ hy
    have hp0 : p.2 = 0 := hp.2
    refine ⟨(p.1, 1), ?_⟩
    rw [projectiveDoubleProjection4_one C f g]
    congr 1
    exact Prod.ext rfl hp0.symm

end PoincareConjecture.M38
