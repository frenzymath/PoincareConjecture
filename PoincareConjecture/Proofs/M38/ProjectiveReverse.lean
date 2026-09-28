import PoincareConjecture.Proofs.M38.ProjectiveInteriorCut








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


def projectiveCollarReflection :
    Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ where
  toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
  contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
  contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg

variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace StandardCapSpace Q]
  (C : SmoothProjectiveDoubleModel Q)


noncomputable def reverseProjectiveDouble : SmoothProjectiveDoubleModel Q := by
  let r := projectiveCollarReflection
  have hr {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
      r z ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := by
    change (z.1, -z.2) ∈ univ ×ˢ Ioo (-1 : ℝ) 1
    exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hi : (C.collar ∘ r) '' (univ ×ˢ Ioo (-1 : ℝ) 1) =
      C.collar '' (univ ×ˢ Ioo (-1 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨r z, hr hz, rfl⟩
    · rintro _ ⟨⟨z, s⟩, hz, rfl⟩
      refine ⟨(z, -s), hr hz, ?_⟩
      change C.collar (z, - -s) = C.collar (z, s)
      rw [neg_neg]
  refine {
    compact := C.compact
    connected := C.connected
    sphere := C.sphere
    first_region := C.second_region
    second_region := C.first_region
    first_open := C.second_open
    second_open := C.first_open
    disjoint := C.disjoint.symm
    sphere_disjoint := by simpa only [union_comm] using C.sphere_disjoint
    cover := by simpa only [union_comm C.first_region C.second_region] using C.cover
    first_puncture := C.second_puncture
    second_puncture := C.first_puncture
    first_model := C.second_model
    second_model := C.first_model
    collar := C.collar ∘ r
    collar_local_diffeomorph := ?_
    collar_injective := fun _ hz _ hw h =>
      r.injective (C.collar_injective (hr hz) (hr hw) h)
    collar_open := hi.symm ▸ C.collar_open
    collar_sphere := ?_
    collar_negative := ?_
    collar_positive := ?_ }
  · intro z
    exact (r.isLocalDiffeomorph z.val).comp (𝓡 3) Q
      (C.collar_local_diffeomorph ⟨r z.val, hr z.property⟩)
  · rw [← C.collar_sphere]
    apply image_congr
    rintro ⟨z, s⟩ ⟨_, hs⟩
    have hs0 : s = 0 := hs
    subst s
    change C.collar (z, -(0 : ℝ)) = C.collar (z, 0)
    rw [neg_zero]
  · rintro _ ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
    exact C.collar_positive ⟨(z, -s),
      ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩, rfl⟩
  · rintro _ ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
    exact C.collar_negative ⟨(z, -s),
      ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩, rfl⟩



theorem exists_projectiveDouble_second_interior_cut [T2Space Q] {O : Set Q}
    (hO : IsOpen O) (hSO : C.sphere ⊆ O) :
    ∃ (e : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
      (H : Diffeomorph (𝓡 3) (𝓡 3) Q Q ∞),
      StrictMono e ∧ e 0 ∈ Ioo (0 : ℝ) 1 ∧
      (∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-1 : ℝ) 1 →
        H (C.collar (z, s)) = C.collar (z, e s)) ∧
      H '' closure C.second_region ⊆ C.second_region ∧
      ∀ x : Q, x ∉ O → H x = x := by
  obtain ⟨e, H, he, he0, hH, hside, hfix⟩ :=
    exists_projectiveDouble_first_interior_cut (reverseProjectiveDouble C) hO hSO
  let n : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toEquiv := Equiv.neg ℝ
    contMDiff_toFun := contMDiff_id.neg
    contMDiff_invFun := contMDiff_id.neg }
  let d := (n.trans e).trans n
  have hd (s : ℝ) : d s = -(e (-s)) := rfl
  refine ⟨d, H, ?_, ?_, ?_, hside, hfix⟩
  · intro s t hst
    rw [hd, hd]
    exact neg_lt_neg (he (neg_lt_neg hst))
  · simpa only [hd, neg_zero, mem_Ioo, neg_pos, neg_lt, neg_neg] using
      (show 0 < -(e 0) ∧ -(e 0) < 1 from
        ⟨neg_pos.mpr he0.2, by linarith [he0.1]⟩)
  · intro z s hs
    have h := hH z (-s) (by constructor <;> linarith [hs.1, hs.2])
    change H (C.collar (z, - -s)) = C.collar (z, -(e (-s))) at h
    simpa only [hd, neg_neg] using h

end PoincareConjecture.M38
