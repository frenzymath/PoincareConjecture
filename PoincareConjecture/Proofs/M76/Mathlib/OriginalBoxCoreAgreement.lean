import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes











set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace Geometry






theorem original_box_eq_iff_core_coordinates
    {E : Type*} (F₀ F₁ f : ((ℝ × ℝ) × ℝ) → E) {r : ℝ} (hr : 0 < r)
    (hinj₀ : InjOn F₀ (box r)) (hinj₁ : InjOn F₁ (box r))
    (hlateral₀ : ∀ u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F₀ ((u, r), z) = f ((u, 0), z))
    (hlateral₁ : ∀ u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F₁ ((u, -r), z) = f ((u, 0), z))
    (hcontact : (F₀ '' box r) ∩ (F₁ '' box r) =
      f '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r))
    {x y : (ℝ × ℝ) × ℝ} (hx : x ∈ box r) (hy : y ∈ box r) :
    F₀ x = F₁ y ↔
      (F₀ ((0, x.1.2), 0), (x.1.1, x.2)) =
        (F₁ ((0, y.1.2), 0), (y.1.1, y.2)) := by
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hneg : -r ∈ Icc (-r) r := ⟨le_rfl, by linarith⟩
  have hpos : r ∈ Icc (-r) r := ⟨by linarith, le_rfl⟩
  have hcollision (v w : (ℝ × ℝ) × ℝ) (hv : v ∈ box r) (hw : w ∈ box r)
      (heq : F₀ v = F₁ w) :
      ∃ u z : ℝ, u ∈ Icc (-r) r ∧ z ∈ Icc (-r) r ∧
        v = ((u, r), z) ∧ w = ((u, -r), z) := by
    obtain ⟨⟨⟨u, s⟩, z⟩, ⟨⟨hu, hs⟩, hz⟩, hfval⟩ :=
      hcontact.subset ⟨mem_image_of_mem F₀ hv, ⟨w, hw, heq.symm⟩⟩
    have hs0 : s = 0 := hs
    subst s
    refine ⟨u, z, hu, hz, ?_, ?_⟩
    · exact hinj₀ hv ⟨⟨hu, hpos⟩, hz⟩
        (hfval.symm.trans (hlateral₀ u z hu hz).symm)
    · exact hinj₁ hw ⟨⟨hu, hneg⟩, hz⟩
        (heq.symm.trans (hfval.symm.trans (hlateral₁ u z hu hz).symm))
  constructor
  · intro h
    obtain ⟨u, z, _, _, rfl, rfl⟩ := hcollision x y hx hy h
    exact Prod.ext ((hlateral₀ 0 0 hzero hzero).trans
      (hlateral₁ 0 0 hzero hzero).symm) rfl
  · intro h
    have hcore := congrArg Prod.fst h
    change F₀ ((0, x.1.2), 0) = F₁ ((0, y.1.2), 0) at hcore
    obtain ⟨u, z, _, _, hxc, hyc⟩ := hcollision ((0, x.1.2), 0) ((0, y.1.2), 0)
      ⟨⟨hzero, hx.1.2⟩, hzero⟩ ⟨⟨hzero, hy.1.2⟩, hzero⟩ hcore
    have hxs := congrArg (fun v : (ℝ × ℝ) × ℝ => v.1.2) hxc
    change x.1.2 = r at hxs
    have hys := congrArg (fun v : (ℝ × ℝ) × ℝ => v.1.2) hyc
    change y.1.2 = -r at hys
    have hcoords := congrArg Prod.snd h
    change (x.1.1, x.2) = (y.1.1, y.2) at hcoords
    have hxleft := hlateral₀ x.1.1 x.2 hx.1.1 hx.2
    have hyright := hlateral₁ y.1.1 y.2 hy.1.1 hy.2
    have hxform : x = ((x.1.1, r), x.2) := Prod.ext (Prod.ext rfl hxs) rfl
    have hyform : y = ((y.1.1, -r), y.2) := Prod.ext (Prod.ext rfl hys) rfl
    have hu := congrArg (fun q : ℝ × ℝ => q.1) hcoords
    change x.1.1 = y.1.1 at hu
    have hz := congrArg (fun q : ℝ × ℝ => q.2) hcoords
    change x.2 = y.2 at hz
    have hshared : ((x.1.1, (0 : ℝ)), x.2) = ((y.1.1, (0 : ℝ)), y.2) :=
      Prod.ext (Prod.ext hu rfl) hz
    calc
      F₀ x = F₀ ((x.1.1, r), x.2) := congrArg F₀ hxform
      _ = f ((x.1.1, 0), x.2) := hxleft
      _ = f ((y.1.1, 0), y.2) := congrArg f hshared
      _ = F₁ ((y.1.1, -r), y.2) := hyright.symm
      _ = F₁ y := (congrArg F₁ hyform).symm

end Geometry
