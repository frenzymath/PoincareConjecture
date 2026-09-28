import PoincareConjecture.Proofs.M76.Mathlib.OriginalBoxCoreAgreement










set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace Geometry






theorem cyclic_box_eq_iff_core_coordinates
    {E ι : Type*} (next : ι → ι) (F f : ι → ((ℝ × ℝ) × ℝ) → E)
    {r : ℝ} (hr : 0 < r) (hinj : ∀ i, InjOn (F i) (box r))
    (hlateral : ∀ i (j : Bool) u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F i ((u, if j then r else -r), z) = f (if j then next i else i) ((u, 0), z))
    (hcontact : ∀ i, (F i '' box r) ∩ (F (next i) '' box r) =
      f (next i) '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r))
    (hdisjoint : ∀ i j, i ≠ j → next i ≠ j → next j ≠ i →
      Disjoint (F i '' box r) (F j '' box r))
    (i j : ι) {x y : (ℝ × ℝ) × ℝ} (hx : x ∈ box r) (hy : y ∈ box r) :
    F i x = F j y ↔
      (F i ((0, x.1.2), 0), (x.1.1, x.2)) =
        (F j ((0, y.1.2), 0), (y.1.1, y.2)) := by
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hxcore : ((0, x.1.2), 0) ∈ box r := ⟨⟨hzero, hx.1.2⟩, hzero⟩
  have hycore : ((0, y.1.2), 0) ∈ box r := ⟨⟨hzero, hy.1.2⟩, hzero⟩
  by_cases hij : i = j
  · subst j
    constructor
    · intro h
      rw [hinj i hx hy h]
    · intro h
      have hc := congrArg Prod.fst h
      have hmiddle := congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.2)
        (hinj i hxcore hycore hc)
      change x.1.2 = y.1.2 at hmiddle
      have hcoords := congrArg Prod.snd h
      have hu := congrArg (fun q : ℝ × ℝ => q.1) hcoords
      change x.1.1 = y.1.1 at hu
      have hz := congrArg (fun q : ℝ × ℝ => q.2) hcoords
      change x.2 = y.2 at hz
      exact congrArg (F i) (Prod.ext
        (Prod.ext hu hmiddle) hz)
  by_cases hnext : next i = j
  · subst j
    exact original_box_eq_iff_core_coordinates (F i) (F (next i)) (f (next i)) hr
      (hinj i) (hinj (next i)) (hlateral i true) (hlateral (next i) false)
      (hcontact i) hx hy
  by_cases hprev : next j = i
  · subst i
    have h := original_box_eq_iff_core_coordinates (F j) (F (next j)) (f (next j)) hr
      (hinj j) (hinj (next j)) (hlateral j true) (hlateral (next j) false)
      (hcontact j) hy hx
    exact ⟨fun heq => ((h.mp heq.symm).symm), fun heq => (h.mpr heq.symm).symm⟩
  have hd := hdisjoint i j hij hnext hprev
  constructor
  · intro h
    exact (disjoint_left.mp hd (mem_image_of_mem _ hx) ⟨y, hy, h.symm⟩).elim
  · intro h
    have hc := congrArg Prod.fst h
    exact (disjoint_left.mp hd (mem_image_of_mem _ hxcore)
      ⟨((0, y.1.2), 0), hycore, hc.symm⟩).elim

end Geometry
