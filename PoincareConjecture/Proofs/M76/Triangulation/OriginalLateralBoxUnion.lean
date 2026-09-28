import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Triangulation.PLBallActualDiskAttachment

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem union_original_lateral_box_ballPair
    (F₀ F₁ : ((ℝ × ℝ) × ℝ) → E)
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hF₀ : FinitePiecewiseAffineOn F₀ (box r))
    (hF₁ : FinitePiecewiseAffineOn F₁ (box r))
    (hinj₀ : InjOn F₀ (box r)) (hinj₁ : InjOn F₁ (box r))
    (hlateral₀ : ∀ t z, t ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F₀ ((t, r), z) = f ((t, 0), z))
    (hlateral₁ : ∀ t z, t ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F₁ ((t, -r), z) = f ((t, 0), z))
    (hcontact : (F₀ '' box r) ∩ (F₁ '' box r) =
      f '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r)) :
    let d := f '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r)
    let q := f '' ((({-r, r} ×ˢ {0}) ×ˢ Icc (-r) r) ∪
      ((Icc (-r) r ×ˢ {0}) ×ˢ {-r, r}))
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) ((F₀ '' box r) ∪ (F₁ '' box r))
      (((F₀ '' boxBoundary r) \ (d \ q)) ∪
        ((F₁ '' boxBoundary r) \ (d \ q))) := by
  let D : Set ((ℝ × ℝ) × ℝ) := (Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r
  let Q : Set ((ℝ × ℝ) × ℝ) :=
    (({-r, r} ×ˢ {0}) ×ˢ Icc (-r) r) ∪ ((Icc (-r) r ×ˢ {0}) ×ˢ {-r, r})
  have hI : IsFinitePLBallPair ℝ (Icc (-r) r) {-r, r} :=
    isFinitePLBallPair_Icc (by linarith)
  have hD : IsFinitePLBallPair (ℝ × ℝ) D Q := (hI.prod_singleton (0 : ℝ)).prod hI
  have hd : IsFinitePLBallPair (ℝ × ℝ) (f '' D) (f '' Q) :=
    hD.affine_image f.toContinuousAffineMap f.injective.injOn
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hneg : -r ∈ Icc (-r) r := ⟨le_rfl, by linarith⟩
  have hpos : r ∈ Icc (-r) r := ⟨by linarith, le_rfl⟩
  have hleft (t z : ℝ) (ht : t ∈ Icc (-r) r) (hz : z ∈ Icc (-r) r) :
      ((t, -r), z) ∈ boxBoundary r :=
    Or.inl ⟨Or.inr ⟨ht, Or.inl rfl⟩, hz⟩
  have hright (t z : ℝ) (ht : t ∈ Icc (-r) r) (hz : z ∈ Icc (-r) r) :
      ((t, r), z) ∈ boxBoundary r :=
    Or.inl ⟨Or.inr ⟨ht, Or.inr rfl⟩, hz⟩
  have hd₀ : f '' D ⊆ F₀ '' boxBoundary r := by
    rintro _ ⟨⟨⟨t, s⟩, z⟩, ⟨⟨ht, hs⟩, hz⟩, rfl⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨((t, r), z), hright t z ht hz, hlateral₀ t z ht hz⟩
  have hd₁ : f '' D ⊆ F₁ '' boxBoundary r := by
    rintro _ ⟨⟨⟨t, s⟩, z⟩, ⟨⟨ht, hs⟩, hz⟩, rfl⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨((t, -r), z), hleft t z ht hz, hlateral₁ t z ht hz⟩
  have hout₀ : ((F₀ '' boxBoundary r) \ (f '' D)).Nonempty := by
    refine ⟨F₀ ((0, -r), 0), ⟨_, hleft 0 0 hzero hzero, rfl⟩, ?_⟩
    rintro ⟨⟨⟨t, s⟩, z⟩, ⟨⟨ht, hs⟩, hz⟩, heq⟩
    have hs0 : s = 0 := hs
    subst s
    have hpoints : ((0, -r), 0) = ((t, r), z) :=
      hinj₀ ⟨⟨hzero, hneg⟩, hzero⟩ ⟨⟨ht, hpos⟩, hz⟩
        (heq.symm.trans (hlateral₀ t z ht hz).symm)
    have hbad : -r = r := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) hpoints
    linarith
  have hout₁ : ((F₁ '' boxBoundary r) \ (f '' D)).Nonempty := by
    refine ⟨F₁ ((0, r), 0), ⟨_, hright 0 0 hzero hzero, rfl⟩, ?_⟩
    rintro ⟨⟨⟨t, s⟩, z⟩, ⟨⟨ht, hs⟩, hz⟩, heq⟩
    have hs0 : s = 0 := hs
    subst s
    have hpoints : ((0, r), 0) = ((t, -r), z) :=
      hinj₁ ⟨⟨hzero, hpos⟩, hzero⟩ ⟨⟨ht, hneg⟩, hz⟩
        (heq.symm.trans (hlateral₁ t z ht hz).symm)
    have hbad : r = -r := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) hpoints
    linarith
  exact ((box_ballPair hr).image hF₀ hinj₀).union_of_actual_disk_contact
    ((box_ballPair hr).image hF₁ hinj₁) hd hd₀ hd₁ hout₀ hout₁ hcontact

end Geometry
