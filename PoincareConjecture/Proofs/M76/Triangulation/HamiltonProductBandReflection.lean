import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProductBandSides
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnmarkedProductHalves










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 4 : ℝ)) (1 / 4)
local notation "Io" => Ioo (-(1 / 4 : ℝ)) (1 / 4)

private theorem reflection_closed_image (S : Set V2) (r : ℝ) :
    diskTimeReflection.symm '' (S ×ˢ Icc (-r) r) = S ×ˢ Icc (-r) r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1, by change -q.2 ∈ Icc (-r) r; constructor <;> linarith [hq.2.1, hq.2.2]⟩
  · intro hp
    refine ⟨(p.1, -p.2), ⟨hp.1, ?_⟩, ?_⟩
    · constructor <;> linarith [hp.2.1, hp.2.2]
    · change (p.1, - -p.2) = p
      simp only [neg_neg, Prod.eta]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem prescribed_band_reflection_properties {R D : Set E} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct R b)
    (F : (V2 × ℝ) → E) (hF : FinitePiecewiseAffineOn F (Q2 ×ˢ I))
    (hFinj : InjOn F (Q2 ×ˢ I))
    (hFfront : MapsTo F (Q2 ×ˢ I) (frontier R))
    (hcenter : ∀ x ∈ Q2, F (x, 0) = P.map (x, 0))
    (hopen : IsOpen ((Subtype.val : frontier R → E) ⁻¹' (F '' (Q2 ×ˢ Io))))
    {w : ℝ} (hband : MapsTo F (Q2 ×ˢ Icc (-w) w)
      (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1))) :
    FinitePiecewiseAffineOn (F ∘ diskTimeReflection) (Q2 ×ˢ I) ∧
      InjOn (F ∘ diskTimeReflection) (Q2 ×ˢ I) ∧
      MapsTo (F ∘ diskTimeReflection) (Q2 ×ˢ I) (frontier R) ∧
      (∀ x ∈ Q2, (F ∘ diskTimeReflection) (x, 0) = P.reflected.map (x, 0)) ∧
      IsOpen ((Subtype.val : frontier R → E) ⁻¹'
        ((F ∘ diskTimeReflection) '' (Q2 ×ˢ Io))) ∧
      MapsTo (F ∘ diskTimeReflection) (Q2 ×ˢ Icc (-w) w)
        (P.reflected.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)) := by
  have hPL := hF.precomp_affineEquiv diskTimeReflection.toContinuousAffineEquiv
  change FinitePiecewiseAffineOn (F ∘ diskTimeReflection)
    (diskTimeReflection.symm '' (Q2 ×ˢ I)) at hPL
  rw [reflection_closed_image] at hPL
  have hmap : MapsTo diskTimeReflection (Q2 ×ˢ I) (Q2 ×ˢ I) := by
    intro p hp
    exact ⟨hp.1, by change -p.2 ∈ I; constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have himage : (F ∘ diskTimeReflection) '' (Q2 ×ˢ Io) = F '' (Q2 ×ˢ Io) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨diskTimeReflection p, ⟨hp.1, ?_⟩, rfl⟩
      change -p.2 ∈ Io
      constructor <;> linarith [hp.2.1, hp.2.2]
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(p.1, -p.2), ⟨hp.1, ?_⟩, ?_⟩
      · constructor <;> linarith [hp.2.1, hp.2.2]
      · change F (p.1, - -p.2) = F p
        simp only [neg_neg, Prod.eta]
  refine ⟨hPL, ?_, fun p hp => hFfront (hmap hp), ?_, ?_, ?_⟩
  · intro p hp q hq he
    exact diskTimeReflection.injective (hFinj (hmap hp) (hmap hq) he)
  · intro x hx
    change F (x, -(0 : ℝ)) = P.map (x, -(0 : ℝ))
    rw [neg_zero]
    exact hcenter x hx
  · rwa [himage]
  · intro p hp
    have hpr : diskTimeReflection p ∈ Q2 ×ˢ Icc (-w) w :=
      ⟨hp.1, by change -p.2 ∈ Icc (-w) w; constructor <;> linarith [hp.2.1, hp.2.2]⟩
    obtain ⟨z, hz, hzF⟩ := hband hpr
    refine ⟨(z.1, -z.2), ⟨hz.1, ?_⟩, ?_⟩
    · constructor <;> linarith [hz.2.1, hz.2.2]
    · change P.map (z.1, - -z.2) = F (diskTimeReflection p)
      simpa only [neg_neg, Prod.eta] using hzF

variable [FiniteDimensional ℝ E]






theorem prescribed_band_half_images {R D : Set E} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct R b)
    (F : (V2 × ℝ) → E) (hF : FinitePiecewiseAffineOn F (Q2 ×ˢ I))
    (hFinj : InjOn F (Q2 ×ˢ I))
    (hFfront : MapsTo F (Q2 ×ˢ I) (frontier R))
    (hcenter : ∀ x ∈ Q2, F (x, 0) = P.map (x, 0))
    (hopen : IsOpen ((Subtype.val : frontier R → E) ⁻¹' (F '' (Q2 ×ˢ Io))))
    {w : ℝ} (hw : 0 < w) (hwsmall : w ≤ 1 / 4)
    (hband : MapsTo F (Q2 ×ˢ Icc (-w) w)
      (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1))) :
    (MapsTo F (Q2 ×ˢ Icc 0 w) (P.map '' (Q2 ×ˢ Ico (0 : ℝ) 1)) ∧
      MapsTo (F ∘ diskTimeReflection) (Q2 ×ˢ Icc 0 w)
        (P.reflected.map '' (Q2 ×ˢ Ico (0 : ℝ) 1))) ∨
    (MapsTo F (Q2 ×ˢ Icc 0 w) (P.reflected.map '' (Q2 ×ˢ Ico (0 : ℝ) 1)) ∧
      MapsTo (F ∘ diskTimeReflection) (Q2 ×ˢ Icc 0 w)
        (P.map '' (Q2 ×ˢ Ico (0 : ℝ) 1))) := by
  obtain ⟨j, _, _, hPj, hcoord, hzero, hsides⟩ :=
    exists_prescribed_band_opposite_sides P F hF hFinj hFfront hcenter hopen hw hwsmall hband
  have hback (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Icc (-w) w) : P.map (j (F p)) = F p :=
    hPj _ (image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self) (hband hp))
  have hpos (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Icc (-w) w)
      (ht : 0 ≤ (j (F p)).2) : F p ∈ P.map '' (Q2 ×ˢ Ico (0 : ℝ) 1) :=
    ⟨j (F p), ⟨(hcoord p hp).1, ht, (hcoord p hp).2.2⟩, hback p hp⟩
  have hneg (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Icc (-w) w)
      (ht : (j (F p)).2 ≤ 0) : F p ∈ P.reflected.map '' (Q2 ×ˢ Ico (0 : ℝ) 1) := by
    refine ⟨((j (F p)).1, -(j (F p)).2), ⟨(hcoord p hp).1, ?_⟩, ?_⟩
    · constructor <;> linarith [(hcoord p hp).2.1]
    · change P.map ((j (F p)).1, - -(j (F p)).2) = F p
      simpa only [neg_neg, Prod.eta] using hback p hp
  have hplus (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Icc 0 w) :
      p ∈ Q2 ×ˢ Icc (-w) w := ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩
  have hminus (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Icc 0 w) :
      diskTimeReflection p ∈ Q2 ×ˢ Icc (-w) w :=
    ⟨hp.1, by change -p.2 ∈ Icc (-w) w; constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hz (p : V2 × ℝ) (hp : p.1 ∈ Q2) (ht : p.2 = 0) : (j (F p)).2 = 0 := by
    have he : p = (p.1, (0 : ℝ)) := Prod.ext rfl ht
    rw [he, hzero p.1 hp]
  rcases hsides with ⟨hp, hn⟩ | ⟨hp, hn⟩
  · refine Or.inl ⟨?_, ?_⟩
    · intro p h
      apply hpos p (hplus p h)
      by_cases ht : p.2 = 0
      · exact (hz p h.1 ht).ge
      · exact (hp p ⟨h.1, lt_of_le_of_ne h.2.1 (Ne.symm ht), h.2.2⟩).le
    · intro p h
      apply hneg (diskTimeReflection p) (hminus p h)
      by_cases ht : p.2 = 0
      · exact (hz (diskTimeReflection p) h.1 (by change -p.2 = 0; rw [ht, neg_zero])).le
      · apply (hn (diskTimeReflection p) _).le
        have hp0 : 0 < p.2 := lt_of_le_of_ne h.2.1 (Ne.symm ht)
        exact ⟨h.1, by change -w ≤ -p.2 ∧ -p.2 < 0; constructor <;> linarith [h.2.1, h.2.2]⟩
  · refine Or.inr ⟨?_, ?_⟩
    · intro p h
      apply hneg p (hplus p h)
      by_cases ht : p.2 = 0
      · exact (hz p h.1 ht).le
      · exact (hp p ⟨h.1, lt_of_le_of_ne h.2.1 (Ne.symm ht), h.2.2⟩).le
    · intro p h
      apply hpos (diskTimeReflection p) (hminus p h)
      by_cases ht : p.2 = 0
      · exact (hz (diskTimeReflection p) h.1 (by change -p.2 = 0; rw [ht, neg_zero])).ge
      · apply (hn (diskTimeReflection p) _).le
        have hp0 : 0 < p.2 := lt_of_le_of_ne h.2.1 (Ne.symm ht)
        exact ⟨h.1, by change -w ≤ -p.2 ∧ -p.2 < 0; constructor <;> linarith [h.2.1, h.2.2]⟩

end PoincareConjecture.M76.HamiltonIndexOne
