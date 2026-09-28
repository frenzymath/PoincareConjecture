import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ReflectedSourceAnnulus



set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip Dehn

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "P2" => (ℝ × ℝ)




theorem exists_reflected_source_annulus_of_cut_strips
    {X E : Type*} (f : P2 → X) (inverse : E → X) (sigma : P2 × ℝ → E)
    (closing : SignedAxisPermutation) (hswap : closing.swap = true)
    (hsign : closing.sign 0 = closing.sign 1)
    {a b L d : ℝ} (hab : a < b) (hd : 0 < d) (hwidth : 4 * d < L)
    (phi : Fin 2 → P2 → P2)
    (hPL : ∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-1 : ℝ) 1 ×ˢ Icc a b))
    (hvalue : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      f (phi j z) = inverse (sigma (signedSheetStripMap j z)))
    (hclose : ∀ j u, u ∈ Icc (-1 : ℝ) 1 → phi j (u, a) = phi (closing.index j)
      ((if closing.sign j.rev then u else -u), b))
    (hfib : ∀ j k z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      ∀ w, w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      (phi j z = phi k w ↔ (j = k ∧ z = w) ∨
        (z.2 = a ∧ w.2 = b ∧ k = closing.index j ∧
          w.1 = (if closing.sign j.rev then z.1 else -z.1)) ∨
        (w.2 = a ∧ z.2 = b ∧ j = closing.index k ∧
          z.1 = (if closing.sign k.rev then w.1 else -w.1))))
    (A : Set P2)
    (haxis : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b → (phi j z ∈ A ↔ z.1 = 0)) :
    ∃ c : squareAnnulus L d ≃ₜ (⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)),
      c.IsFinitePL ∧ c.symm.IsFinitePL ∧
      (∀ s ∈ Icc 0 (4 * L), ∀ u : Icc (-d) d,
        f (c ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩) =
        if s ≤ 2 * L then
          normalizedReflectedTube closing a b L d hab (by linarith) hd (inverse ∘ sigma) ((u, u), s)
        else
          normalizedReflectedTube closing a b L d hab (by linarith) hd (inverse ∘ sigma)
            ((u, -u), s - 2 * L)) ∧
      ∀ p : squareAnnulus L d, (c p : P2) ∈ A ↔ depth L p = 0 := by
  have hL : 0 < L := by linarith
  have hab2 : a < 2 * b - a := by linarith
  have hsigns (j : Fin 2) : closing.sign j = closing.sign 0 := by
    fin_cases j
    · rfl
    · exact hsign.symm
  have hclose1 : ∀ u ∈ Icc (-1 : ℝ) 1,
      phi 1 (u, a) = phi 0 ((if closing.sign 0 then u else -u), b) := by
    intro u hu
    simpa [SignedAxisPermutation.index, jointSheetIndex, hswap, Fin.rev] using hclose 1 u hu
  have hfib' := hfib
  simp only [SignedAxisPermutation.index, jointSheetIndex, hswap, if_true, hsigns] at hfib'
  let psi := doubledSourceStrip (closing.sign 0) a b phi
  have hpsi : FinitePiecewiseAffineOn psi (Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a)) :=
    doubledSourceStrip_finitePL (closing.sign 0) hab phi hPL hclose1
  obtain ⟨c, hc, _hci, hcvalue⟩ := exists_source_annulus_of_endpoint_strip hd hwidth hab2 psi hpsi
    (doubledSourceStrip_fibers (closing.sign 0) hab phi hfib')
  have himage : psi '' (Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a)) =
      ⋃ j, phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
    rw [doubledSourceStrip_image (closing.sign 0) hab phi hclose1]
    simp [Set.iUnion_fin_add_one_eq_iUnion_succ]
  let c' := c.trans (Homeomorph.setCongr himage)
  have hc' : c'.IsFinitePL := hc.setCongr rfl himage
  have hratio : (2 * b - a - a) / (4 * L) = (b - a) / (2 * L) := by
    field_simp
    ring
  have hval (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      (c' ⟨annulusMap L hL ((s : AddCircle (4 * L)), u),
        _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩ : P2) =
      psi (u / d, a + (b - a) / (2 * L) * s) := by
    change (c ⟨annulusMap L hL ((s : AddCircle (4 * L)), u),
      _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩ : P2) = _
    simpa only [hratio] using hcvalue s hs u
  have hz (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d) :
      (u / d, a + (b - a) / (2 * L) * s) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a) := by
    simpa only [sourceStripPeriodCoordinates_apply, hratio] using
      sourceStripPeriodCoordinates_mapsTo hL hd hab2
        (show (s, (u : ℝ)) ∈ rectangle (4 * L) d from ⟨hs, u.property⟩)
  have htime (s : ℝ) : a + (b - a) / (2 * L) * s ≤ b ↔ s ≤ 2 * L := by
    have hp : 0 < (b - a) / (2 * L) := div_pos (sub_pos.mpr hab) (by positivity)
    have hend : (b - a) / (2 * L) * (2 * L) = b - a := div_mul_cancel₀ _ (by positivity)
    constructor <;> intro h <;> nlinarith
  refine ⟨c', hc', hc'.symm, ?_, ?_⟩
  · intro s hs u
    rw [hval s hs u]
    dsimp only [psi, doubledSourceStrip]
    simp only [htime]
    by_cases h : s ≤ 2 * L
    · simp only [if_pos h]
      rw [hvalue 0 ((if closing.sign 0 then u / d else -(u / d)),
        a + (b - a) / (2 * L) * s) ⟨?_, (hz s hs u).2.1, (htime s).mpr h⟩]
      · change _ = inverse (sigma (reflectedTubeCoordinates closing a b L d hab hL hd ((u, u), s)))
        have he := reflectedTubeCoordinates_diagonal closing a b L d hab hL hd 0 u s
        simp only [ite_true] at he
        rw [he]
      · have hu := (hz s hs u).1
        cases hh : closing.sign 0
        · change -(u / d) ∈ Icc (-1 : ℝ) 1
          constructor <;> linarith [hu.1, hu.2]
        · exact hu
    · simp only [if_neg h]
      rw [hvalue 1 (u / d, a + (b - a) / (2 * L) * s - (b - a)) ⟨(hz s hs u).1, ?_⟩]
      · change _ = inverse (sigma (reflectedTubeCoordinates closing a b L d hab hL hd ((u, -u), s - 2 * L)))
        have he := reflectedTubeCoordinates_diagonal closing a b L d hab hL hd 1 u (s - 2 * L)
        simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)] at he
        rw [he]
        have hend : (b - a) / (2 * L) * (2 * L) = b - a := div_mul_cancel₀ _ (by positivity)
        have ht : a + (b - a) / (2 * L) * s - (b - a) =
            a + (b - a) / (2 * L) * (s - 2 * L) := by nlinarith
        rw [ht]
      · have ht := (hz s hs u).2
        have hs' := mt (htime s).mp h
        constructor <;> linarith [ht.1, ht.2]
  · intro p
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    let u : Icc (-d) d := ⟨depth L p, mem_squareAnnulus_iff_depth.mp p.property⟩
    have hform : (⟨annulusMap L hL ((s : AddCircle (4 * L)), u),
        _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩ : squareAnnulus L d) = p :=
      Subtype.ext hsp.symm
    have hcval := hval s hs u
    rw [hform] at hcval
    rw [hcval, doubledSourceStrip_axis (closing.sign 0) phi A haxis _ (hz s hs u)]
    simp [u, hd.ne']

end PoincareConjecture.M76.Dehn.Annuli
