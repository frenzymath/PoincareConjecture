import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTubeSigns
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)

noncomputable def sourceStripPeriodCoordinates (L d a b : ℝ) : P2 →ᴬ[ℝ] P2 :=
  ((d⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).prod
    (ContinuousAffineMap.const ℝ P2 a +
      (((b - a) / (4 * L)) • ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap)

theorem sourceStripPeriodCoordinates_apply (L d a b : ℝ) (x : P2) :
    sourceStripPeriodCoordinates L d a b x =
      (x.2 / d, a + ((b - a) / (4 * L)) * x.1) := by
  simp [sourceStripPeriodCoordinates, div_eq_inv_mul]

theorem sourceStripPeriodCoordinates_mapsTo {L d a b : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hab : a < b) :
    MapsTo (sourceStripPeriodCoordinates L d a b) (rectangle (4 * L) d)
      (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
  intro x hx
  have hp : 0 < 4 * L := by positivity
  have hc : 0 < (b - a) / (4 * L) := div_pos (sub_pos.mpr hab) hp
  rw [sourceStripPeriodCoordinates_apply]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mem_Icc, le_div_iff₀ hd, div_le_iff₀ hd, neg_one_mul, one_mul] using hx.2
  · nlinarith [mul_nonneg hc.le hx.1.1]
  · have hh := mul_le_mul_of_nonneg_left hx.1.2 hc.le
    rw [div_mul_cancel₀ _ hp.ne'] at hh
    linarith

theorem sourceStripPeriodCoordinates_image {L d a b : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hab : a < b) :
    sourceStripPeriodCoordinates L d a b '' rectangle (4 * L) d =
      Icc (-1 : ℝ) 1 ×ˢ Icc a b := by
  apply Subset.antisymm (sourceStripPeriodCoordinates_mapsTo hL hd hab).image_subset
  rintro ⟨u, t⟩ ⟨hu, ht⟩
  have hp : 0 < 4 * L := by positivity
  have hdiff : 0 < b - a := sub_pos.mpr hab
  refine ⟨((4 * L) * ((t - a) / (b - a)), d * u), ?_, ?_⟩
  · refine ⟨⟨mul_nonneg hp.le (div_nonneg (sub_nonneg.mpr ht.1) hdiff.le), ?_⟩, ?_⟩
    · have hh : (t - a) / (b - a) ≤ 1 := (div_le_one hdiff).mpr (by linarith [ht.2])
      nlinarith
    · constructor <;> nlinarith [hu.1, hu.2]
  · rw [sourceStripPeriodCoordinates_apply]
    apply Prod.ext
    · dsimp
      field_simp
    · dsimp
      field_simp
      ring

theorem sourceStripPeriodCoordinates_finitePL {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (a b : ℝ) : FinitePiecewiseAffineOn (sourceStripPeriodCoordinates L d a b)
      (rectangle (4 * L) d) := by
  have hbox := (isFinitePLBallPair_Icc (show (0 : ℝ) < 4 * L by positivity)).prod
    (isFinitePLBallPair_Icc (show -d < d by linarith))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hbox
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (sourceStripPeriodCoordinates L d a b)⟩

theorem source_strip_period_fibers {E : Type*} {L d a b : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hab : a < b) (phi : P2 → E)
    (hfib : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b, ∀ y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      phi x = phi y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = a ∧ y.2 = b) ∨ (y.2 = a ∧ x.2 = b))) :
    ∀ x ∈ rectangle (4 * L) d, ∀ y ∈ rectangle (4 * L) d,
      (phi ∘ sourceStripPeriodCoordinates L d a b) x =
        (phi ∘ sourceStripPeriodCoordinates L d a b) y ↔
      x.2 = y.2 ∧ (x.1 : AddCircle (4 * L)) = (y.1 : AddCircle (4 * L)) := by
  intro x hx y hy
  let : Fact (0 < 4 * L) := ⟨by positivity⟩
  have hp : 0 < 4 * L := by positivity
  have hc : 0 < (b - a) / (4 * L) := div_pos (sub_pos.mpr hab) hp
  have hcp : ((b - a) / (4 * L)) * (4 * L) = b - a := div_mul_cancel₀ _ hp.ne'
  have htime (s t : ℝ) :
      a + ((b - a) / (4 * L)) * s = a + ((b - a) / (4 * L)) * t ↔ s = t :=
    add_left_cancel_iff.trans (mul_right_inj' hc.ne')
  have hstart (s : ℝ) : a + ((b - a) / (4 * L)) * s = a ↔ s = 0 := by
    simpa only [mul_zero, add_zero] using htime s 0
  have hend (s : ℝ) : a + ((b - a) / (4 * L)) * s = b ↔ s = 4 * L := by
    simpa only [hcp, add_sub_cancel] using htime s (4 * L)
  rw [Function.comp_apply, Function.comp_apply,
    hfib _ (sourceStripPeriodCoordinates_mapsTo hL hd hab hx)
      _ (sourceStripPeriodCoordinates_mapsTo hL hd hab hy),
    sourceStripPeriodCoordinates_apply, sourceStripPeriodCoordinates_apply,
    AddCircle.coe_eq_coe_iff_eq_or_endpoints hx.1 hy.1]
  simp only [div_left_inj' hd.ne', htime, hstart, hend]
  tauto

theorem exists_source_annulus_of_endpoint_strip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L d a b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hab : a < b)
    (phi : P2 → E) (hphi : FinitePiecewiseAffineOn phi (Icc (-1 : ℝ) 1 ×ˢ Icc a b))
    (hfib : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b, ∀ y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      phi x = phi y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = a ∧ y.2 = b) ∨ (y.2 = a ∧ x.2 = b))) :
    ∃ c : squareAnnulus L d ≃ₜ (phi '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)),
      c.IsFinitePL ∧ c.symm.IsFinitePL ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        (c ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩ : E) =
        phi (u / d, a + ((b - a) / (4 * L)) * s)) := by
  have hL : 0 < L := by linarith
  let psi := phi ∘ sourceStripPeriodCoordinates L d a b
  have hpsi : FinitePiecewiseAffineOn psi (rectangle (4 * L) d) :=
    hphi.comp (sourceStripPeriodCoordinates_finitePL hL hd a b)
      (sourceStripPeriodCoordinates_mapsTo hL hd hab)
  obtain ⟨c, hc, hci, hval, _⟩ := _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
    hd hwidth psi hpsi (source_strip_period_fibers hL hd hab phi hfib)
  have himage : psi '' rectangle (4 * L) d = phi '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
    change (phi ∘ sourceStripPeriodCoordinates L d a b) '' rectangle (4 * L) d = _
    rw [image_comp, sourceStripPeriodCoordinates_image hL hd hab]
  let c' := c.trans (Homeomorph.setCongr himage)
  have hc' : c'.IsFinitePL := by
    obtain ⟨g, hg, hgval⟩ := hc
    exact ⟨g, hg, hgval⟩
  refine ⟨c', hc', hc'.symm, ?_⟩
  intro s hs u
  exact (hval s hs u).trans (congrArg phi (sourceStripPeriodCoordinates_apply L d a b (s, u)))

end PoincareConjecture.M76.Dehn
