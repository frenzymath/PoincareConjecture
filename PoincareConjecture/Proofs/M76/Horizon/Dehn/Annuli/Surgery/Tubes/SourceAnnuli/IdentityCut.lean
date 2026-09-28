import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedSourceAnnuli

set_option autoImplicit false
open Set Geometry PLAnnularStrip Dehn

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "P2" => (ℝ × ℝ)

theorem exists_identity_source_annuli_of_cut_strips
    {X E : Type*} (f : P2 → X) (inverse : E → X) (sigma : P2 × ℝ → E)
    {a b L d : ℝ} (hab : a < b) (hd : 0 < d) (hwidth : 4 * d < L)
    (phi : Fin 2 → P2 → P2)
    (hPL : ∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-1 : ℝ) 1 ×ˢ Icc a b))
    (hvalue : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      f (phi j z) = inverse (sigma (signedSheetStripMap j z)))
    (hfib : ∀ j k z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      ∀ w, w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      (phi j z = phi k w ↔ j = k ∧ z.1 = w.1 ∧
        (z.2 = w.2 ∨ (z.2 = a ∧ w.2 = b) ∨ (w.2 = a ∧ z.2 = b))))
    (A : Fin 2 → Set P2)
    (haxis : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b → (phi j z ∈ A j ↔ z.1 = 0))
    (hcover : ∀ j, (fun s ↦ phi j (0, s)) '' Icc a b = A j) :
    ∃ c : ∀ j, squareAnnulus L d ≃ₜ (phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)),
      (∀ j, (c j).IsFinitePL ∧ (c j).symm.IsFinitePL) ∧
      Disjoint (phi 0 '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b))
        (phi 1 '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)) ∧
      (∀ j s, s ∈ Icc 0 (4 * L) → ∀ u : Icc (-d) d,
        f (c j ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩) =
          inverse (sigma (periodicTubeCoordinates L d a b (sourceTubeDiagonal j u, s)))) ∧
      (∀ j (p : squareAnnulus L d), (c j p : P2) ∈ A j ↔ depth L p = 0) ∧
      ∀ j, (fun p : squareAnnulus L d ↦ (c j p : P2)) '' {p | depth L p = 0} = A j := by
  have hL : 0 < L := by linarith
  have hperiodFib (j : Fin 2) : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      ∀ w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
      phi j z = phi j w ↔ z.1 = w.1 ∧
        (z.2 = w.2 ∨ (z.2 = a ∧ w.2 = b) ∨ (w.2 = a ∧ z.2 = b)) := by
    intro z hz w hw
    simpa only [true_and] using hfib j j z hz w hw
  choose c hc hci hcperiod using fun j ↦
    exists_source_annulus_of_endpoint_strip hd hwidth hab (phi j) (hPL j) (hperiodFib j)
  have hcval (j : Fin 2) (p : squareAnnulus L d) (s : ℝ) (hs : s ∈ Icc 0 (4 * L))
      (hp : (p : P2) = annulusMap L hL ((s : AddCircle (4 * L)), depth L p)) :
      (c j p : P2) = phi j (sourceStripPeriodCoordinates L d a b (s, depth L p)) := by
    have hu : depth L p ∈ Icc (-d) d := mem_squareAnnulus_iff_depth.mp p.property
    have heq : p = ⟨annulusMap L hL ((s : AddCircle (4 * L)), depth L p),
        _root_.Dehn.annulus_period_point_mem hd hwidth _ ⟨depth L p, hu⟩⟩ := Subtype.ext hp
    calc
      (c j p : P2) = c j ⟨annulusMap L hL ((s : AddCircle (4 * L)), depth L p),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ ⟨depth L p, hu⟩⟩ :=
        congrArg (fun q ↦ (c j q : P2)) heq
      _ = phi j (depth L p / d, a + ((b - a) / (4 * L)) * s) := hcperiod j s hs ⟨_, hu⟩
      _ = _ := congrArg (phi j)
        (sourceStripPeriodCoordinates_apply L d a b (s, depth L p)).symm
  have htrace (j : Fin 2) (p : squareAnnulus L d) :
      (c j p : P2) ∈ A j ↔ depth L p = 0 := by
    obtain ⟨s, hs, hp⟩ := exists_period_parameter_of_depth hd hwidth p
    have hu := mem_squareAnnulus_iff_depth.mp p.property
    rw [hcval j p s hs hp, haxis j _
      (sourceStripPeriodCoordinates_mapsTo hL hd hab ⟨hs, hu⟩),
      sourceStripPeriodCoordinates_apply]
    simp [div_eq_zero_iff, hd.ne']
  refine ⟨c, fun j ↦ ⟨hc j, hci j⟩, ?_, ?_, htrace, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    exact (show (0 : Fin 2) ≠ 1 by decide) ((hfib 0 1 z hz w hw).mp heq.symm).1
  · intro j s hs u
    rw [hcperiod j s hs u, periodicTubeCoordinates_diagonal]
    have hx := sourceStripPeriodCoordinates_mapsTo hL hd hab (show
      (s, (u : ℝ)) ∈ rectangle (4 * L) d from ⟨hs, u.property⟩)
    simpa only [sourceStripPeriodCoordinates_apply] using hvalue j _ hx
  · intro j
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (htrace j p).mpr hp
    · intro hx
      obtain ⟨s, hs, hxs⟩ := (hcover j).symm.subset hx
      have hxA : x ∈ phi j '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b) :=
        ⟨(0, s), ⟨by norm_num, hs⟩, hxs⟩
      refine ⟨(c j).symm ⟨x, hxA⟩, ?_, ?_⟩
      · apply (htrace j _).mp
        simpa only [Homeomorph.apply_symm_apply] using hx
      · exact congrArg Subtype.val ((c j).apply_symm_apply _)

end PoincareConjecture.M76.Dehn.Annuli
