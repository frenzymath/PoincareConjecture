import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProductBandContainment
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 4 : ℝ)) (1 / 4)
local notation "Io" => Ioo (-(1 / 4 : ℝ)) (1 / 4)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem both_time_signs_in_prescribed_band {R D : Set E} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct R b)
    (F : (V2 × ℝ) → E) (hF : FinitePiecewiseAffineOn F (Q2 ×ˢ I))
    (hFinj : InjOn F (Q2 ×ˢ I))
    (hcenter : ∀ x ∈ Q2, F (x, 0) = P.map (x, 0))
    (hopen : IsOpen ((Subtype.val : frontier R → E) ⁻¹' (F '' (Q2 ×ˢ Io))))
    {w : ℝ} (hw : 0 < w)
    (j : E → (V2 × ℝ))
    (hjP : ∀ p ∈ D2 ×ˢ Icc (-1 : ℝ) 1, j (P.map p) = p) :
    (∃ p ∈ Q2 ×ˢ Icc (-w) w, 0 < (j (F p)).2) ∧
      ∃ p ∈ Q2 ×ˢ Icc (-w) w, (j (F p)).2 < 0 := by
  let Z := F '' (Q2 ×ˢ (I \ Ioo (-w) w))
  have hZ : IsCompact Z :=
    ((isCompact_sphere (0 : V2) 1).prod (isCompact_Icc.diff isOpen_Ioo)).image_of_continuousOn
      (hF.continuousOn.mono (fun _ hp => ⟨hp.1, hp.2.1⟩))
  let V := ((Subtype.val : frontier R → E) ⁻¹' (F '' (Q2 ×ˢ Io))) \
    (Subtype.val : frontier R → E) ⁻¹' Z
  have hV : IsOpen V := hopen.sdiff (hZ.isClosed.preimage continuous_subtype_val)
  let x0 : V2 := 1
  have hx0 : x0 ∈ Q2 := mem_sphere_zero_iff_norm.mpr norm_one
  let curve : Icc (-1 : ℝ) 1 → frontier R := fun t =>
    ⟨P.map (x0, (t : ℝ)),
      (P.proper _ ⟨sphere_subset_closedBall hx0, t.property⟩).mpr hx0⟩
  have hcurve : Continuous curve := by
    apply Continuous.subtype_mk
    exact P.piecewiseAffine.continuousOn.comp_continuous
      (continuous_const.prodMk continuous_subtype_val)
      (fun t => ⟨sphere_subset_closedBall hx0, t.property⟩)
  let t0 : Icc (-1 : ℝ) 1 := ⟨0, by norm_num⟩
  have h0 : curve t0 ∈ V := by
    constructor
    · change P.map (x0, 0) ∈ F '' (Q2 ×ˢ Io)
      exact ⟨(x0, 0), ⟨hx0, by norm_num⟩, hcenter x0 hx0⟩
    · rintro ⟨p, hp, hp0⟩
      change F p = P.map (x0, 0) at hp0
      have hpq : p = (x0, (0 : ℝ)) := hFinj ⟨hp.1, hp.2.1⟩
        ⟨hx0, by norm_num⟩ (hp0.trans (hcenter x0 hx0).symm)
      have ht : p.2 = 0 := congrArg Prod.snd hpq
      apply hp.2.2
      rw [ht]
      exact ⟨neg_lt_zero.mpr hw, hw⟩
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.mp (hV.preimage hcurve) t0 h0
  have hex (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) (htr : |t| < r) :
      ∃ p ∈ Q2 ×ˢ Icc (-w) w, (j (F p)).2 = t := by
    have hv : curve ⟨t, ht⟩ ∈ V := hrv (by
      change dist t (0 : ℝ) < r
      rwa [Real.dist_eq, sub_zero])
    obtain ⟨p, hp, hpt⟩ := hv.1
    change F p = P.map (x0, t) at hpt
    have hpw : p.2 ∈ Ioo (-w) w := by
      by_contra hn
      exact hv.2 ⟨p, ⟨hp.1, Ioo_subset_Icc_self hp.2, hn⟩, hpt⟩
    refine ⟨p, ⟨hp.1, Ioo_subset_Icc_self hpw⟩, ?_⟩
    rw [hpt, hjP _ ⟨sphere_subset_closedBall hx0, ht⟩]
  let s := min (r / 2) (1 / 2 : ℝ)
  have hs : 0 < s := lt_min (half_pos hr) (by norm_num)
  have hs1 : s ≤ (1 / 2 : ℝ) := min_le_right _ _
  have hsr : s < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  obtain ⟨p, hp, hpv⟩ := hex s ⟨by linarith, by linarith⟩
    (by rw [abs_of_pos hs]; exact hsr)
  obtain ⟨q, hq, hqv⟩ := hex (-s) ⟨by linarith, by linarith⟩
    (by rw [abs_neg, abs_of_pos hs]; exact hsr)
  refine ⟨⟨p, hp, ?_⟩, ⟨q, hq, ?_⟩⟩
  · rw [hpv]
    exact hs
  · rw [hqv]
    exact neg_neg_of_pos hs

theorem exists_prescribed_band_opposite_sides {R D : Set E} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct R b)
    (F : (V2 × ℝ) → E) (hF : FinitePiecewiseAffineOn F (Q2 ×ˢ I))
    (hFinj : InjOn F (Q2 ×ˢ I))
    (hFfront : MapsTo F (Q2 ×ˢ I) (frontier R))
    (hcenter : ∀ x ∈ Q2, F (x, 0) = P.map (x, 0))
    (hopen : IsOpen ((Subtype.val : frontier R → E) ⁻¹' (F '' (Q2 ×ˢ Io))))
    {w : ℝ} (hw : 0 < w) (hwsmall : w ≤ 1 / 4)
    (hband : MapsTo F (Q2 ×ˢ Icc (-w) w)
      (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1))) :
    ∃ j : E → (V2 × ℝ),
      FinitePiecewiseAffineOn j (P.map '' (D2 ×ˢ Icc (-1 : ℝ) 1)) ∧
      (∀ p ∈ D2 ×ˢ Icc (-1 : ℝ) 1, j (P.map p) = p) ∧
      (∀ y ∈ P.map '' (D2 ×ˢ Icc (-1 : ℝ) 1), P.map (j y) = y) ∧
      (∀ p ∈ Q2 ×ˢ Icc (-w) w, j (F p) ∈ Q2 ×ˢ Ioo (-1 : ℝ) 1) ∧
      (∀ x ∈ Q2, j (F (x, 0)) = (x, 0)) ∧
      (((∀ p ∈ Q2 ×ˢ Ioc 0 w, 0 < (j (F p)).2) ∧
        (∀ p ∈ Q2 ×ˢ Ico (-w) 0, (j (F p)).2 < 0)) ∨
       ((∀ p ∈ Q2 ×ˢ Ioc 0 w, (j (F p)).2 < 0) ∧
        (∀ p ∈ Q2 ×ˢ Ico (-w) 0, 0 < (j (F p)).2))) := by
  obtain ⟨j, hj, hjP, hPj, hcoord, hcenterj, hzero⟩ :=
    exists_prescribed_band_coordinates P F hFinj hFfront hcenter hwsmall hband
  let t : (V2 × ℝ) → ℝ := fun p => (j (F p)).2
  have hsmall : Q2 ×ˢ Icc (-w) w ⊆ Q2 ×ˢ I := fun p hp =>
    ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hFP : MapsTo F (Q2 ×ˢ Icc (-w) w)
      (P.map '' (D2 ×ˢ Icc (-1 : ℝ) 1)) := fun p hp =>
    image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self) (hband hp)
  have ht : ContinuousOn t (Q2 ×ˢ Icc (-w) w) :=
    continuous_snd.comp_continuousOn (hj.continuousOn.comp
      (hF.continuousOn.mono hsmall) hFP)
  have hrank : 1 < Module.rank ℝ V2 := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have hQ : IsPreconnected Q2 := isPreconnected_sphere hrank (0 : V2) 1
  have hpos : Q2 ×ˢ Ioc 0 w ⊆ Q2 ×ˢ Icc (-w) w := fun p hp =>
    ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hneg : Q2 ×ˢ Ico (-w) 0 ⊆ Q2 ×ˢ Icc (-w) w := fun p hp =>
    ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hpzero (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Ioc 0 w) : t p ≠ 0 := by
    intro he
    exact (ne_of_gt hp.2.1) ((hzero p (hpos hp)).mp he)
  have hnzero (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Ico (-w) 0) : t p ≠ 0 := by
    intro he
    exact (ne_of_lt hp.2.2) ((hzero p (hneg hp)).mp he)
  have hp := (hQ.prod isPreconnected_Ioc).mapsTo_Ioi_or_Iio (ht.mono hpos) hpzero
  have hn := (hQ.prod isPreconnected_Ico).mapsTo_Ioi_or_Iio (ht.mono hneg) hnzero
  obtain ⟨⟨p, hpw, hpv⟩, ⟨q, hqw, hqv⟩⟩ :=
    both_time_signs_in_prescribed_band P F hF hFinj hcenter hopen hw j hjP
  have hneq (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Icc (-w) w) (htp : t p ≠ 0) :
      p.2 ≠ 0 := fun he => htp ((hzero p hp).mpr he)
  refine ⟨j, hj, hjP, hPj, hcoord, hcenterj, ?_⟩
  rcases hp with hp | hp <;> rcases hn with hn | hn
  · exfalso
    rcases lt_or_gt_of_ne (hneq q hqw (ne_of_lt hqv)) with hqt | hqt
    · have h := hn ⟨hqw.1, hqw.2.1, hqt⟩
      exact (not_lt_of_ge (le_of_lt hqv)) h
    · have h := hp ⟨hqw.1, hqt, hqw.2.2⟩
      exact (not_lt_of_ge (le_of_lt hqv)) h
  · exact Or.inl ⟨fun _ h => hp h, fun _ h => hn h⟩
  · exact Or.inr ⟨fun _ h => hp h, fun _ h => hn h⟩
  · exfalso
    rcases lt_or_gt_of_ne (hneq p hpw (ne_of_gt hpv)) with hpt | hpt
    · have h := hn ⟨hpw.1, hpw.2.1, hpt⟩
      exact (not_lt_of_ge (le_of_lt hpv)) h
    · have h := hp ⟨hpw.1, hpt, hpw.2.2⟩
      exact (not_lt_of_ge (le_of_lt hpv)) h

end PoincareConjecture.M76.HamiltonIndexOne
