import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ShiftedMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ShiftedDisk

set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

theorem exists_axis_contact_deleting_motion
    {q : ℝ → V} (hq : FinitePiecewiseAffineOn q (Icc (0 : ℝ) 1))
    (hi : InjOn q (Icc (0 : ℝ) 1))
    {l t c : ℝ} (hl : 0 ≤ l) (hlt : l < t) (ht : t ≤ 1) (hc : c < 0)
    (hql : (q l).2 = c) (hqt : (q t).2 = c)
    (hpos : ∀ x ∈ Ioo l t, c < (q x).2)
    {C U E : Set V} (hC : Convex ℝ C) (hinto : q '' Icc l t ⊆ C)
    (hU : IsOpen U) (hCU : C ⊆ U) (hE : IsClosed E) (hCE : Disjoint C E)
    (T : SimplicialComplex ℝ V) (hT : T.faces.Finite)
    (hlower : ∀ x ∈ T.space, x.2 ≤ c)
    (haxisT : ∀ x ∈ T.space, x.2 = c → x = q l ∨ x = q t)
    (hresidual : ∀ x ∈ Icc (0 : ℝ) 1 \ Icc l t, q x ∈ T.space ∪ E) :
    ∃ (D : Set V) (H : I → V ≃ₜ V) (F Fi : (ℝ × V) → V),
      IsFinitePLBallPair V D (frontier D) ∧ D ⊆ U ∧
      H 0 = Homeomorph.refl V ∧
      Continuous (fun z : I × V => H z.1 z.2) ∧
      Continuous (fun z : I × V => (H z.1).symm z.2) ∧
      (∀ s : I, ∀ x : V, x ∉ interior D → H s x = x) ∧
      (∀ s : I, ∀ x ∈ T.space ∪ E, H s x = x) ∧
      H 1 '' (q '' Icc l t) = segment ℝ (q l) (q t) ∧
      {x ∈ Icc (0 : ℝ) 1 | (H 1 (q x)).2 = 0} =
        {x ∈ Icc (0 : ℝ) 1 | (q x).2 = 0} \ Icc l t ∧
      (∀ s : I, ∀ x : V, F ((s : ℝ), x) = H s x) ∧
      (∀ s : I, ∀ x : V, Fi ((s : ℝ), x) = (H s).symm x) ∧
      ∀ K : SimplicialComplex ℝ V, K.faces.Finite →
        FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ K.space) := by
  have hsub : Icc l t ⊆ Icc (0 : ℝ) 1 :=
    fun x hx => ⟨hl.trans hx.1, hx.2.trans ht⟩
  have hpair : IsFinitePLBallPair ℝ (q '' Icc l t) {q l, q t} := by
    simpa only [image_pair] using (isFinitePLBallPair_Icc hlt).image_of_subset hq hsub hi
  have hne : q l ≠ q t := fun h => hlt.ne (hi (hsub ⟨le_rfl, hlt.le⟩)
    (hsub ⟨hlt.le, le_rfl⟩) h)
  have hge (x : ℝ) (hx : x ∈ Icc l t) : c ≤ (q x).2 := by
    rcases hx.1.eq_or_lt with h | h
    · simp only [← h, hql, le_refl]
    rcases hx.2.eq_or_lt with he | he
    · simp only [he, hqt, le_refl]
    exact (hpos x ⟨h, he⟩).le
  have haxis : (q '' Icc l t) ∩ {x : V | x.2 = c} = {q l, q t} := by
    apply Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, hsc⟩
      by_cases hsl : s = l
      · simp [hsl]
      by_cases hst : s = t
      · simp [hst]
      exact (not_lt_of_ge (le_of_eq hsc)
        (hpos s ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hst⟩)).elim
    · rintro x (rfl | rfl)
      · exact ⟨mem_image_of_mem q ⟨le_rfl, hlt.le⟩, hql⟩
      · exact ⟨mem_image_of_mem q ⟨hlt.le, le_rfl⟩, hqt⟩
  obtain ⟨B, hB, _, hBC, _⟩ := exists_finitePL_returning_disk_above_level hpair hne
    (by rintro _ ⟨x, hx, rfl⟩; exact hge x hx) haxis hC hinto
  obtain ⟨D, H, F, Fi, hD, hDU, hzero, hcont, hconti, hfixed, hres, hend,
      hF, hFi, hPL⟩ := exists_returning_arc_motion_fixing_residual_at_level
    hpair hne hql hqt (by rintro _ ⟨x, hx, rfl⟩; exact hge x hx) haxis
    (by simpa only [union_comm] using hB) hU (hBC.trans hCU) hE
    (hCE.mono_left hBC) T hT hlower haxisT
  have hnegative (x : ℝ) (hx : x ∈ Icc l t) : (H 1 (q x)).2 = c := by
    have hm := hend.subset (mem_image_of_mem (H 1) (mem_image_of_mem q hx))
    have hconv : Convex ℝ {x : V | x.2 = c} :=
      (convex_singleton c).linear_preimage (LinearMap.snd ℝ ℝ ℝ)
    exact hconv.segment_subset hql hqt hm
  refine ⟨D, H, F, Fi, hD, hDU, hzero, hcont, hconti, hfixed, hres, hend,
    ?_, hF, hFi, hPL⟩
  ext x
  constructor
  · rintro ⟨hx, hxzero⟩
    have hout : x ∉ Icc l t := fun hh => hc.ne ((hnegative x hh).symm.trans hxzero)
    refine ⟨⟨hx, ?_⟩, hout⟩
    rwa [hres 1 (q x) (hresidual x ⟨hx, hout⟩)] at hxzero
  · rintro ⟨⟨hx, hxzero⟩, hout⟩
    exact ⟨hx, (congrArg Prod.snd (hres 1 (q x) (hresidual x ⟨hx, hout⟩))).trans hxzero⟩

theorem axis_contact_count_decreases_of_transverse_deletion
    {r f : ℝ → V} {u v : ℝ} (huv : u < v)
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | (r x).2 = 0}.Finite)
    (hleft : ∃ a b m : ℝ, 0 ≤ a ∧ a < u ∧ u < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 = m * (x - u))
    (hright : ∃ a b m : ℝ, 0 ≤ a ∧ a < v ∧ v < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 = m * (x - v))
    (hdelete : {x ∈ Icc (0 : ℝ) 1 | (f x).2 = 0} =
      {x ∈ Icc (0 : ℝ) 1 | (r x).2 = 0} \ {u, v}) :
    {x ∈ Icc (0 : ℝ) 1 | (f x).2 = 0}.ncard + 2 =
      {x ∈ Icc (0 : ℝ) 1 | (r x).2 = 0}.ncard ∧
    {x ∈ Icc (0 : ℝ) 1 | (f x).2 = 0}.ncard <
      {x ∈ Icc (0 : ℝ) 1 | (r x).2 = 0}.ncard := by
  obtain ⟨a, b, m, ha, hau, hub, hb, _, hmu⟩ := hleft
  obtain ⟨a', b', n, ha', hav, hvb, hb', _, hnv⟩ := hright
  have hu : u ∈ {x ∈ Icc (0 : ℝ) 1 | (r x).2 = 0} := by
    refine ⟨⟨ha.trans hau.le, hub.le.trans hb⟩, ?_⟩
    simpa using hmu u ⟨hau.le, hub.le⟩
  have hv : v ∈ {x ∈ Icc (0 : ℝ) 1 | (r x).2 = 0} := by
    refine ⟨⟨ha'.trans hav.le, hvb.le.trans hb'⟩, ?_⟩
    simpa using hnv v ⟨hav.le, hvb.le⟩
  have hsub : ({u, v} : Set ℝ) ⊆ {x ∈ Icc (0 : ℝ) 1 | (r x).2 = 0} := by
    rintro x (rfl | rfl)
    · exact hu
    · exact hv
  have he := ncard_sdiff_add_ncard_of_subset hsub hfinite
  rw [ncard_pair huv.ne, ← hdelete] at he
  exact ⟨he, by omega⟩

theorem transverse_axis_germs_of_contact_deletion
    {r f : ℝ → V}
    (hsub : {x ∈ Icc (0 : ℝ) 1 | (f x).2 = 0} ⊆
      {x ∈ Icc (0 : ℝ) 1 | (r x).2 = 0})
    (hregular : ∀ x ∈ Icc (0 : ℝ) 1, (r x).2 = 0 →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).2 = m * (y - x))
    (hlocal : ∀ x ∈ Icc (0 : ℝ) 1, (f x).2 = 0 →
      ∃ η : ℝ, 0 < η ∧ ∀ y ∈ Icc (0 : ℝ) 1, |y - x| < η → f y = r y) :
    ∀ x ∈ Icc (0 : ℝ) 1, (f x).2 = 0 →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (f y).2 = m * (y - x) := by
  intro x hx hz
  obtain ⟨a, b, m, ha, hax, hxb, hb, hm, hformula⟩ := hregular x hx (hsub ⟨hx, hz⟩).2
  obtain ⟨η, hη, heq⟩ := hlocal x hx hz
  refine ⟨max a (x - η / 2), min b (x + η / 2), m,
    ha.trans (le_max_left _ _), max_lt hax (by linarith),
    lt_min hxb (by linarith), (min_le_left _ _).trans hb, hm, ?_⟩
  intro y hy
  have hya : a ≤ y := (le_max_left _ _).trans hy.1
  have hyb : y ≤ b := hy.2.trans (min_le_left _ _)
  rw [heq y ⟨ha.trans hya, hyb.trans hb⟩ ?_]
  · exact hformula y ⟨hya, hyb⟩
  · apply abs_lt.mpr
    have hlo := (le_max_right a (x - η / 2)).trans hy.1
    have hhi := hy.2.trans (min_le_right b (x + η / 2))
    constructor <;> linarith

end PoincareConjecture.M76.Dehn
