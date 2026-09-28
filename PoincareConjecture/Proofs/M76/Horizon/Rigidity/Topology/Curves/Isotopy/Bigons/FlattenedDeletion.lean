import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.FlattenedTube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ContactDeletion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V" => (ℝ × ℝ)

private theorem finite_interval_image_complex {q : ℝ → V}
    (hq : FinitePiecewiseAffineOn q (Icc 0 1)) (hi : InjOn q (Icc 0 1))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ T : SimplicialComplex ℝ V, T.faces.Finite ∧ T.space = q '' Icc a b := by
  have hball : IsFinitePLBallPair ℝ (q '' Icc a b) {q a, q b} := by
    simpa only [image_pair] using (isFinitePLBallPair_Icc hab).image_of_subset hq
      (fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩) hi
  obtain ⟨_, C, _, _, _, e, ⟨f, ⟨T, hT, hTs, _⟩, _⟩, _⟩ := hball
  exact ⟨T, hT, hTs⟩

theorem exists_flattened_excursion_contact_deletion
    {r q : ℝ → V} (hr : FinitePiecewiseAffineOn r (Icc 0 1))
    (hq : FinitePiecewiseAffineOn q (Icc 0 1)) (hi : InjOn q (Icc 0 1))
    {L u v R : ℝ} (hL : 0 < L) (hLu : L < u) (huv : u < v)
    (hvR : v < R) (hR : R < 1)
    (hpositive : ∀ x ∈ Ioo u v, 0 < (r x).2)
    (hleft : ∃ a b m : ℝ, 0 ≤ a ∧ a < u ∧ u < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 = m * (x - u))
    (hright : ∃ a b m : ℝ, 0 ≤ a ∧ a < v ∧ v < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (r x).2 = m * (x - v))
    (hfixed : ∀ x ∈ Icc (0 : ℝ) 1 \ Ioo u v, q x = r x)
    (hflat : q '' Icc u v = segment ℝ (r u) (r v))
    {m n : ℝ} (hm : 0 < m) (hn : n < 0)
    (hmformula : ∀ x ∈ Icc L u, (r x).2 = m * (x - u))
    (hnformula : ∀ x ∈ Icc v R, (r x).2 = n * (x - v))
    {U E : Set V} (hU : IsOpen U) (hbaseU : segment ℝ (r u) (r v) ⊆ U)
    (hE : IsClosed E) (hbaseE : Disjoint (segment ℝ (r u) (r v)) E)
    (hfar : ∀ x ∈ Icc (0 : ℝ) 1 \ Ioo L R, r x ∈ E) :
    ∃ (D : Set V) (H : I → V ≃ₜ V) (F Fi : (ℝ × V) → V),
      IsFinitePLBallPair V D (frontier D) ∧ D ⊆ U ∧
      H 0 = Homeomorph.refl V ∧
      Continuous (fun z : I × V => H z.1 z.2) ∧
      Continuous (fun z : I × V => (H z.1).symm z.2) ∧
      (∀ s : I, ∀ x : V, x ∉ interior D → H s x = x) ∧
      (∀ s : I, ∀ x ∈ E, H s x = x) ∧
      {x ∈ Icc (0 : ℝ) 1 | (H 1 (q x)).2 = 0} =
        {x ∈ Icc (0 : ℝ) 1 | (r x).2 = 0} \ {u, v} ∧
      (∀ s : I, ∀ x : V, F ((s : ℝ), x) = H s x) ∧
      (∀ s : I, ∀ x : V, Fi ((s : ℝ), x) = (H s).symm x) ∧
      (∀ K : SimplicialComplex ℝ V, K.faces.Finite →
        FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ K.space)) ∧
      ∃ l t : ℝ, L < l ∧ l < u ∧ v < t ∧ t < R ∧
        (∀ s : I, ∀ x ∈ Icc (0 : ℝ) 1 \ Ioo l t, H s (q x) = q x) ∧
        ∀ x ∈ Icc (0 : ℝ) 1, (H 1 (q x)).2 = 0 →
          ∃ η : ℝ, 0 < η ∧ ∀ s : I, ∀ y ∈ Icc (0 : ℝ) 1,
            |y - x| < η → H s (q y) = r y := by
  let δ := min (u - L) (R - v)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hLu) (sub_pos.mpr hvR)
  obtain ⟨ε, l, t, C, hε, _, hl, hlu, hvt, ht, _, hC, hCU, _, hinto,
      _, _, hql, hqt, _, hpos, _, _, hcloseL, hcloseR⟩ :=
    exists_flattened_excursion_in_convex_tube_unordered hr hq hi huv hδ
      hpositive hleft hright hfixed hflat (hU.inter hE.isOpen_compl)
      (fun x hx => ⟨hbaseU hx, disjoint_left.mp hbaseE hx⟩)
  have hLl : L < l := by have := min_le_left (u - L) (R - v); dsimp [δ] at hcloseL; linarith
  have htR : t < R := by have := min_le_right (u - L) (R - v); dsimp [δ] at hcloseR; linarith
  have hlt : l < t := hlu.trans (huv.trans hvt)
  have huI : u ∈ Icc (0 : ℝ) 1 := ⟨(hL.trans hLu).le, (huv.trans (hvR.trans hR)).le⟩
  have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨(hL.trans (hLu.trans huv)).le, (hvR.trans hR).le⟩
  have hqleft (x : ℝ) (hx : x ∈ Icc L u) : q x = r x :=
    hfixed x ⟨⟨hL.le.trans hx.1, hx.2.trans huI.2⟩, fun hh => (not_lt_of_ge hx.2) hh.1⟩
  have hqright (x : ℝ) (hx : x ∈ Icc v R) : q x = r x :=
    hfixed x ⟨⟨hvI.1.trans hx.1, hx.2.trans hR.le⟩, fun hh => (not_lt_of_ge hx.1) hh.2⟩
  have hml : m * (l - u) = -ε := by
    rw [← hmformula l ⟨hLl.le, hlu.le⟩, ← hqleft l ⟨hLl.le, hlu.le⟩]
    exact hql
  have hnt : n * (t - v) = -ε := by
    rw [← hnformula t ⟨hvt.le, htR.le⟩, ← hqright t ⟨hvt.le, htR.le⟩]
    exact hqt
  obtain ⟨TL, hTL, hTLs⟩ := finite_interval_image_complex hq hi hL.le hLl (hlt.trans ht).le
  obtain ⟨TR, hTR, hTRs⟩ := finite_interval_image_complex hq hi (hl.trans hlt).le htR hR.le
  obtain ⟨T, hT, hTs⟩ := TL.exists_finite_triangulation_union TR hTL hTR
  rw [hTLs, hTRs] at hTs
  have hlow : ∀ x ∈ T.space, x.2 ≤ -ε := by
    intro x hx
    rw [hTs] at hx
    rcases hx with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · rw [hqleft s ⟨hs.1, hs.2.trans hlu.le⟩, hmformula s ⟨hs.1, hs.2.trans hlu.le⟩]
      nlinarith [hs.2]
    · rw [hqright s ⟨hvt.le.trans hs.1, hs.2⟩, hnformula s ⟨hvt.le.trans hs.1, hs.2⟩]
      nlinarith [hs.1]
  have haxisT : ∀ x ∈ T.space, x.2 = -ε → x = q l ∨ x = q t := by
    intro x hx hz
    rw [hTs] at hx
    rcases hx with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · rw [hqleft s ⟨hs.1, hs.2.trans hlu.le⟩, hmformula s ⟨hs.1, hs.2.trans hlu.le⟩] at hz
      have he : s = l := by nlinarith
      exact Or.inl (congrArg q he)
    · rw [hqright s ⟨hvt.le.trans hs.1, hs.2⟩, hnformula s ⟨hvt.le.trans hs.1, hs.2⟩] at hz
      have he : s = t := by nlinarith
      exact Or.inr (congrArg q he)
  have hresidual : ∀ x ∈ Icc (0 : ℝ) 1 \ Icc l t, q x ∈ T.space ∪ E := by
    intro x hx
    by_cases hfarx : x ∉ Ioo L R
    · apply Or.inr
      rw [hfixed x ⟨hx.1, fun hh => hfarx ⟨hLu.trans hh.1, hh.2.trans hvR⟩⟩]
      exact hfar x ⟨hx.1, hfarx⟩
    · have hnear : x ∈ Ioo L R := not_not.mp hfarx
      apply Or.inl
      rw [hTs]
      by_cases hxl : x < l
      · exact Or.inl (mem_image_of_mem q ⟨hnear.1.le, hxl.le⟩)
      · exact Or.inr (mem_image_of_mem q ⟨(lt_of_not_ge (fun hxt => hx.2 ⟨le_of_not_gt hxl, hxt⟩)).le,
          hnear.2.le⟩)
  obtain ⟨D, H, F, Fi, hD, hDU, hzero, hcont, hconti, hfix, hres, _, hdelete,
      hF, hFi, hPL⟩ := exists_axis_contact_deleting_motion hq hi hl.le hlt ht.le
    (neg_neg_of_pos hε) hql hqt hpos hC hinto hU
    (fun x hx => (hCU hx).1) hE
    (disjoint_left.mpr (fun x hx hxE => (hCU hx).2 hxE)) T hT hlow haxisT hresidual
  have houtside (s : I) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1 \ Ioo l t) :
      H s (q x) = q x := by
    apply hres s (q x)
    by_cases he : x = l
    · apply Or.inl
      rw [he, hTs]
      exact Or.inl (mem_image_of_mem q ⟨hLl.le, le_rfl⟩)
    by_cases he' : x = t
    · apply Or.inl
      rw [he', hTs]
      exact Or.inr (mem_image_of_mem q ⟨le_rfl, htR.le⟩)
    exact hresidual x ⟨hx.1, fun hh => hx.2
      ⟨lt_of_le_of_ne hh.1 (Ne.symm he), lt_of_le_of_ne hh.2 he'⟩⟩
  have hlocal (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hz : (H 1 (q x)).2 = 0) :
      ∃ η : ℝ, 0 < η ∧ ∀ s : I, ∀ y ∈ Icc (0 : ℝ) 1,
        |y - x| < η → H s (q y) = r y := by
    have hout : x ∉ Icc l t := (hdelete.subset ⟨hx, hz⟩).2
    by_cases hxl : x < l
    · refine ⟨(l - x) / 2, by linarith, ?_⟩
      intro s y hy hdist
      have hyl : y < l := by have := (abs_lt.mp hdist).2; linarith
      rw [houtside s y ⟨hy, fun hh => (not_lt_of_ge hyl.le) hh.1⟩]
      exact hfixed y ⟨hy, fun hh => (not_lt_of_ge (hyl.trans hlu).le) hh.1⟩
    · have htx : t < x := lt_of_not_ge (fun hxt => hout ⟨le_of_not_gt hxl, hxt⟩)
      refine ⟨(x - t) / 2, by linarith, ?_⟩
      intro s y hy hdist
      have hty : t < y := by have := (abs_lt.mp hdist).1; linarith
      rw [houtside s y ⟨hy, fun hh => (not_lt_of_ge hty.le) hh.2⟩]
      exact hfixed y ⟨hy, fun hh => (not_lt_of_ge (hvt.trans hty).le) hh.2⟩
  refine ⟨D, H, F, Fi, hD, hDU, hzero, hcont, hconti, hfix,
    (fun s x hx => hres s x (Or.inr hx)), ?_, hF, hFi, hPL,
    l, t, hLl, hlu, hvt, htR, houtside, hlocal⟩
  rw [hdelete]
  ext x
  constructor
  · rintro ⟨⟨hx, hxzero⟩, hout⟩
    have houtuv : x ∉ Ioo u v := fun hh => hout ⟨hlu.le.trans hh.1.le, hh.2.le.trans hvt.le⟩
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · rwa [hfixed x ⟨hx, houtuv⟩] at hxzero
    · rintro (rfl | rfl)
      · exact hout ⟨hlu.le, (huv.trans hvt).le⟩
      · exact hout ⟨(hlu.trans huv).le, hvt.le⟩
  · rintro ⟨⟨hx, hxzero⟩, hends⟩
    have houtuv : x ∉ Ioo u v := fun hh => (hpositive x hh).ne' hxzero
    refine ⟨⟨hx, by rw [hfixed x ⟨hx, houtuv⟩]; exact hxzero⟩, ?_⟩
    intro hxin
    by_cases hxu : x ≤ u
    · have he := hmformula x ⟨hLl.le.trans hxin.1, hxu⟩
      have hxe : x = u := by rw [hxzero] at he; nlinarith
      exact hends (Or.inl hxe)
    · have hvx : v ≤ x := le_of_not_gt (fun hxv => houtuv ⟨lt_of_not_ge hxu, hxv⟩)
      have he := hnformula x ⟨hvx, hxin.2.trans htR.le⟩
      have hxe : x = v := by rw [hxzero] at he; nlinarith
      exact hends (Or.inr hxe)

end PoincareConjecture.M76.Dehn
