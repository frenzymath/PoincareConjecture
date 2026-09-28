import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ExtendedExcursion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

private theorem interval_image_complex {q : ℝ → P2}
    (hq : FinitePiecewiseAffineOn q (Icc 0 1)) (hi : InjOn q (Icc 0 1))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ T : SimplicialComplex ℝ P2, T.faces.Finite ∧ T.space = q '' Icc a b := by
  have hball : IsFinitePLBallPair ℝ (q '' Icc a b) {q a, q b} := by
    simpa only [image_pair] using (isFinitePLBallPair_Icc hab).image_of_subset hq
      (fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩) hi
  obtain ⟨_, C, _, _, _, e, ⟨f, ⟨T, hT, hTs, _⟩, _⟩, _⟩ := hball
  exact ⟨T, hT, hTs⟩

theorem exists_lower_tail_complex_and_distant_remainder
    {q : ℝ → P2} (hq : FinitePiecewiseAffineOn q (Icc 0 1))
    (hi : InjOn q (Icc 0 1)) {u v : ℝ} (huv : u < v)
    (hpositive : ∀ x ∈ Ioo u v, 0 < (q x).2)
    (hleft : ∃ a b m : ℝ, 0 ≤ a ∧ a < u ∧ u < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (q x).2 - 0 = m * (x - u))
    (hright : ∃ a b m : ℝ, 0 ≤ a ∧ a < v ∧ v < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
      ∀ x ∈ Icc a b, (q x).2 - 0 = m * (x - v))
    {B : Set P2} (hB : B ∩ (q '' Icc (0 : ℝ) 1) = q '' Icc u v) :
    ∃ (l t : ℝ) (T : SimplicialComplex ℝ P2) (E : Set P2),
      0 < l ∧ l < u ∧ v < t ∧ t < 1 ∧ T.faces.Finite ∧
      T.space = q '' Icc l u ∪ q '' Icc v t ∧
      (∀ x ∈ T.space, x.2 ≤ 0) ∧
      (∀ x ∈ T.space, x.2 = 0 → x = q u ∨ x = q v) ∧
      (∃ m n : ℝ, 0 < m ∧ n < 0 ∧
        (∀ s ∈ Icc l u, (q s).2 = m * (s - u)) ∧
        (∀ s ∈ Icc v t, (q s).2 = n * (s - v))) ∧
      IsCompact E ∧ Disjoint B E ∧
      E = q '' Icc 0 l ∪ q '' Icc t 1 ∧
      q '' (Icc (0 : ℝ) 1 \ Ioo u v) ⊆ T.space ∪ E := by
  obtain ⟨a₀, b₀, m, ha₀, hau, hub, hb₀, hm, hfm⟩ := hleft
  obtain ⟨a₁, b₁, n, ha₁, hav, hvb, hb₁, hn, hfn⟩ := hright
  have hδ : 0 < min (u - a₀) (b₁ - v) :=
    lt_min (sub_pos.mpr hau) (sub_pos.mpr hvb)
  obtain ⟨ε, l, t, hε, _, hl, hlu, hvt, ht, _, _, _, hnegL, hnegR, hcloseL, hcloseR⟩ :=
    exists_lower_level_extension_of_transverse_excursion huv hδ
      hpositive ⟨a₀, b₀, m, ha₀, hau, hub, hb₀, hm, hfm⟩
      ⟨a₁, b₁, n, ha₁, hav, hvb, hb₁, hn, hfn⟩
  have hal : a₀ < l := by have := min_le_left (u - a₀) (b₁ - v); linarith
  have htb : t < b₁ := by have := min_le_right (u - a₀) (b₁ - v); linarith
  have hmpos : 0 < m := by
    obtain ⟨x, hux, hx⟩ := exists_between (lt_min hub huv)
    have hp := hpositive x ⟨hux, (lt_min_iff.mp hx).2⟩
    have he := hfm x ⟨hau.le.trans hux.le, (lt_min_iff.mp hx).1.le⟩
    nlinarith
  have hnneg : n < 0 := by
    obtain ⟨x, hx, hxv⟩ := exists_between (max_lt hav huv)
    have hp := hpositive x ⟨(max_lt_iff.mp hx).2, hxv⟩
    have he := hfn x ⟨(max_lt_iff.mp hx).1.le, hxv.le.trans hvb.le⟩
    nlinarith
  have hu : 0 < u := hl.trans hlu
  have hv : v < 1 := hvt.trans ht
  have hqu : (q u).2 = 0 := by
    simpa using hfm u ⟨hau.le, hub.le⟩
  have hqv : (q v).2 = 0 := by
    simpa using hfn v ⟨hav.le, hvb.le⟩
  obtain ⟨L, hL, hLs⟩ := interval_image_complex hq hi hl.le hlu (huv.le.trans hv.le)
  obtain ⟨R, hR, hRs⟩ := interval_image_complex hq hi (hu.le.trans huv.le) hvt ht.le
  obtain ⟨T, hT, hTs⟩ := L.exists_finite_triangulation_union R hL hR
  rw [hLs, hRs] at hTs
  let E := q '' Icc 0 l ∪ q '' Icc t 1
  have hEc : IsCompact E :=
    (isCompact_Icc.image_of_continuousOn (hq.continuousOn.mono
      (fun x hx => ⟨hx.1, hx.2.trans (hlu.trans (huv.trans hv)).le⟩))).union
    (isCompact_Icc.image_of_continuousOn (hq.continuousOn.mono
      (fun x hx => ⟨(hu.trans (huv.trans hvt)).le.trans hx.1, hx.2⟩)))
  have hBE : Disjoint B E := by
    apply disjoint_left.mpr
    intro x hxB hxE
    rcases hxE with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (hlu.trans (huv.trans hv)).le⟩
      obtain ⟨y, hy, hys⟩ := hB.subset ⟨hxB, mem_image_of_mem q hsI⟩
      have he := hi ⟨hu.le.trans hy.1, hy.2.trans hv.le⟩ hsI hys
      linarith [hy.1, hs.2]
    · have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨(hu.trans (huv.trans hvt)).le.trans hs.1, hs.2⟩
      obtain ⟨y, hy, hys⟩ := hB.subset ⟨hxB, mem_image_of_mem q hsI⟩
      have he := hi ⟨hu.le.trans hy.1, hy.2.trans hv.le⟩ hsI hys
      linarith [hy.2, hs.1]
  refine ⟨l, t, T, E, hl, hlu, hvt, ht, hT, hTs, ?_, ?_, ?_, hEc, hBE, rfl, ?_⟩
  · intro x hx
    rw [hTs] at hx
    rcases hx with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · by_cases he : s = u
      · simp [he, hqu]
      · exact (hnegL s ⟨hs.1, lt_of_le_of_ne hs.2 he⟩).le
    · by_cases he : s = v
      · simp [he, hqv]
      · exact (hnegR s ⟨lt_of_le_of_ne hs.1 (Ne.symm he), hs.2⟩).le
  · intro x hx hz
    rw [hTs] at hx
    rcases hx with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · by_cases he : s = u
      · exact Or.inl (congrArg q he)
      · exact ((hnegL s ⟨hs.1, lt_of_le_of_ne hs.2 he⟩).ne hz).elim
    · by_cases he : s = v
      · exact Or.inr (congrArg q he)
      · exact ((hnegR s ⟨lt_of_le_of_ne hs.1 (Ne.symm he), hs.2⟩).ne hz).elim
  · exact ⟨m, n, hmpos, hnneg,
      fun s hs => by simpa using hfm s ⟨hal.le.trans hs.1, hs.2.trans hub.le⟩,
      fun s hs => by simpa using hfn s ⟨hav.le.trans hs.1, hs.2.trans htb.le⟩⟩
  · rintro x ⟨s, ⟨hs, hsout⟩, rfl⟩
    by_cases hsl : s ≤ l
    · exact Or.inr (Or.inl (mem_image_of_mem q ⟨hs.1, hsl⟩))
    by_cases hts : t ≤ s
    · exact Or.inr (Or.inr (mem_image_of_mem q ⟨hts, hs.2⟩))
    apply Or.inl
    rw [hTs]
    by_cases hsu : s ≤ u
    · exact Or.inl (mem_image_of_mem q ⟨le_of_lt (lt_of_not_ge hsl), hsu⟩)
    · exact Or.inr (mem_image_of_mem q ⟨le_of_not_gt (fun hsv =>
        hsout ⟨lt_of_not_ge hsu, hsv⟩), le_of_lt (lt_of_not_ge hts)⟩)

end PoincareConjecture.M76.Dehn
