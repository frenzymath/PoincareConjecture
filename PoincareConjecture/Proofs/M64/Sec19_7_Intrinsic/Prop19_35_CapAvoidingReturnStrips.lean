import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ObstacleStripChain

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_cap_avoiding_return_strips
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U) :
    ∃ (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : ℝ)
      (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : Set AnnulusCoordinates) (positive : Bool) (d : ℝ → AnnulusCoordinates),
      let C := ⋃ i : Bool × Bool,
        ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
          F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
      0 < r ∧ r ≤ T / 3 ∧ H 0 = gamma 0 ∧
      (∀ s : ℝ, H (s, 0) = gamma s) ∧
      (∀ s : ℝ, H (0, s) = gamma (T - s)) ∧
      (∀ i,
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source ∧
        (F i).target ⊆ H.target ∧
        ContDiffOn ℝ ∞ (F i) (F i).source ∧
        ContDiffOn ℝ ∞ (F i).symm (F i).target ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0))) ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (0, s) = H (sectorParameterEquiv 0 i (0, s))) ∧
        (∀ t : ℝ, F i ((1 - t) * r, t * r) =
          (1 - t) • F i (r, 0) + t • F i (0, r)) ∧
        F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
          H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
            {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2})) ∧
      IsOpen W ∧ gamma 0 ∈ W ∧ IsCompact C ∧ C ⊆ closure U ∧ W ∩ closure U ⊆ C ∧
      C ∩ gamma '' Icc 0 T = gamma '' Icc 0 r ∪ gamma '' Icc (T - r) T ∧
      (∀ t ∈ Icc r (T - r), 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t)) ∧
      (∀ z ∈ Icc (0 : ℝ) 1,
        gamma r + z • d r ∈ C ∧ gamma (T - r) + z • d (T - r) ∈ C) ∧
      ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
        (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ)
        (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (G i).target)
        (P : ∀ i, TransverseGraphCuts (f i) (G i (c i.castSucc)) (G i (c i.succ))
          (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
          (L i (d (c i.succ))).1 (L i (d (c i.succ))).2),
        let S (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
        ∃ delta > 0, 0 < n ∧ StrictMono c ∧ c 0 = r ∧ c (Fin.last n) = T - r ∧
          (∀ i, Icc (c i.castSucc) (c i.succ) ⊆ (G i).source ∧
            StrictMonoOn (G i) (G i).source ∧ ContDiffOn ℝ ∞ (G i) (G i).source ∧
            (∀ t ∈ (G i).source, L i (gamma t) = (G i t, f i (G i t))) ∧
            G i '' Icc (c i.castSucc) (c i.succ) =
              Icc (G i (c i.castSucc)) (G i (c i.succ)) ∧
            Icc (G i (c i.castSucc)) (G i (c i.succ)) ⊆ (G i).target) ∧
          (∀ i, delta ≤ (P i).radius ∧
            Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ (S i).source ∧
            (fun t => S i (t, 0)) '' Icc (0 : ℝ) 1 =
              gamma '' Icc (c i.castSucc) (c i.succ)) ∧
          (∀ i j : Fin n, i.succ < j.castSucc →
            Disjoint (S i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta))
              (S j '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta))) ∧
          (∀ i j : Fin n, i.succ = j.castSucc →
            ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
            ∀ z w : ℝ, |z| < delta → |w| < delta →
              S i (t, z) = S j (s, w) → t = 1 ∧ s = 0) ∧
          ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < delta → S i (t, z) ∈ C →
            (c i.castSucc = r ∧ t = 0) ∨ (c i.succ = T - r ∧ t = 1) := by
  classical
  obtain ⟨H, r, F, W, positive, hr, hrbound, hbase, haxis, haxis', hF,
    hW, hpW, hsub, hcover, hcontact⟩ :=
    m64Intrinsic_exists_loop_caps_with_exact_contacts hg hT hend hinj hind hU hV hdisj hfU hfV
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let C := ⋃ i : Bool × Bool, ⋃ (_ : occupied i),
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  have hcompact : IsCompact C := by
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro _
    exact m64Intrinsic_cap_isCompact (F i) (hF i).1
  have hrT : r < T := by linarith
  have hmiddle : r < T - r := by linarith
  have hcapSub (i : Bool × Bool) (hi : occupied i) :
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ C :=
    fun _ hz => mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hz⟩⟩
  have hleftSub := hcapSub (true, positive) (by cases positive <;> simp [occupied])
  have hrightSub := hcapSub (positive, true) (by cases positive <;> simp [occupied])
  have hleftAxis : ∀ s ∈ Icc (0 : ℝ) r, F (true, positive) (s, 0) = gamma s := by
    intro s hs
    simpa [sectorParameterEquiv_apply, haxis] using (hF (true, positive)).2.2.2.2.1 s hs
  have hrightAxis : ∀ s ∈ Icc (0 : ℝ) r, F (positive, true) (0, s) = gamma (T - s) := by
    intro s hs
    simpa [sectorParameterEquiv_apply, haxis'] using (hF (positive, true)).2.2.2.2.2.1 s hs
  let dl := F (true, positive) (0, r) - F (true, positive) (r, 0)
  let dr := F (positive, true) (r, 0) - F (positive, true) (0, r)
  have hdl : 0 < inner ℝ (quarterTurn (deriv gamma r)) dl :=
    m64Intrinsic_cap_endpoint_chord_sign hg hend hinj hregular hU hV hdisj hfU hfV hray
      hr hrT (F (true, positive)) (hF _).1 (hF _).2.2.1 (hF _).2.2.2.1
      (hF _).2.2.2.2.2.2.1 (hleftSub.trans hsub) false false hleftAxis
  have hdr : 0 < inner ℝ (quarterTurn (deriv gamma (T - r))) dr :=
    m64Intrinsic_cap_endpoint_chord_sign hg hend hinj hregular hU hV hdisj hfU hfV hray
      hr hrT (F (positive, true)) (hF _).1 (hF _).2.2.1 (hF _).2.2.2.1
      (hF _).2.2.2.2.2.2.1 (hrightSub.trans hsub) true true hrightAxis
  let d : ℝ → AnnulusCoordinates := fun t =>
    if t = r then dl else if t = T - r then dr else quarterTurn (deriv gamma t)
  have hda : d r = dl := by simp [d]
  have hdb : d (T - r) = dr := by simp [d, ne_of_gt hmiddle]
  have hd : ∀ t ∈ Icc r (T - r), 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t) := by
    intro t ht
    by_cases hta : t = r
    · simpa only [hta, hda] using hdl
    by_cases htb : t = T - r
    · simpa only [htb, hdb] using hdr
    have hreg := hregular t ⟨hr.trans_le ht.1, ht.2.trans_lt (sub_lt_self T hr)⟩
    have hrot : quarterTurn (deriv gamma t) ≠ 0 := by
      intro hz
      exact hreg (quarterTurn.injective (by simpa only [map_zero] using hz))
    simpa only [d, if_neg hta, if_neg htb] using real_inner_self_pos.mpr hrot
  have hpaths : ∀ z ∈ Icc (0 : ℝ) 1,
      gamma r + z • d r ∈ C ∧ gamma (T - r) + z • d (T - r) ∈ C := by
    intro z hz
    constructor
    · apply hleftSub
      refine ⟨((1 - z) * r, z * r),
        ⟨mul_nonneg (sub_nonneg.mpr hz.2) hr.le, mul_nonneg hz.1 hr.le, by dsimp; nlinarith⟩, ?_⟩
      rw [(hF _).2.2.2.2.2.2.1, hda, ← hleftAxis r ⟨hr.le, le_rfl⟩]
      dsimp [dl]
      module
    · apply hrightSub
      refine ⟨((1 - (1 - z)) * r, (1 - z) * r),
        ⟨by nlinarith [mul_nonneg hz.1 hr.le],
          mul_nonneg (sub_nonneg.mpr hz.2) hr.le, by dsimp; nlinarith⟩, ?_⟩
      rw [(hF _).2.2.2.2.2.2.1, hdb, ← hrightAxis r ⟨hr.le, le_rfl⟩]
      dsimp [dr]
      module
  obtain ⟨ellA, WA, hWA, haW, hnA, hkA, hsA⟩ :=
    m64Intrinsic_exists_loop_cap_union_separator hg hr hrT hinj H hbase haxis haxis' F
      (fun i => (hF i).1) (fun i => (hF i).2.2.1) (fun i => (hF i).2.2.2.1)
      (fun i => (hF i).2.2.2.2.1) (fun i => (hF i).2.2.2.2.2.1)
      (fun i => (hF i).2.2.2.2.2.2.1) (fun i => (hF i).2.2.2.2.2.2.2) positive false
  obtain ⟨ellB, WB, hWB, hbW, hnB, hkB, hsB⟩ :=
    m64Intrinsic_exists_loop_cap_union_separator hg hr hrT hinj H hbase haxis haxis' F
      (fun i => (hF i).1) (fun i => (hF i).2.2.1) (fun i => (hF i).2.2.2.1)
      (fun i => (hF i).2.2.2.2.1) (fun i => (hF i).2.2.2.2.2.1)
      (fun i => (hF i).2.2.2.2.2.2.1) (fun i => (hF i).2.2.2.2.2.2.2) positive true
  change ellA (deriv gamma r) = 1 at hnA
  change ellB (deriv gamma (T - r)) = -1 at hnB
  change ellA dl = 0 at hkA
  change ellB dr = 0 at hkB
  have hI : Icc r (T - r) ⊆ Ico (0 : ℝ) T :=
    fun _ ht => ⟨hr.le.trans ht.1, ht.2.trans_lt (sub_lt_self T hr)⟩
  have havoids : ∀ t ∈ Ioo r (T - r), gamma t ∉ C :=
    m64Intrinsic_trimmed_arc_avoids_caps hr hrT hend hinj (subset_of_eq hcontact)
  have hchain := m64Intrinsic_exists_obstacle_avoiding_strip_chain hg hmiddle (hinj.mono hI)
    (fun t ht => hregular t ⟨hr.trans_le ht.1, ht.2.trans_lt (sub_lt_self T hr)⟩)
    d hd hcompact.isClosed havoids ellA ellB
    (by simpa only [hda] using hkA) (by simpa only [hdb] using hkB)
    (by rw [hnA]; norm_num) (by rw [hnB]; norm_num) hWA hWB haW hbW
    (fun z hz => hsA z ⟨hz.2, hz.1⟩) (fun z hz => hsB z ⟨hz.2, hz.1⟩)
  exact ⟨H, r, F, W, positive, d, hr, hrbound, hbase, haxis, haxis', hF,
    hW, hpW, hcompact, hsub, hcover, hcontact, hd, hpaths, hchain⟩

end PoincareConjecture
