import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcCornerContacts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcCapChordSign
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ObstacleStripChain

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_two_corner_arc_strips
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ}
    (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U)
    (r : Bool → ℝ) (hr : ∀ e, 0 < r e) (hrbound : ∀ e, r e ≤ T / 3)
    (H : Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (positive vertical : Bool → Bool)
    (hsource : ∀ e i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆ (F e i).source)
    (hF : ∀ e i, ContDiffOn ℝ ∞ (F e i) (F e i).source)
    (hFi : ∀ e i, ContDiffOn ℝ ∞ (F e i).symm (F e i).target)
    (hfirst : ∀ e i, ∀ s ∈ Icc (0 : ℝ) (r e),
      F e i (s, 0) = H e (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ e i, ∀ s ∈ Icc (0 : ℝ) (r e),
      F e i (0, s) = H e (sectorParameterEquiv 0 i (0, s)))
    (hchord : ∀ e i, ∀ t : ℝ, F e i ((1 - t) * r e, t * r e) =
      (1 - t) • F e i (r e, 0) + t • F e i (0, r e))
    (hsector : ∀ e i,
      F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆
        H e '' ((H e).source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxis : ∀ e : Bool, ∀ s : ℝ,
      H e (if vertical e then (0, s) else (s, 0)) = gamma (if e then T - s else s))
    (htip : ∀ e : Bool,
      (if vertical e then ((0 : ℝ), r e) else (r e, 0)) ∈ (H e).source) :
    let C (e : Bool) := ⋃ i,
      ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
    (∀ e, C e ⊆ closure U) → Disjoint (C false) (C true) →
    (∀ e : Bool, C e ∩ frontier U ⊆
      (fun s => gamma (if e then T - s else s)) '' Icc 0 (r e) ∪ K) →
    ∃ d : ℝ → AnnulusCoordinates,
      (∀ t ∈ Icc (r false) (T - r true),
        0 < inner ℝ (quarterTurn (deriv gamma t)) (d t)) ∧
      (∀ e : Bool, ∀ z ∈ Icc (0 : ℝ) 1,
        gamma (if e then T - r e else r e) +
          z • d (if e then T - r e else r e) ∈ C e) ∧
      ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
        (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ)
        (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (G i).target)
        (P : ∀ i, TransverseGraphCuts (f i) (G i (c i.castSucc)) (G i (c i.succ))
          (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
          (L i (d (c i.succ))).1 (L i (d (c i.succ))).2),
        let S (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
        ∃ delta > 0, 0 < n ∧ StrictMono c ∧ c 0 = r false ∧
          c (Fin.last n) = T - r true ∧
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
          ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < delta →
            S i (t, z) ∈ C false ∪ C true →
              (c i.castSucc = r false ∧ t = 0) ∨ (c i.succ = T - r true ∧ t = 1) := by
  classical
  intro C hsub hCC hcontact
  have hT : 0 < T := by linarith [hr false, hrbound false]
  have hrT (e : Bool) : r e < T := by linarith [hrbound e]
  have hmiddle : r false < T - r true := by linarith [hrbound false, hrbound true]
  let selected (e : Bool) :=
    if vertical e then (positive e, true) else (true, positive e)
  let v (e : Bool) :=
    if vertical e then F e (selected e) (r e, 0) - F e (selected e) (0, r e)
    else F e (selected e) (0, r e) - F e (selected e) (r e, 0)
  have hselected (e : Bool) :
      if positive e then selected e = (true, true) else selected e ≠ (true, true) := by
    cases hv : vertical e <;> cases hp : positive e <;> simp [selected, hv, hp]
  have hcapSub (e : Bool) :
      F e (selected e) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆ C e :=
    fun _ hz => mem_iUnion.mpr ⟨selected e, mem_iUnion.mpr ⟨hselected e, hz⟩⟩
  have hselectedAxis (e : Bool) : ∀ s ∈ Icc (0 : ℝ) (r e),
      F e (selected e) (if vertical e then (0, s) else (s, 0)) =
        gamma (if e then T - s else s) := by
    intro s hs
    cases hv : vertical e
    · calc
        F e (selected e) (s, 0) = H e (s, 0) := by
          simpa [selected, hv, sectorParameterEquiv_apply] using
            hfirst e (true, positive e) s hs
        _ = gamma (if e then T - s else s) := by simpa [hv] using haxis e s
    · calc
        F e (selected e) (0, s) = H e (0, s) := by
          simpa [selected, hv, sectorParameterEquiv_apply] using
            hsecond e (positive e, true) s hs
        _ = gamma (if e then T - s else s) := by simpa only [hv, if_true] using haxis e s
  have hvpos (e : Bool) :
      0 < inner ℝ (quarterTurn (deriv gamma (if e then T - r e else r e))) (v e) :=
    m64Intrinsic_arc_cap_endpoint_chord_sign hg hinj hregular hK havoid hU hV hdisj
      hfU hfV hray (hr e) (hrT e) (F e (selected e)) (hsource e _) (hF e _) (hFi e _)
      (hchord e _) ((hcapSub e).trans (hsub e)) e (vertical e) (hselectedAxis e)
  let d : ℝ → AnnulusCoordinates := fun t =>
    if t = r false then v false else if t = T - r true then v true
    else quarterTurn (deriv gamma t)
  have hde (e : Bool) : d (if e then T - r e else r e) = v e := by
    cases e <;> simp [d, ne_of_gt hmiddle]
  have hda : d (r false) = v false := hde false
  have hdb : d (T - r true) = v true := hde true
  have hd : ∀ t ∈ Icc (r false) (T - r true),
      0 < inner ℝ (quarterTurn (deriv gamma t)) (d t) := by
    intro t ht
    by_cases hl : t = r false
    · simpa only [hl, hda, Bool.false_eq_true, if_false] using hvpos false
    by_cases hh : t = T - r true
    · simpa only [hh, hdb, if_true] using hvpos true
    have hreg := hregular t ⟨(hr false).trans_le ht.1,
      ht.2.trans_lt (sub_lt_self T (hr true))⟩
    have hrot : quarterTurn (deriv gamma t) ≠ 0 := by
      intro hz
      exact hreg (quarterTurn.injective (by simpa only [map_zero] using hz))
    simpa only [d, if_neg hl, if_neg hh] using real_inner_self_pos.mpr hrot
  have hpaths (e : Bool) (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      gamma (if e then T - r e else r e) +
        z • d (if e then T - r e else r e) ∈ C e := by
    rw [hde]
    apply hcapSub e
    cases hv : vertical e
    · refine ⟨((1 - z) * r e, z * r e),
        ⟨mul_nonneg (sub_nonneg.mpr hz.2) (hr e).le,
          mul_nonneg hz.1 (hr e).le, by dsimp; nlinarith⟩, ?_⟩
      rw [hchord]
      have hbase := hselectedAxis e (r e) ⟨(hr e).le, le_rfl⟩
      simp only [hv, Bool.false_eq_true, if_false] at hbase
      rw [← hbase]
      simp only [v, hv, Bool.false_eq_true, if_false]
      module
    · refine ⟨(z * r e, (1 - z) * r e),
        ⟨mul_nonneg hz.1 (hr e).le,
          mul_nonneg (sub_nonneg.mpr hz.2) (hr e).le, by dsimp; nlinarith⟩, ?_⟩
      have hc := hchord e (selected e) (1 - z)
      simp only [sub_sub_cancel] at hc
      rw [hc]
      have hbase := hselectedAxis e (r e) ⟨(hr e).le, le_rfl⟩
      simp only [hv, if_true] at hbase
      rw [← hbase]
      simp only [v, hv, if_true]
      module
  have hcompact (e : Bool) : IsCompact (C e) := by
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro _
    exact m64Intrinsic_cap_isCompact (F e i) (hsource e i)
  have hbarrier (e : Bool) := m64Intrinsic_exists_two_arc_cap_union_separator
    hg (hr e) (H e) (F e) (hsource e) (hF e) (hFi e) (hfirst e) (hsecond e)
      (hchord e) (hsector e) (positive e) e (vertical e) (haxis e) (htip e)
  choose ell W hW hpW htangent hkernel hsep using hbarrier
  have hbaseC (e : Bool) : gamma (if e then T - r e else r e) ∈ C e := by
    simpa only [zero_smul, add_zero] using hpaths e 0 (by simp)
  obtain ⟨W0, hW0, hpW0, hsep0⟩ := m64Intrinsic_corner_separator_union
    (hcompact true).isClosed hCC (hbaseC false) (hW false) (hpW false) (ell false) (hsep false)
  obtain ⟨W1, hW1, hpW1, hsep1⟩ := m64Intrinsic_corner_separator_union
    (hcompact false).isClosed hCC.symm (hbaseC true) (hW true) (hpW true) (ell true) (hsep true)
  have hkernel' (e : Bool) : ell e (d (if e then T - r e else r e)) = 0 := by
    rw [hde]
    exact hkernel e
  refine ⟨d, hd, hpaths, ?_⟩
  apply m64Intrinsic_exists_obstacle_avoiding_strip_chain hg hmiddle
    (hinj.mono (Icc_subset_Icc (hr false).le (sub_le_self T (hr true).le)))
    (fun t ht => hregular t ⟨(hr false).trans_le ht.1,
      ht.2.trans_lt (sub_lt_self T (hr true))⟩) d hd
    ((hcompact false).union (hcompact true)).isClosed
    (m64Intrinsic_arc_trim_avoids_two_caps hinj r hr (fun e => (hrT e).le)
      C hfU havoid hcontact) (ell false) (ell true)
    (hkernel' false) (hkernel' true)
    (by have ht : ell false (deriv gamma (r false)) = 1 := htangent false; linarith)
    (by have ht : ell true (deriv gamma (T - r true)) = -1 := htangent true; linarith)
    hW0 hW1 hpW0 hpW1
  · exact fun z hz => hsep0 z ⟨hz.2, hz.1⟩
  · intro z hz
    apply hsep1 z
    exact ⟨hz.2, hz.1.elim Or.inr Or.inl⟩

end PoincareConjecture
