import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoCornerArcStrips
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcObstacleBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcStripNeighborhood

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_two_corner_arc_bands
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
      (if vertical e then ((0 : ℝ), r e) else (r e, 0)) ∈ (H e).source)
    {O : Set AnnulusCoordinates} (hO : IsOpen O)
    (hOarc : gamma '' Icc 0 T ⊆ O) :
    let C (e : Bool) := ⋃ i,
      ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
    (∀ e, C e ⊆ closure U) → Disjoint (C false) (C true) →
    (∀ e : Bool, C e ∩ frontier U ⊆
      (fun s => gamma (if e then T - s else s)) '' Icc 0 (r e) ∪ K) →
    ∃ d : ℝ → AnnulusCoordinates,
      (∀ e : Bool, ∀ z ∈ Icc (0 : ℝ) 1,
        gamma (if e then T - r e else r e) +
          z • d (if e then T - r e else r e) ∈ C e) ∧
      ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
        (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ),
        0 < n ∧ StrictMono c ∧ c 0 = r false ∧ c (Fin.last n) = T - r true ∧
        ∃ epsilon > 0, epsilon ≤ 1 ∧
          ∀ lengths : Fin (n + 1) → ℝ,
            (∀ k, lengths k ∈ Ioo (0 : ℝ) epsilon) →
            ∃ B : ∀ i : Fin n,
              ObliqueBandFaces
                (collarParameterEquiv.trans (L i).symm).toHomeomorph.toOpenPartialHomeomorph
                (f i) (G i (c i.castSucc)) (G i (c i.succ))
                (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
                (L i (d (c i.succ))).1 (L i (d (c i.succ))).2
                (lengths i.castSucc) (lengths i.succ),
              (∀ i, (B i).carrier ⊆ O) ∧
              (∀ i, (B i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) ∧
                (B i).leftCut = segment ℝ (gamma (c i.castSucc))
                  (gamma (c i.castSucc) + lengths i.castSucc • d (c i.castSucc)) ∧
                (B i).rightCut = segment ℝ (gamma (c i.succ))
                  (gamma (c i.succ) + lengths i.succ • d (c i.succ)) ∧
                (B i).carrier ⊆ closure U ∧ (B i).carrier \ (B i).lowerArc ⊆ U) ∧
              (∀ i j : Fin n, i.succ < j.castSucc →
                Disjoint (B i).carrier (B j).carrier) ∧
              (∀ i j : Fin n, i.succ = j.castSucc →
                (B i).carrier ∩ (B j).carrier = segment ℝ (gamma (c i.succ))
                  (gamma (c i.succ) + lengths i.succ • d (c i.succ))) ∧
              ∀ i, (C false ∪ C true) ∩ (B i).carrier =
                (if c i.castSucc = r false then (B i).leftCut else ∅) ∪
                  (if c i.succ = T - r true then (B i).rightCut else ∅) := by
  classical
  intro C hsub hCC hcontact
  obtain ⟨d, hd, hpaths, n, c, L, G, f, hf, P, rho, hrho, hn, hc, hcfirst, hclast,
    hgraph, hstrip, hsep, hadj, hobstacle⟩ :=
    m64Intrinsic_exists_two_corner_arc_strips hg hinj hregular hK havoid hU hV hdisj
      hfU hfV hray r hr hrbound H F positive vertical hsource hF hFi hfirst hsecond
      hchord hsector haxis htip hsub hCC hcontact
  let S (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
  have hcut (k : Fin (n + 1)) : c k ∈ Icc (r false) (T - r true) := by
    constructor
    · simpa only [hcfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hclast] using hc.monotone (Fin.le_last k)
  have haxisO (i : Fin n) : ∀ t ∈ Icc (0 : ℝ) 1, S i (t, 0) ∈ O := by
    intro t ht
    apply hOarc
    apply image_mono (Icc_subset_Icc ((hr false).le.trans (hcut i.castSucc).1)
      ((hcut i.succ).2.trans (sub_le_self T (hr true).le)))
    rw [← (hstrip i).2.2]
    exact ⟨t, ht, rfl⟩
  have hwidth (i : Fin n) := m64Intrinsic_exists_strip_neighborhood_width (S i)
    (fun t ht => (hstrip i).2.1 ⟨ht, neg_lt_zero.mpr hrho, hrho⟩) hO (haxisO i)
  choose width hwidth hneighborhood using hwidth
  obtain ⟨eta, heta, hetale⟩ := exists_pos_le_finite_family width hwidth
  let delta := min rho eta
  have hdelta : 0 < delta := lt_min hrho heta
  have hdr : delta ≤ rho := min_le_left _ _
  have hdw (i : Fin n) : delta ≤ width i := (min_le_right _ _).trans (hetale i)
  have hthin (i : Fin n) :
      S i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta) ⊆
        S i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-rho) rho) :=
    image_mono (prod_subset_prod_right (Ioo_subset_Ioo (neg_le_neg hdr) hdr))
  have hthinO (i : Fin n) :
      S i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta) ⊆ O :=
    (image_mono (prod_subset_prod_right
      (Ioo_subset_Ioo (neg_le_neg (hdw i)) (hdw i)))).trans (hneighborhood i).2
  have hpaths' (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      gamma (r false) + z • d (r false) ∈ C false ∪ C true ∧
        gamma (T - r true) + z • d (T - r true) ∈ C false ∪ C true :=
    ⟨Or.inl (hpaths false z hz), Or.inr (hpaths true z hz)⟩
  obtain ⟨epsilon, hepsilon, hepsilon1, hbands⟩ :=
    m64Intrinsic_exists_arc_inward_obstacle_band_chain hg hinj (hr false)
      (sub_lt_self T (hr true)) hregular hK havoid hU hV hdisj hfU hfV hray d hd
      hpaths' c L G f hf P hc hcfirst hclast hgraph hdelta
      (fun i => (hstrip i).2.2)
      (fun i j hij => (hsep i j hij).mono (hthin i) (hthin j))
      (fun i j hij t ht s hs z w hz hw heq =>
        hadj i j hij t ht s hs z w (hz.trans_le hdr) (hw.trans_le hdr) heq)
      (fun i t ht z hz hp => hobstacle i t ht z (hz.trans_le hdr) hp)
  refine ⟨d, hpaths, n, c, L, G, f, hn, hc, hcfirst, hclast,
    epsilon, hepsilon, hepsilon1, ?_⟩
  intro lengths hlengths
  obtain ⟨B, hBO, hB, hsepB, hadjB, hcapB⟩ := hbands lengths hlengths
  exact ⟨B, fun i => (hBO i).trans (hthinO i), hB, hsepB, hadjB, hcapB⟩

end PoincareConjecture
