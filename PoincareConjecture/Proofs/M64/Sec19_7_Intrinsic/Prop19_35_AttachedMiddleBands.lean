import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ObstacleStripChain
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcObstacleBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcStripNeighborhood

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_attached_middle_bands
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T) (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {K U V C O : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoidK : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      gamma t + r • quarterTurn (deriv gamma t) ∈ U)
    (d : ℝ → AnnulusCoordinates)
    (hd : ∀ t ∈ Icc a b, 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t))
    (hC : IsClosed C) (havoid : ∀ t ∈ Ioo a b, gamma t ∉ C)
    (hpaths : ∀ z ∈ Icc (0 : ℝ) 1,
      gamma a + z • d a ∈ C ∧ gamma b + z • d b ∈ C)
    (ellA ellB : AnnulusCoordinates →L[ℝ] ℝ)
    (hcutA : ellA (d a) = 0) (hcutB : ellB (d b) = 0)
    (htangentA : 0 < ellA (deriv gamma a)) (htangentB : ellB (deriv gamma b) < 0)
    {WA WB : Set AnnulusCoordinates} (hWA : IsOpen WA) (hWB : IsOpen WB)
    (haW : gamma a ∈ WA) (hbW : gamma b ∈ WB)
    (hsepA : ∀ z ∈ C ∩ WA, ellA (z - gamma a) ≤ 0)
    (hsepB : ∀ z ∈ C ∩ WB, ellB (z - gamma b) ≤ 0)
    (hO : IsOpen O) (haxisO : gamma '' Icc a b ⊆ O) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
      (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ),
      0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
      ∃ epsilon > 0, epsilon ≤ 1 ∧
        ∀ lengths : Fin (n + 1) → ℝ, (∀ k, lengths k ∈ Ioo (0 : ℝ) epsilon) →
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
            (∀ i j : Fin n, i.succ < j.castSucc → Disjoint (B i).carrier (B j).carrier) ∧
            (∀ i j : Fin n, i.succ = j.castSucc →
              (B i).carrier ∩ (B j).carrier = segment ℝ (gamma (c i.succ))
                (gamma (c i.succ) + lengths i.succ • d (c i.succ))) ∧
            ∀ i, C ∩ (B i).carrier =
              (if c i.castSucc = a then (B i).leftCut else ∅) ∪
                (if c i.succ = b then (B i).rightCut else ∅) := by
  obtain ⟨n, c, L, G, f, hf, P, rho, hrho, hn, hc, hfirst, hlast,
      hgraph, hstrip, hsep, hadj, hobstacle⟩ :=
    m64Intrinsic_exists_obstacle_avoiding_strip_chain hg hab
      (hinj.mono (Icc_subset_Icc ha.le hb.le))
      (fun t ht => hregular t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩) d hd
      hC havoid ellA ellB hcutA hcutB htangentA htangentB hWA hWB haW hbW hsepA hsepB
  let S (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
  have hcut (k : Fin (n + 1)) : c k ∈ Icc a b := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  have hSO (i : Fin n) : ∀ t ∈ Icc (0 : ℝ) 1, S i (t, 0) ∈ O := by
    intro t ht
    apply haxisO
    apply image_mono (Icc_subset_Icc (hcut i.castSucc).1 (hcut i.succ).2)
    rw [← (hstrip i).2.2]
    exact ⟨t, ht, rfl⟩
  have hwidth (i : Fin n) := m64Intrinsic_exists_strip_neighborhood_width (S i)
    (fun t ht => (hstrip i).2.1 ⟨ht, neg_lt_zero.mpr hrho, hrho⟩) hO (hSO i)
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
  have hthinO (i : Fin n) : S i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta) ⊆ O :=
    (image_mono (prod_subset_prod_right
      (Ioo_subset_Ioo (neg_le_neg (hdw i)) (hdw i)))).trans (hneighborhood i).2
  obtain ⟨epsilon, hepsilon, hepsilon1, hbands⟩ :=
    m64Intrinsic_exists_arc_inward_obstacle_band_chain hg hinj ha hb hregular
      hK havoidK hU hV hUV hfront hfV hray d hd hpaths c L G f hf P
      hc hfirst hlast hgraph hdelta (fun i => (hstrip i).2.2)
      (fun i j hij => (hsep i j hij).mono (hthin i) (hthin j))
      (fun i j hij t ht s hs z w hz hw =>
        hadj i j hij t ht s hs z w (hz.trans_le hdr) (hw.trans_le hdr))
      (fun i t ht z hz => hobstacle i t ht z (hz.trans_le hdr))
  refine ⟨n, c, L, G, f, hn, hc, hfirst, hlast, epsilon, hepsilon, hepsilon1, ?_⟩
  intro lengths hlengths
  obtain ⟨B, hBO, hB, hsepB, hadjB, hCB⟩ := hbands lengths hlengths
  exact ⟨B, fun i => (hBO i).trans (hthinO i), hB, hsepB, hadjB, hCB⟩

end PoincareConjecture
