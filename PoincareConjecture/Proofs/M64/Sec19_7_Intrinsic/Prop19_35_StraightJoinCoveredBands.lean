import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinOccupiedStrips
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedOccupiedBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcStripNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinBandCoverage
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GraphObstacleWidth

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_straight_join_covered_bands
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {A0 A B B1 c eta : ℝ} (haA : A0 < A) (hBb : B < B1) (hc : 0 < c) (heta : 0 < eta)
    (hai : InjOn alpha (Icc A0 A)) (hbi : InjOn beta (Icc B B1))
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A)
    (hmeet : ∀ s ∈ Icc A0 A, ∀ t ∈ Icc B B1,
      alpha s = beta t → s = A ∧ t = B)
    (hregular : ∀ t ∈ Ioo A0 A, deriv alpha t ≠ 0)
    {K U V O : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : alpha A ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc A0 A ∪ beta '' Icc B B1 ∪ K)
    (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo A0 A, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      alpha t + r • quarterTurn (deriv alpha t) ∈ U)
    (hO : IsOpen O) (hpO : alpha A ∈ O) :
    let w := quarterTurn (deriv alpha A)
    ∃ epsilon > 0, epsilon < eta ∧ A0 < A - epsilon ∧ B + epsilon < B1 ∧
      ∃ (L R : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates) (f g : ℝ → ℝ) (a b s t : ℝ),
        a < b ∧ s < t ∧
        L (a, f a) = alpha (A - epsilon) ∧ L (b, f b) = alpha A ∧
        R (s, g s) = alpha A ∧ R (t, g t) = beta (B + epsilon) ∧
        0 < inner ℝ (quarterTurn (deriv alpha (A - epsilon))) w ∧
        0 < inner ℝ (quarterTurn (deriv beta (B + epsilon))) w ∧
        (∃ v : ℝ, 0 < v ∧ deriv alpha (A - epsilon) = v • L (1, deriv f a)) ∧
        (∃ v : ℝ, 0 < v ∧ deriv beta (B + epsilon) = v • R (1, deriv g t)) ∧
        ∃ cutoff > 0, ∀ ra ∈ Ioo (0 : ℝ) cutoff, ∀ r ∈ Ioo (0 : ℝ) cutoff,
          ∀ rb ∈ Ioo (0 : ℝ) cutoff,
            ∃ (C : ObliqueBandFaces
              (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
              f a b (L.symm w).1 (L.symm w).2 (L.symm w).1 (L.symm w).2 ra r)
              (D : ObliqueBandFaces
              (collarParameterEquiv.trans R).toHomeomorph.toOpenPartialHomeomorph
              g s t (R.symm w).1 (R.symm w).2 (R.symm w).1 (R.symm w).2 r rb),
              C.lowerArc = alpha '' Icc (A - epsilon) A ∧
              D.lowerArc = beta '' Icc B (B + epsilon) ∧
              C.carrier ⊆ O ∧ D.carrier ⊆ O ∧
              C.carrier ⊆ closure U ∧ D.carrier ⊆ closure U ∧
              C.carrier \ C.lowerArc ⊆ U ∧ D.carrier \ D.lowerArc ⊆ U ∧
              C.leftCut = segment ℝ (alpha (A - epsilon)) (alpha (A - epsilon) + ra • w) ∧
              C.rightCut = segment ℝ (alpha A) (alpha A + r • w) ∧
              D.leftCut = segment ℝ (alpha A) (alpha A + r • w) ∧
              D.rightCut = segment ℝ (beta (B + epsilon)) (beta (B + epsilon) + rb • w) ∧
              C.carrier ∩ D.carrier = segment ℝ (alpha A) (alpha A + r • w) ∧
              ∃ W : Set AnnulusCoordinates, IsOpen W ∧ alpha A ∈ W ∧
                W ∩ closure U ⊆ C.carrier ∪ D.carrier := by
  intro w
  have hnearA : ∀ᶠ t in 𝓝 A, alpha t ∈ O :=
    ha.continuous.continuousAt.eventually (hO.mem_nhds hpO)
  have hnearB : ∀ᶠ t in 𝓝 B, beta t ∈ O :=
    hb.continuous.continuousAt.eventually (hO.mem_nhds (hend ▸ hpO))
  obtain ⟨rA, hrA, hballA⟩ := Metric.mem_nhds_iff.mp hnearA
  obtain ⟨rB, hrB, hballB⟩ := Metric.mem_nhds_iff.mp hnearB
  obtain ⟨epsilon, hepsilon, heBound, haeps, hbeps, L, R, G, H, f, g, hf, hg,
      P, Q, d, hd, _, _, htransA, htransB,
      hgraphA, hgraphB, haxisA, haxisB, hinsideA, hinsideB, _, hinter⟩ :=
    m64Intrinsic_exists_straight_join_occupied_strips ha hb haA hBb hc
      (lt_min heta (lt_min hrA hrB)) hai hbi hend hreg htan hmeet hregular
      hK hpK hU hV hUV hfront hfV hray
  have heeta : epsilon < eta := heBound.trans_le (min_le_left _ _)
  have heR : epsilon < min rA rB := heBound.trans_le (min_le_right _ _)
  have haxisAO : alpha '' Icc (A - epsilon) A ⊆ O := by
    rintro _ ⟨s, hs, rfl⟩
    apply hballA
    rw [Metric.mem_ball, Real.dist_eq]
    exact (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩).trans_lt
      (heR.trans_le (min_le_left _ _))
  have haxisBO : beta '' Icc B (B + epsilon) ⊆ O := by
    rintro _ ⟨s, hs, rfl⟩
    apply hballB
    rw [Metric.mem_ball, Real.dist_eq]
    exact (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩).trans_lt
      (heR.trans_le (min_le_right _ _))
  let S := P.linearCoordinates L.symm G.open_target hf
  let T := Q.linearCoordinates R.symm H.open_target hg
  obtain ⟨rhoA, hrhoA, _, hSO⟩ := m64Intrinsic_exists_strip_neighborhood_width S
    (fun t ht => (hinsideA t ht 0 ⟨le_rfl, hd.le⟩).1) hO
    (fun t ht => haxisAO (haxisA.subset ⟨t, ht, rfl⟩))
  obtain ⟨rhoB, hrhoB, _, hTO⟩ := m64Intrinsic_exists_strip_neighborhood_width T
    (fun t ht => (hinsideB t ht 0 ⟨le_rfl, hd.le⟩).1) hO
    (fun t ht => haxisBO (haxisB.subset ⟨t, ht, rfl⟩))
  let delta := min d (min rhoA rhoB)
  have hdelta : 0 < delta := lt_min hd (lt_min hrhoA hrhoB)
  have hdd : delta ≤ d := min_le_left _ _
  have hdA : delta ≤ rhoA := (min_le_right _ _).trans (min_le_left _ _)
  have hdB : delta ≤ rhoB := (min_le_right _ _).trans (min_le_right _ _)
  have heA : A - epsilon < A := sub_lt_self _ hepsilon
  have heB : B < B + epsilon := lt_add_of_pos_right _ hepsilon
  have hpa : L.symm (G (A - epsilon), f (G (A - epsilon))) = alpha (A - epsilon) := by
    rw [← hgraphA.2.2.2.1 _ (hgraphA.1 (left_mem_Icc.mpr heA.le)), L.symm_apply_apply]
  have hpb : L.symm (G A, f (G A)) = alpha A := by
    rw [← hgraphA.2.2.2.1 _ (hgraphA.1 (right_mem_Icc.mpr heA.le)), L.symm_apply_apply]
  have hpc : R.symm (H B, g (H B)) = alpha A := by
    rw [← hgraphB.2.2.2.1 _ (hgraphB.1 (left_mem_Icc.mpr heB.le)), R.symm_apply_apply, hend]
  have hpd : R.symm (H (B + epsilon), g (H (B + epsilon))) = beta (B + epsilon) := by
    rw [← hgraphB.2.2.2.1 _ (hgraphB.1 (right_mem_Icc.mpr heB.le)), R.symm_apply_apply]
  have hGab := hgraphA.2.1 (hgraphA.1 (left_mem_Icc.mpr heA.le))
    (hgraphA.1 (right_mem_Icc.mpr heA.le)) heA
  have hHcd := hgraphB.2.1 (hgraphB.1 (left_mem_Icc.mpr heB.le))
    (hgraphB.1 (right_mem_Icc.mpr heB.le)) heB
  have hregB : deriv beta (B + epsilon) ≠ 0 := by
    intro hz
    simp only [hz, map_zero, inner_zero_left] at htransB
    exact (lt_irrefl 0) htransB
  have htangentA : ∃ v : ℝ, 0 < v ∧
      deriv alpha (A - epsilon) = v • L.symm (1, deriv f (G (A - epsilon))) := by
    refine ⟨deriv G (A - epsilon), m64Intrinsic_graph_parameter_deriv_pos ha L G
      hgraphA.2.2.1 hf hgraphA.2.1 hgraphA.2.2.2.1
      (hgraphA.1 (left_mem_Icc.mpr heA.le)) (hregular _ ⟨haeps, heA⟩), ?_⟩
    apply L.injective
    simpa only [map_smul, L.apply_symm_apply] using m64Intrinsic_graph_tangent
      ha L G hgraphA.2.2.1 hf hgraphA.2.2.2.1 (hgraphA.1 (left_mem_Icc.mpr heA.le))
  have htangentB : ∃ v : ℝ, 0 < v ∧
      deriv beta (B + epsilon) = v • R.symm (1, deriv g (H (B + epsilon))) := by
    refine ⟨deriv H (B + epsilon), m64Intrinsic_graph_parameter_deriv_pos hb R H
      hgraphB.2.2.1 hg hgraphB.2.1 hgraphB.2.2.2.1
      (hgraphB.1 (right_mem_Icc.mpr heB.le)) hregB, ?_⟩
    apply R.injective
    simpa only [map_smul, R.apply_symm_apply] using m64Intrinsic_graph_tangent
      hb R H hgraphB.2.2.1 hg hgraphB.2.2.2.1 (hgraphB.1 (right_mem_Icc.mpr heB.le))
  obtain ⟨cutoff, hcutoff, hbands⟩ := m64Intrinsic_exists_joined_occupied_bands
    L.symm R.symm G.open_target H.open_target hf hg hGab hHcd
    hgraphA.2.2.2.2.2 hgraphB.2.2.2.2.2 P Q (w := w) hpb hpc
    (by simp only [Prod.eta, L.symm_apply_apply, w])
    (by simp only [Prod.eta, R.symm_apply_apply, w]) hdelta
    (fun t ht z hz => hinsideA t ht z ⟨hz.1, hz.2.trans hdd⟩)
    (fun t ht z hz => hinsideB t ht z ⟨hz.1, hz.2.trans hdd⟩)
    (fun h k hh hk => hinter h k (fun t ht => ⟨(hh t ht).1, (hh t ht).2.trans_le hdd⟩)
      (fun t ht => ⟨(hk t ht).1, (hk t ht).2.trans_le hdd⟩))
  refine ⟨epsilon, hepsilon, heeta, haeps, hbeps, L.symm, R.symm, f, g,
    G (A - epsilon), G A, H B, H (B + epsilon), hGab, hHcd, hpa, hpb, hpc, hpd,
    htransA, htransB, htangentA, htangentB, cutoff, hcutoff, ?_⟩
  intro ra hra r hr rb hrb
  obtain ⟨C, D, hClower, hDlower, hCS, hDT, hCsub, hDsub, hCopen, hDopen,
      hCleft, hCright, hDleft, hDright, hCD⟩ := hbands ra hra r hr rb hrb
  have hClower' : C.lowerArc = alpha '' Icc (A - epsilon) A := hClower.trans haxisA
  have hDlower' : D.lowerArc = beta '' Icc B (B + epsilon) := hDlower.trans haxisB
  have hCO : C.carrier ⊆ O := hCS.trans ((image_mono
    (prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg hdA) hdA))).trans hSO)
  have hDO : D.carrier ⊆ O := hDT.trans ((image_mono
    (prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg hdB) hdB))).trans hTO)
  have hcover := m64Intrinsic_straight_join_bands_cover_region ha hb haA hBb hc hai hbi
    hend hreg htan hK hpK hU hV hUV hfront hfV L.symm R.symm C D
    hpb hpc (d := w)
    (by simp only [Prod.eta, L.symm_apply_apply, w])
    (by simp only [Prod.eta, R.symm_apply_apply, w]) hCD
    (hClower'.subset.trans (image_mono (Icc_subset_Icc haeps.le le_rfl)))
    (hDlower'.subset.trans (image_mono (Icc_subset_Icc le_rfl hbeps.le))) hCsub hDsub
  refine ⟨C, D, hClower', hDlower', hCO, hDO, hCsub, hDsub, hCopen, hDopen,
    ?_, hCright, hDleft, ?_, hCD, hcover⟩
  · simpa only [hpa, Prod.eta, L.symm_apply_apply] using hCleft
  · simpa only [hpd, Prod.eta, R.symm_apply_apply] using hDright

end PoincareConjecture
