import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinStrips
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedStripFrontier
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedStripSide
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcInwardRaySign





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture




theorem m64Intrinsic_exists_straight_join_occupied_strips
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {A0 A B B1 c eta : ℝ} (haA : A0 < A) (hBb : B < B1) (hc : 0 < c) (heta : 0 < eta)
    (hai : InjOn alpha (Icc A0 A)) (hbi : InjOn beta (Icc B B1))
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A)
    (hmeet : ∀ s ∈ Icc A0 A, ∀ t ∈ Icc B B1,
      alpha s = beta t → s = A ∧ t = B)
    (hregular : ∀ t ∈ Ioo A0 A, deriv alpha t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : alpha A ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc A0 A ∪ beta '' Icc B B1 ∪ K)
    (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo A0 A, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      alpha t + r • quarterTurn (deriv alpha t) ∈ U) :
    let w := quarterTurn (deriv alpha A)
    ∃ epsilon > 0, epsilon < eta ∧ A0 < A - epsilon ∧ B + epsilon < B1 ∧
      ∃ (L R : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G H : OpenPartialHomeomorph ℝ ℝ) (f g : ℝ → ℝ)
        (hf : ContDiffOn ℝ ∞ f G.target) (hg : ContDiffOn ℝ ∞ g H.target)
        (P : TransverseGraphCuts f (G (A - epsilon)) (G A)
          (L w).1 (L w).2 (L w).1 (L w).2)
        (Q : TransverseGraphCuts g (H B) (H (B + epsilon))
          (R w).1 (R w).2 (R w).1 (R w).2),
        let S := P.linearCoordinates L.symm G.open_target hf
        let T := Q.linearCoordinates R.symm H.open_target hg
        ∃ delta > 0, delta ≤ P.radius ∧ delta ≤ Q.radius ∧
          0 < inner ℝ (quarterTurn (deriv alpha (A - epsilon))) w ∧
          0 < inner ℝ (quarterTurn (deriv beta (B + epsilon))) w ∧
          (Icc (A - epsilon) A ⊆ G.source ∧ StrictMonoOn G G.source ∧
            ContDiffOn ℝ ∞ G G.source ∧
            (∀ t ∈ G.source, L (alpha t) = (G t, f (G t))) ∧
            G '' Icc (A - epsilon) A = Icc (G (A - epsilon)) (G A) ∧
            Icc (G (A - epsilon)) (G A) ⊆ G.target) ∧
          (Icc B (B + epsilon) ⊆ H.source ∧ StrictMonoOn H H.source ∧
            ContDiffOn ℝ ∞ H H.source ∧
            (∀ t ∈ H.source, R (beta t) = (H t, g (H t))) ∧
            H '' Icc B (B + epsilon) = Icc (H B) (H (B + epsilon)) ∧
            Icc (H B) (H (B + epsilon)) ⊆ H.target) ∧
          ((fun t => S (t, 0)) '' Icc (0 : ℝ) 1 = alpha '' Icc (A - epsilon) A) ∧
          ((fun t => T (t, 0)) '' Icc (0 : ℝ) 1 = beta '' Icc B (B + epsilon)) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) delta,
            (t, z) ∈ S.source ∧ S (t, z) ∈ closure U ∧ (0 < z → S (t, z) ∈ U)) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) delta,
            (t, z) ∈ T.source ∧ T (t, z) ∈ closure U ∧ (0 < z → T (t, z) ∈ U)) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
            ∀ z y : ℝ, |z| < delta → |y| < delta →
              (t, z) ∈ S.source ∧ (s, y) ∈ T.source ∧
                (S (t, z) = T (s, y) → t = 1 ∧ s = 0)) ∧
          ∀ h k : ℝ → ℝ,
            (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ h t ∧ h t < delta) →
            (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ k t ∧ k t < delta) →
            ∀ r : ℝ, 0 ≤ r → r ∈ P.right.parameter.source → r ∈ Q.left.parameter.source →
              h 1 = P.right.parameter r → k 0 = Q.left.parameter r →
              S '' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ h q.1} ∩
                T '' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ k q.1} =
                  segment ℝ (alpha A) (alpha A + r • w) := by
  intro w
  have hnearA : ∀ᶠ t in 𝓝 A, alpha t ∉ K :=
    ha.continuous.continuousAt.eventually (hK.isClosed.isOpen_compl.mem_nhds hpK)
  have hnearB : ∀ᶠ t in 𝓝 B, beta t ∉ K :=
    hb.continuous.continuousAt.eventually (hK.isClosed.isOpen_compl.mem_nhds (hend ▸ hpK))
  obtain ⟨rA, hrA, hballA⟩ := Metric.mem_nhds_iff.mp hnearA
  obtain ⟨rB, hrB, hballB⟩ := Metric.mem_nhds_iff.mp hnearB
  let bound := min eta (min (min (A - A0) (B1 - B)) (min rA rB))
  have hbound : 0 < bound := lt_min heta
    (lt_min (lt_min (sub_pos.mpr haA) (sub_pos.mpr hBb)) (lt_min hrA hrB))
  obtain ⟨epsilon, hepsilon, heB, hleft, hright, _, _, hlocal⟩ :=
    m64Intrinsic_straight_join_local_geometry ha hb hbound hc hend hreg htan
  have heeta : epsilon < eta := heB.trans_le (min_le_left _ _)
  have heAB : epsilon < min (A - A0) (B1 - B) :=
    heB.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heR : epsilon < min rA rB :=
    heB.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have haeps : A0 < A - epsilon := by have h := heAB.trans_le (min_le_left _ _); linarith
  have hbeps : B + epsilon < B1 := by have h := heAB.trans_le (min_le_right _ _); linarith
  have havoidA (t : ℝ) (ht : t ∈ Icc (A - epsilon) A) : alpha t ∉ K := by
    apply hballA
    rw [Metric.mem_ball, Real.dist_eq]
    exact (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans_lt
      (heR.trans_le (min_le_left _ _))
  have havoidB (t : ℝ) (ht : t ∈ Icc B (B + epsilon)) : beta t ∉ K := by
    apply hballB
    rw [Metric.mem_ball, Real.dist_eq]
    exact (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans_lt
      (heR.trans_le (min_le_right _ _))
  have heA : A - epsilon < A := sub_lt_self _ hepsilon
  have heB' : B < B + epsilon := lt_add_of_pos_right _ hepsilon
  obtain ⟨L, R, G, H, f, g, hf, hg, P, Q, d, hd, hdP, hdQ,
      hgraphA, hgraphB, haxisA, haxisB, hsep, hinter⟩ :=
    m64Intrinsic_exists_joined_arc_strips ha hb heA heB' (deriv alpha A) w
      (fun t ht => (hleft t ht).1) (fun t ht => (hright t ht).1)
      (fun t ht => (hleft t ht).2) (fun t ht => (hright t ht).2) hend hlocal
  obtain ⟨rho, hrho, hrd, hfrontA, hfrontB⟩ :=
    m64Intrinsic_exists_joined_strip_frontier_width ha.continuous hb.continuous
      haeps.le heA heB' hbeps.le hai hbi hend hmeet hK havoidA havoidB hfront
      L R G H hf hg hgraphA.1 hgraphA.2.1 hgraphA.2.2.2.1
      hgraphA.2.2.2.2.1 hgraphA.2.2.2.2.2
      hgraphB.1 hgraphB.2.1 hgraphB.2.2.2.1 hgraphB.2.2.2.2.1 hgraphB.2.2.2.2.2 P Q hd hsep
  have hpOther : alpha (A - epsilon) ∉ beta '' Icc B B1 ∪ K := by
    rintro (⟨t, ht, heq⟩ | hp)
    · have he := (hmeet _ ⟨haeps.le, heA.le⟩ t ht heq.symm).1
      exact heA.ne he
    · exact havoidA _ (left_mem_Icc.mpr heA.le) hp
  have hfront' : frontier U = alpha '' Icc A0 A ∪ (beta '' Icc B B1 ∪ K) := by
    rw [hfront, union_assoc]
  have hray' := m64Intrinsic_arc_transverse_ray_enters_region ha hai ⟨haeps, heA⟩
    hregular ((isCompact_Icc.image hb.continuous).union hK) hpOther hU hV hUV hfront' hfV
    (hray _ ⟨haeps, heA⟩) (hleft _ (left_mem_Icc.mpr heA.le)).2
  have hbaseA : L.symm (G A, f (G A)) = alpha A := by
    rw [← hgraphA.2.2.2.1 A (hgraphA.1 (right_mem_Icc.mpr heA.le)), L.symm_apply_apply]
  have hbaseB : R.symm (H B, g (H B)) = alpha A := by
    rw [← hgraphB.2.2.2.1 B (hgraphB.1 (left_mem_Icc.mpr heB'.le)), R.symm_apply_apply, hend]
  have hrayL : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      L.symm (G (A - epsilon), f (G (A - epsilon))) + r • L.symm ((L w).1, (L w).2) ∈ U := by
    rw [← hgraphA.2.2.2.1 _ (hgraphA.1 (left_mem_Icc.mpr heA.le))]
    simpa only [Prod.eta, L.symm_apply_apply] using hray'
  obtain ⟨hinsideA, hinsideB⟩ := m64Intrinsic_joined_graph_strips_inside
    L.symm R.symm G.open_target H.open_target hf hg P Q (w := w) hbaseA hbaseB
    (by simp only [Prod.eta, L.symm_apply_apply])
    (by simp only [Prod.eta, R.symm_apply_apply]) hU hrho hfrontA hfrontB hrayL
  have hhalf : rho / 2 ≤ d := (half_le_self hrho.le).trans hrd
  refine ⟨epsilon, hepsilon, heeta, haeps, hbeps,
    L, R, G, H, f, g, hf, hg, P, Q, rho / 2, half_pos hrho,
    hhalf.trans hdP, hhalf.trans hdQ,
    (hleft _ (left_mem_Icc.mpr heA.le)).2, (hright _ (right_mem_Icc.mpr heB'.le)).2,
    hgraphA, hgraphB, haxisA, haxisB,
    hinsideA, hinsideB, ?_, ?_⟩
  · exact fun t ht s hs z y hz hy => hsep t ht s hs z y (hz.trans_le hhalf) (hy.trans_le hhalf)
  · intro h k hh hk
    exact hinter h k (fun t ht => ⟨(hh t ht).1, (hh t ht).2.trans_le hhalf⟩)
      (fun t ht => ⟨(hk t ht).1, (hk t ht).2.trans_le hhalf⟩)

end PoincareConjecture
