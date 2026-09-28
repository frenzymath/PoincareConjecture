import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThinGraphBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandBoundaryGeometry










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem occupied_band
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb delta : ℝ}
    (B : ObliqueBandFaces F f a b ua wa ub wb ra rb)
    (S : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    {U : Set AnnulusCoordinates} (hd : 0 < delta)
    (hcoord : ∀ q, B.coordinates q = S (collarParameterEquiv q))
    (hheight : ∀ t ∈ Icc (0 : ℝ) 1, B.height t < delta)
    (hcarrier : B.carrier = S ''
      {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ B.height q.1})
    (hinside : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) delta,
      (t, z) ∈ S.source ∧ S (t, z) ∈ closure U ∧ (0 < z → S (t, z) ∈ U)) :
    B.lowerArc = (fun t => S (t, 0)) '' Icc (0 : ℝ) 1 ∧
      B.carrier ⊆ S '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta) ∧
      B.carrier ⊆ closure U ∧ B.carrier \ B.lowerArc ⊆ U := by
  have hbottom : B.lowerArc = (fun t => S (t, 0)) '' Icc (0 : ℝ) 1 := by
    rw [← m64Intrinsic_band_bottom_image B]
    exact image_congr (fun t _ => by rw [hcoord, collarParameterEquiv.apply_symm_apply])
  refine ⟨hbottom, ?_, ?_, ?_⟩
  · rw [hcarrier]
    apply image_mono
    intro q hq
    exact ⟨hq.1, ⟨by linarith [hq.2.1], hq.2.2.trans_lt (hheight q.1 hq.1)⟩⟩
  · rw [hcarrier]
    rintro _ ⟨q, hq, rfl⟩
    exact (hinside q.1 hq.1 q.2
      ⟨hq.2.1, (hq.2.2.trans_lt (hheight q.1 hq.1)).le⟩).2.1
  · rintro p ⟨hp, hnot⟩
    rw [hcarrier] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hpos : 0 < q.2 := by
      by_contra hn
      have hz : q.2 = 0 := le_antisymm (le_of_not_gt hn) hq.2.1
      apply hnot
      rw [hbottom]
      exact ⟨q.1, hq.1, by rw [← hz]⟩
    exact (hinside q.1 hq.1 q.2
      ⟨hq.2.1, (hq.2.2.trans_lt (hheight q.1 hq.1)).le⟩).2.2 hpos




theorem m64Intrinsic_exists_joined_occupied_bands
    (L R : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {X Y : Set ℝ} (hX : IsOpen X) (hY : IsOpen Y)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f X) (hg : ContDiffOn ℝ ∞ g Y)
    {a b c d ua wa ub wb uc wc ud wd delta : ℝ}
    (hab : a < b) (hcd : c < d) (hI : Icc a b ⊆ X) (hJ : Icc c d ⊆ Y)
    (P : TransverseGraphCuts f a b ua wa ub wb)
    (Q : TransverseGraphCuts g c d uc wc ud wd)
    {p w : AnnulusCoordinates}
    (hbaseP : L (b, f b) = p) (hbaseQ : R (c, g c) = p)
    (hdirP : L (ub, wb) = w) (hdirQ : R (uc, wc) = w)
    {U : Set AnnulusCoordinates} (hd : 0 < delta) :
    let S := P.linearCoordinates L hX hf
    let T := Q.linearCoordinates R hY hg
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) delta,
      (t, z) ∈ S.source ∧ S (t, z) ∈ closure U ∧ (0 < z → S (t, z) ∈ U)) →
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) delta,
      (t, z) ∈ T.source ∧ T (t, z) ∈ closure U ∧ (0 < z → T (t, z) ∈ U)) →
    (∀ h k : ℝ → ℝ,
      (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ h t ∧ h t < delta) →
      (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ k t ∧ k t < delta) →
      ∀ r : ℝ, 0 ≤ r → r ∈ P.right.parameter.source → r ∈ Q.left.parameter.source →
        h 1 = P.right.parameter r → k 0 = Q.left.parameter r →
        S '' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ h q.1} ∩
          T '' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ k q.1} =
            segment ℝ p (p + r • w)) →
    ∃ epsilon > 0, ∀ ra ∈ Ioo (0 : ℝ) epsilon, ∀ r ∈ Ioo (0 : ℝ) epsilon,
      ∀ rb ∈ Ioo (0 : ℝ) epsilon,
        ∃ (B : ObliqueBandFaces
          (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
          f a b ua wa ub wb ra r)
          (C : ObliqueBandFaces
          (collarParameterEquiv.trans R).toHomeomorph.toOpenPartialHomeomorph
          g c d uc wc ud wd r rb),
          B.lowerArc = (fun t => S (t, 0)) '' Icc (0 : ℝ) 1 ∧
          C.lowerArc = (fun t => T (t, 0)) '' Icc (0 : ℝ) 1 ∧
          B.carrier ⊆ S '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta) ∧
          C.carrier ⊆ T '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta) ∧
          B.carrier ⊆ closure U ∧ C.carrier ⊆ closure U ∧
          B.carrier \ B.lowerArc ⊆ U ∧ C.carrier \ C.lowerArc ⊆ U ∧
          B.leftCut = segment ℝ (L (a, f a)) (L (a, f a) + ra • L (ua, wa)) ∧
          B.rightCut = segment ℝ p (p + r • w) ∧
          C.leftCut = segment ℝ p (p + r • w) ∧
          C.rightCut = segment ℝ (R (d, g d)) (R (d, g d) + rb • R (ud, wd)) ∧
          B.carrier ∩ C.carrier = segment ℝ p (p + r • w) := by
  intro S T hinsideS hinsideT hinter
  obtain ⟨epsilonP, heP, hbandP⟩ := m64Intrinsic_exists_thin_graph_bands L hX hf hab hI P hd
  obtain ⟨epsilonQ, heQ, hbandQ⟩ := m64Intrinsic_exists_thin_graph_bands R hY hg hcd hJ Q hd
  refine ⟨min epsilonP epsilonQ, lt_min heP heQ, ?_⟩
  intro ra hra r hr rb hrb
  obtain ⟨B, hBl, hBr, hBcoord, hBheight, hBcarrier, hBleft, hBright⟩ :=
    hbandP ra ⟨hra.1, hra.2.trans_le (min_le_left _ _)⟩
      r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩
  obtain ⟨C, hCl, hCr, hCcoord, hCheight, hCcarrier, hCleft, hCright⟩ :=
    hbandQ r ⟨hr.1, hr.2.trans_le (min_le_right _ _)⟩
      rb ⟨hrb.1, hrb.2.trans_le (min_le_right _ _)⟩
  obtain ⟨hBlower, hBstrip, hBsub, hBopen⟩ :=
    occupied_band B S hd hBcoord hBheight hBcarrier hinsideS
  obtain ⟨hClower, hCstrip, hCsub, hCopen⟩ :=
    occupied_band C T hd hCcoord hCheight hCcarrier hinsideT
  refine ⟨B, C, hBlower, hClower, hBstrip, hCstrip, hBsub, hCsub, hBopen, hCopen,
    hBleft, ?_, ?_, hCright, ?_⟩
  · simpa only [hbaseP, hdirP] using hBright
  · simpa only [hbaseQ, hdirQ] using hCleft
  · rw [hBcarrier, hCcarrier]
    apply hinter B.height C.height
      (fun t ht => ⟨(B.height_pos ht).le, hBheight t ht⟩)
      (fun t ht => ⟨(C.height_pos ht).le, hCheight t ht⟩) r hr.1.le
    · rw [← hBr]
      exact B.interface.right_parameter_mem
    · rw [← hCl]
      exact C.interface.left_parameter_mem
    · rw [B.height_one, hBr]
    · rw [C.height_zero, hCl]

end PoincareConjecture
