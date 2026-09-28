import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsTubeEndFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMatching

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)

theorem exists_stackTwoTubeMatchedChart
    (Tm0 Tp0 : OpenPartialHomeomorph P P)
    (hTm : ContDiffOn ℝ ∞ Tm0 Tm0.source)
    (hTmi : ContDiffOn ℝ ∞ Tm0.symm Tm0.target)
    (hTp : ContDiffOn ℝ ∞ Tp0 Tp0.source)
    (hTpi : ContDiffOn ℝ ∞ Tp0.symm Tp0.target)
    (hTmh : ∀ p ∈ Tm0.source, (Tm0 p).1 = p.1)
    (hTph : ∀ p ∈ Tp0.source, (Tp0 p).1 = p.1)
    (ell r wm wp eta : ℝ) (horder : ell < r)
    (hwm : 0 < wm) (hwp : 0 < wp) (heta : 0 < eta)
    (hTms : Ioo (ell - wm) (ell + wm) ×ˢ closedBall (0 : E2) 1 ⊆ Tm0.source)
    (hTps : Ioo (r - wp) (r + wp) ×ˢ closedBall (0 : E2) 1 ⊆ Tp0.source)
    (hP : PlanarSchoenfliesService) (c : ℝ → UnitCircle → E2)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => c p.1 p.2))
    (hce : ∀ z ∈ Icc (ell - eta) (r + eta), IsPlanarEmbedding (c z))
    (hmcircle : ∀ z ∈ Ioo (ell - wm) (ell + wm), ∀ q : UnitCircle,
      (Tm0 (z, (q : E2))).2 ∈ range (c z))
    (hpcircle : ∀ z ∈ Ioo (r - wp) (r + wp), ∀ q : UnitCircle,
      (Tp0 (z, (q : E2))).2 ∈ range (c z)) :
    ∃ epsilon delta : ℝ,
      0 < epsilon ∧ 4 * epsilon < eta ∧
      4 * epsilon < wm ∧ 4 * epsilon < wp ∧ 8 * epsilon < r - ell ∧
      0 < delta ∧ delta < 1 / 4 ∧
      ∃ Rm Rp : E2 ≃ₗᵢ[ℝ] E2,
        (Rm = LinearIsometryEquiv.refl ℝ E2 ∨
          Rm = Complex.orthonormalBasisOneI.repr.symm.trans
            (Complex.conjLIE.trans Complex.orthonormalBasisOneI.repr)) ∧
        (Rp = LinearIsometryEquiv.refl ℝ E2 ∨
          Rp = Complex.orthonormalBasisOneI.repr.symm.trans
            (Complex.conjLIE.trans Complex.orthonormalBasisOneI.repr)) ∧
        ∃ cbar : ℝ → UnitCircle → E2,
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
            (fun p : ℝ × UnitCircle => cbar p.1 p.2) ∧
          (∀ z ∈ Icc (ell - eta) (r + eta), IsPlanarEmbedding (cbar z)) ∧
          (∀ z : ℝ, range (cbar z) = range (c z)) ∧
          (∀ z ∉ Ioo (ell - 4 * epsilon) (ell + 4 * epsilon) ∪
              Ioo (r - 4 * epsilon) (r + 4 * epsilon),
            ∀ q : UnitCircle, cbar z q = c z q) ∧
          ∃ D : PlanarSchoenfliesFamilyData cbar (ell - eta) (r + eta),
            ∃ G : PlanarFamilyGraphChart D,
              ∃ Tm Tp Q : OpenPartialHomeomorph P P,
                Tm.source = {p : P | (p.1, Rm p.2) ∈ Tm0.source} ∧
                Tm.target = Tm0.target ∧
                (∀ p : P, Tm p = Tm0 (p.1, Rm p.2)) ∧
                (∀ p : P, Tm.symm p = ((Tm0.symm p).1, Rm.symm (Tm0.symm p).2)) ∧
                ContDiffOn ℝ ∞ Tm Tm.source ∧
                ContDiffOn ℝ ∞ Tm.symm Tm.target ∧
                (∀ p ∈ Tm.source, (Tm p).1 = p.1) ∧
                (∀ p ∈ Tm.target, (Tm.symm p).1 = p.1) ∧
                Icc (ell - 3 * epsilon) (ell + 3 * epsilon) ×ˢ
                  closedBall (0 : E2) 1 ⊆ Tm.source ∧
                Tp.source = {p : P | (p.1, Rp p.2) ∈ Tp0.source} ∧
                Tp.target = Tp0.target ∧
                (∀ p : P, Tp p = Tp0 (p.1, Rp p.2)) ∧
                (∀ p : P, Tp.symm p = ((Tp0.symm p).1, Rp.symm (Tp0.symm p).2)) ∧
                ContDiffOn ℝ ∞ Tp Tp.source ∧
                ContDiffOn ℝ ∞ Tp.symm Tp.target ∧
                (∀ p ∈ Tp.source, (Tp p).1 = p.1) ∧
                (∀ p ∈ Tp.target, (Tp.symm p).1 = p.1) ∧
                Icc (r - 3 * epsilon) (r + 3 * epsilon) ×ˢ
                  closedBall (0 : E2) 1 ⊆ Tp.source ∧
                Q.target = G.chart.target ∧
                ContDiffOn ℝ ∞ Q Q.source ∧
                ContDiffOn ℝ ∞ Q.symm Q.target ∧
                (∀ p ∈ Q.source, (Q p).1 = p.1) ∧
                (∀ p ∈ Q.target, (Q.symm p).1 = p.1) ∧
                Icc (ell - eta) (r + eta) ×ˢ closedBall (0 : E2) 1 ⊆ Q.source ∧
                (∀ J : Set ℝ,
                  Q '' (J ×ˢ ball (0 : E2) 1) = G.chart '' (J ×ˢ ball 0 1) ∧
                  Q '' (J ×ˢ closedBall (0 : E2) 1) =
                    G.chart '' (J ×ˢ closedBall 0 1)) ∧
                (∀ z : ℝ, ∀ q ∈ sphere (0 : E2) 1,
                  Q (z, q) = G.chart (z, q)) ∧
                (∀ z ∈ Icc (ell - epsilon) (ell + epsilon), ∀ x : E2,
                  |‖x‖ - 1| < delta →
                    (z, x) ∈ Q.source ∧ Q (z, x) = Tm (z, x)) ∧
                ∀ z ∈ Icc (r - epsilon) (r + epsilon), ∀ x : E2,
                  |‖x‖ - 1| < delta →
                    (z, x) ∈ Q.source ∧ Q (z, x) = Tp (z, x) := by
  let d := min eta (min ((r - ell) / 2) (min wm wp))
  have hd : 0 < d := lt_min heta (lt_min (by linarith only [horder]) (lt_min hwm hwp))
  have hdeta : d ≤ eta := min_le_left _ _
  have hdgap : d ≤ (r - ell) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdwm : d ≤ wm :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdwp : d ≤ wp :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  let epsilon := d / 16
  have he : 0 < epsilon := div_pos hd (by norm_num)
  have heeta : 4 * epsilon < eta := by dsimp [epsilon]; linarith only [hd, hdeta]
  have hewm : 4 * epsilon < wm := by dsimp [epsilon]; linarith only [hd, hdwm]
  have hewp : 4 * epsilon < wp := by dsimp [epsilon]; linarith only [hd, hdwp]
  have hsep : 8 * epsilon < r - ell := by
    dsimp [epsilon]
    linarith only [hd, hdgap]
  have hmBand : Ioo (ell - 4 * epsilon) (ell + 4 * epsilon) ⊆
      Icc (ell - eta) (r + eta) := by
    intro z hz
    constructor <;> linarith only [hz.1, hz.2, heeta, horder]
  have hpBand : Ioo (r - 4 * epsilon) (r + 4 * epsilon) ⊆
      Icc (ell - eta) (r + eta) := by
    intro z hz
    constructor <;> linarith only [hz.1, hz.2, heeta, horder]
  have hmCap : Ioo (ell - 4 * epsilon) (ell + 4 * epsilon) ⊆
      Ioo (ell - wm) (ell + wm) := by
    intro z hz
    constructor <;> linarith only [hz.1, hz.2, hewm]
  have hpCap : Ioo (r - 4 * epsilon) (r + 4 * epsilon) ⊆
      Ioo (r - wp) (r + wp) := by
    intro z hz
    constructor <;> linarith only [hz.1, hz.2, hewp]
  have hband : ell - eta < r + eta := by linarith only [horder, heta]
  obtain ⟨Rm, hRm, cm, hcm, hcme, hcmrange, hcmout, Dm, Gm, Tm,
      hmSource, hmTarget, hmValue, hmInverse, hTmR, hTmiR, hTmhR, hTmihR,
      hTmsR, hboundm⟩ :=
    exists_stackTubeEndFamily Tm0 hTm hTmi hTmh c (ell - eta) (r + eta)
      (ell - 4 * epsilon) (ell + 4 * epsilon) hP hband hc hce hmBand
      (fun _ hp => hTms ⟨hmCap hp.1, hp.2⟩)
      (fun z hz q => hmcircle z (hmCap hz) q)
      (ell - 3 * epsilon) (ell + 3 * epsilon)
      (by linarith only [he]) (by linarith only [he]) (by linarith only [he])
  obtain ⟨Rp, hRp, cbar, hcb, hcbe, hcbrange, hcbout, D, G, Tp,
      hpSource, hpTarget, hpValue, hpInverse, hTpR, hTpiR, hTphR, hTpihR,
      hTpsR, hboundp⟩ :=
    exists_stackTubeEndFamily Tp0 hTp hTpi hTph cm (ell - eta) (r + eta)
      (r - 4 * epsilon) (r + 4 * epsilon) hP hband hcm hcme hpBand
      (fun _ hp => hTps ⟨hpCap hp.1, hp.2⟩)
      (by intro z hz q; rw [hcmrange]; exact hpcircle z (hpCap hz) q)
      (r - 3 * epsilon) (r + 3 * epsilon)
      (by linarith only [he]) (by linarith only [he]) (by linarith only [he])
  have hmClosed (z : ℝ) (hz : z ∈ Icc (ell - 3 * epsilon) (ell + 3 * epsilon)) :
      z ∈ Icc (ell - eta) (r + eta) := by
    apply hmBand
    constructor <;> linarith only [hz.1, hz.2, he]
  have hpClosed (z : ℝ) (hz : z ∈ Icc (r - 3 * epsilon) (r + 3 * epsilon)) :
      z ∈ Icc (ell - eta) (r + eta) := by
    apply hpBand
    constructor <;> linarith only [hz.1, hz.2, he]
  have hmFilled : Icc (ell - 3 * epsilon) (ell + 3 * epsilon) ×ˢ
      closedBall (0 : E2) 1 ⊆ Tm.source := by
    intro p hp
    exact hTmsR ⟨⟨by linarith only [hp.1.1, he], by linarith only [hp.1.2, he]⟩, hp.2⟩
  have hpFilled : Icc (r - 3 * epsilon) (r + 3 * epsilon) ×ˢ
      closedBall (0 : E2) 1 ⊆ Tp.source := by
    intro p hp
    exact hTpsR ⟨⟨by linarith only [hp.1.1, he], by linarith only [hp.1.2, he]⟩, hp.2⟩
  have hboundm' (z : ℝ) (hz : z ∈ Icc (ell - 3 * epsilon) (ell + 3 * epsilon))
      (q : E2) (hq : q ∈ sphere (0 : E2) 1) : Tm (z, q) = G.chart (z, q) := by
    have hout : z ∉ Ioo (r - 4 * epsilon) (r + 4 * epsilon) := by
      intro hz'
      linarith only [hz.2, hz'.1, hsep, he]
    calc
      Tm (z, q) = Gm.chart (z, q) := hboundm z hz q hq
      _ = (z, cm z ⟨q, hq⟩) := by
        rw [Gm.chart_apply, Dm.chart_boundary z (hmClosed z hz) ⟨q, hq⟩]
      _ = (z, cbar z ⟨q, hq⟩) := by rw [hcbout z hout]
      _ = G.chart (z, q) := by
        rw [G.chart_apply, D.chart_boundary z (hmClosed z hz) ⟨q, hq⟩]
  have hGs : Icc (ell - eta) (r + eta) ×ˢ closedBall (0 : E2) 1 ⊆ G.chart.source := by
    intro p hp
    exact G.mem_source hp.1
      (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp.2).trans_lt G.one_lt_radius))
  obtain ⟨dm, hdm, hdmq, PhiM, _Sm, _hSm, _hSmsub, _hMs, _hMis, _hMfix, _hMh,
      hMcircle, _hQms, hQmt, hQm, hQmi, hQmh, _hQmih, hMproduct, hMmatch⟩ :=
    exists_stackAnnularMatchedChart Tm G.chart
      hTmR hTmiR G.smooth G.smooth_symm hTmhR (fun p _ => by rw [G.chart_apply])
      (ell - 3 * epsilon) (ell - 2 * epsilon) (ell + 2 * epsilon) (ell + 3 * epsilon)
      (by linarith only [he]) (by linarith only [he]) (by linarith only [he])
      hmFilled (fun p hp => hGs ⟨hmClosed p.1 hp.1, hp.2⟩) hboundm'
  let Qm := PhiM.toHomeomorph.toOpenPartialHomeomorph.trans G.chart
  have hQmsBand : Icc (ell - eta) (r + eta) ×ˢ closedBall (0 : E2) 1 ⊆ Qm.source :=
    (hMproduct _).2.2.2.2.2.2 hGs
  have hQmbound (z : ℝ) (hz : z ∈ Icc (r - 3 * epsilon) (r + 3 * epsilon))
      (q : E2) (hq : q ∈ sphere (0 : E2) 1) : Tp (z, q) = Qm (z, q) := by
    change Tp (z, q) = G.chart (PhiM (z, q))
    rw [(hMcircle z q hq).1]
    exact hboundp z hz q hq
  obtain ⟨dp, hdp, hdpq, PhiP, Sp, _hSp, hSpsub, _hPs, _hPis, hPfix, _hPh,
      hPcircle, hQs, hQt, hQ, hQi, hQh, hQih, hPproduct, hPmatch⟩ :=
    exists_stackAnnularMatchedChart Tp Qm hTpR hTpiR hQm hQmi hTphR hQmh
      (r - 3 * epsilon) (r - 2 * epsilon) (r + 2 * epsilon) (r + 3 * epsilon)
      (by linarith only [he]) (by linarith only [he]) (by linarith only [he])
      hpFilled (fun p hp => hQmsBand ⟨hpClosed p.1 hp.1, hp.2⟩) hQmbound
  let Q := PhiP.toHomeomorph.toOpenPartialHomeomorph.trans Qm
  have hPfixm (p : P) (hp : p.1 ∈ Icc (ell - 3 * epsilon) (ell + 3 * epsilon)) :
      PhiP p = p ∧ PhiP.symm p = p := by
    apply hPfix
    intro hmem
    have hh := (hSpsub hmem).1.1
    linarith only [hp.2, hh, hsep, he]
  refine ⟨epsilon, min dm dp, he, heeta, hewm, hewp, hsep,
    lt_min hdm hdp, (min_le_left dm dp).trans_lt hdmq, Rm, Rp, hRm, hRp,
    cbar, hcb, hcbe, (fun z => (hcbrange z).trans (hcmrange z)), ?_, D, G, Tm, Tp, Q,
    hmSource, hmTarget, hmValue, hmInverse, hTmR, hTmiR, hTmhR, hTmihR, hmFilled,
    hpSource, hpTarget, hpValue, hpInverse, hTpR, hTpiR, hTphR, hTpihR, hpFilled,
    hQt.trans hQmt, hQ, hQi, hQh, hQih, (hPproduct _).2.2.2.2.2.2 hQmsBand,
    ?_, ?_, ?_, ?_⟩
  · intro z hz q
    rw [hcbout z (fun hp => hz (Or.inr hp)), hcmout z (fun hm => hz (Or.inl hm))]
  · intro J
    rcases hMproduct J with ⟨_, _, _, _, hmb, hmcb, _⟩
    rcases hPproduct J with ⟨_, _, _, _, hpb, hpcb, _⟩
    exact ⟨hpb.trans hmb, hpcb.trans hmcb⟩
  · intro z q hq
    change G.chart (PhiM (PhiP (z, q))) = G.chart (z, q)
    rw [(hPcircle z q hq).1, (hMcircle z q hq).1]
  · intro z hz x hx
    have hz3 : z ∈ Icc (ell - 3 * epsilon) (ell + 3 * epsilon) := by
      constructor <;> linarith only [hz.1, hz.2, he]
    have hz2 : z ∈ Icc (ell - 2 * epsilon) (ell + 2 * epsilon) := by
      constructor <;> linarith only [hz.1, hz.2, he]
    have hm := hMmatch z hz2 x (hx.le.trans (min_le_left _ _))
    have hfix := (hPfixm (z, x) hz3).1
    constructor
    · rw [hQs]
      change PhiP (z, x) ∈ Qm.source
      rw [hfix]
      exact hm.1
    · change Qm (PhiP (z, x)) = _
      rw [hfix]
      exact hm.2
  · intro z hz x hx
    apply hPmatch z _ x (hx.le.trans (min_le_right _ _))
    constructor <;> linarith only [hz.1, hz.2, he]

end PoincareConjecture.M25.Topology3D
