import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMatching










set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)


theorem exists_stackTwoCapMatchedChart
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (Cm Cp : SurgeryCapTag psi u)
    (horder : Cm.cutHeight + Cm.sign * Cm.removal <
      Cp.cutHeight + Cp.sign * Cp.removal)
    (hP : PlanarSchoenfliesService) (eta : ℝ) (heta : 0 < eta)
    (c : ℝ → UnitCircle → E2)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => c p.1 p.2))
    (hce : ∀ z ∈ Icc (Cm.cutHeight + Cm.sign * Cm.removal - eta)
      (Cp.cutHeight + Cp.sign * Cp.removal + eta), IsPlanarEmbedding (c z))
    (hfull : ∀ z ∈ Icc (Cm.cutHeight + Cm.sign * Cm.removal - eta)
      (Cp.cutHeight + Cp.sign * Cp.removal + eta),
      range (c z) = {x : E2 | (heightPlaneCoordinates u).symm (x, z) ∈
        range (fun q : UnitTwoSphere => psi (q, 0))}) :
    let ell := Cm.cutHeight + Cm.sign * Cm.removal
    let r := Cp.cutHeight + Cp.sign * Cp.removal
    ∃ epsilon delta : ℝ,
      0 < epsilon ∧ epsilon < eta ∧ 8 * epsilon < r - ell ∧
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
              ∃ PhiM PhiP : Diffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) P P ∞,
                ∃ Sm Sp : Set P,
                  let Qm := PhiM.toHomeomorph.toOpenPartialHomeomorph.trans G.chart
                  let Q := PhiP.toHomeomorph.toOpenPartialHomeomorph.trans Qm
                  IsCompact Sm ∧ IsCompact Sp ∧
                  Sm ⊆ Ioo (ell - 3 * epsilon) (ell + 3 * epsilon) ×ˢ univ ∧
                  Sp ⊆ Ioo (r - 3 * epsilon) (r + 3 * epsilon) ×ˢ univ ∧
                  tsupport (fun p : P => PhiM p - p) ⊆ Sm ∧
                  tsupport (fun p : P => PhiM.symm p - p) ⊆ Sm ∧
                  tsupport (fun p : P => PhiP p - p) ⊆ Sp ∧
                  tsupport (fun p : P => PhiP.symm p - p) ⊆ Sp ∧
                  (∀ p ∉ Sm, PhiM p = p ∧ PhiM.symm p = p) ∧
                  (∀ p ∉ Sp, PhiP p = p ∧ PhiP.symm p = p) ∧
                  (∀ p : P,
                    (PhiM p).1 = p.1 ∧ (PhiM.symm p).1 = p.1 ∧
                    (PhiP p).1 = p.1 ∧ (PhiP.symm p).1 = p.1) ∧
                  (∀ z : ℝ, ∀ q ∈ sphere (0 : E2) 1,
                    PhiM (z, q) = (z, q) ∧ PhiM.symm (z, q) = (z, q) ∧
                    PhiP (z, q) = (z, q) ∧ PhiP.symm (z, q) = (z, q)) ∧
                  (∀ p : P, p.1 ∈ Icc (ell - 3 * epsilon) (ell + 3 * epsilon) →
                    PhiP p = p ∧ PhiP.symm p = p) ∧
                  (∀ p : P, p.1 ∈ Icc (r - 3 * epsilon) (r + 3 * epsilon) →
                    PhiM p = p ∧ PhiM.symm p = p) ∧
                  Q.source = PhiP ⁻¹' (PhiM ⁻¹' G.chart.source) ∧
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
                      (z, x) ∈ Q.source ∧ Q (z, x) = stackCapEndChart Cm Rm (z, x)) ∧
                  ∀ z ∈ Icc (r - epsilon) (r + epsilon), ∀ x : E2,
                    |‖x‖ - 1| < delta →
                      (z, x) ∈ Q.source ∧ Q (z, x) = stackCapEndChart Cp Rp (z, x) := by
  let ell := Cm.cutHeight + Cm.sign * Cm.removal
  let r := Cp.cutHeight + Cp.sign * Cp.removal
  have hlr : ell < r := horder
  let wm := Cm.scale * Cm.overlapWidth / 2
  let wp := Cp.scale * Cp.overlapWidth / 2
  have hwm : 0 < wm := div_pos (mul_pos Cm.scale_pos Cm.overlap_pos) (by norm_num)
  have hwp : 0 < wp := div_pos (mul_pos Cp.scale_pos Cp.overlap_pos) (by norm_num)
  let d := min eta (min ((r - ell) / 2) (min wm wp))
  have hd : 0 < d := lt_min heta (lt_min (by linarith only [hlr]) (lt_min hwm hwp))
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
    constructor <;> linarith only [hz.1, hz.2, heeta, hlr]
  have hpBand : Ioo (r - 4 * epsilon) (r + 4 * epsilon) ⊆
      Icc (ell - eta) (r + eta) := by
    intro z hz
    constructor <;> linarith only [hz.1, hz.2, heeta, hlr]
  have hmCap : Ioo (ell - 4 * epsilon) (ell + 4 * epsilon) ⊆
      Ioo (ell - wm) (ell + wm) := by
    intro z hz
    constructor <;> linarith only [hz.1, hz.2, hewm]
  have hpCap : Ioo (r - 4 * epsilon) (r + 4 * epsilon) ⊆
      Ioo (r - wp) (r + wp) := by
    intro z hz
    constructor <;> linarith only [hz.1, hz.2, hewp]
  have hband : ell - eta < r + eta := by linarith only [hlr, heta]
  obtain ⟨Rm, hRm, cm, hcm, hcme, hcmrange, hcmout, Dm, Gm, hboundm, _⟩ :=
    exists_stackCapEndFamily Cm c (ell - eta) (r + eta)
      (ell - 4 * epsilon) (ell + 4 * epsilon) hP hband hc hce hmBand hmCap
      (fun z hz => hfull z (hmBand hz)) (ell - 3 * epsilon) (ell + 3 * epsilon)
      (by linarith only [he]) (by linarith only [he]) (by linarith only [he])
  obtain ⟨Rp, hRp, cbar, hcb, hcbe, hcbrange, hcbout, D, G, hboundp, _⟩ :=
    exists_stackCapEndFamily Cp cm (ell - eta) (r + eta)
      (r - 4 * epsilon) (r + 4 * epsilon) hP hband hcm hcme hpBand hpCap
      (fun z hz => (hcmrange z).trans (hfull z (hpBand hz)))
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
  have hboundm' (z : ℝ) (hz : z ∈ Icc (ell - 3 * epsilon) (ell + 3 * epsilon))
      (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      stackCapEndChart Cm Rm (z, q) = G.chart (z, q) := by
    have hout : z ∉ Ioo (r - 4 * epsilon) (r + 4 * epsilon) := by
      intro hz'
      linarith only [hz.2, hz'.1, hsep, he]
    calc
      stackCapEndChart Cm Rm (z, q) = Gm.chart (z, q) := hboundm z hz q hq
      _ = (z, cm z ⟨q, hq⟩) := by
        rw [Gm.chart_apply, Dm.chart_boundary z (hmClosed z hz) ⟨q, hq⟩]
      _ = (z, cbar z ⟨q, hq⟩) := by rw [hcbout z hout]
      _ = G.chart (z, q) := by
        rw [G.chart_apply, D.chart_boundary z (hmClosed z hz) ⟨q, hq⟩]
  have hGs : Icc (ell - eta) (r + eta) ×ˢ closedBall (0 : E2) 1 ⊆ G.chart.source := by
    intro p hp
    exact G.mem_source hp.1
      (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp.2).trans_lt G.one_lt_radius))
  obtain ⟨_, _, _, _, hTm, hTmi, hTms, hTmh, _⟩ := stackCapEndChart_spec Cm Rm
  obtain ⟨_, _, _, _, hTp, hTpi, hTps, hTph, _⟩ := stackCapEndChart_spec Cp Rp
  obtain ⟨dm, hdm, hdmq, PhiM, Sm, hSm, hSmsub, hMs, hMis, hMfix, hMh,
      hMcircle, hQms, hQmt, hQm, hQmi, hQmh, _hQmih, hMproduct, hMmatch⟩ :=
    exists_stackAnnularMatchedChart (stackCapEndChart Cm Rm) G.chart
      hTm hTmi G.smooth G.smooth_symm hTmh (fun p _ => by rw [G.chart_apply])
      (ell - 3 * epsilon) (ell - 2 * epsilon) (ell + 2 * epsilon) (ell + 3 * epsilon)
      (by linarith only [he]) (by linarith only [he]) (by linarith only [he])
      (fun _ hp => hTms ⟨mem_univ _, hp.2⟩)
      (fun p hp => hGs ⟨hmClosed p.1 hp.1, hp.2⟩) hboundm'
  let Qm := PhiM.toHomeomorph.toOpenPartialHomeomorph.trans G.chart
  have hQmsBand : Icc (ell - eta) (r + eta) ×ˢ closedBall (0 : E2) 1 ⊆ Qm.source :=
    (hMproduct _).2.2.2.2.2.2 hGs
  have hQmbound (z : ℝ) (hz : z ∈ Icc (r - 3 * epsilon) (r + 3 * epsilon))
      (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      stackCapEndChart Cp Rp (z, q) = Qm (z, q) := by
    change stackCapEndChart Cp Rp (z, q) = G.chart (PhiM (z, q))
    rw [(hMcircle z q hq).1]
    exact hboundp z hz q hq
  obtain ⟨dp, hdp, hdpq, PhiP, Sp, hSp, hSpsub, hPs, hPis, hPfix, hPh,
      hPcircle, hQs, hQt, hQ, hQi, hQh, hQih, hPproduct, hPmatch⟩ :=
    exists_stackAnnularMatchedChart (stackCapEndChart Cp Rp) Qm
      hTp hTpi hQm hQmi hTph hQmh
      (r - 3 * epsilon) (r - 2 * epsilon) (r + 2 * epsilon) (r + 3 * epsilon)
      (by linarith only [he]) (by linarith only [he]) (by linarith only [he])
      (fun _ hp => hTps ⟨mem_univ _, hp.2⟩)
      (fun p hp => hQmsBand ⟨hpClosed p.1 hp.1, hp.2⟩) hQmbound
  let Q := PhiP.toHomeomorph.toOpenPartialHomeomorph.trans Qm
  have hPfixm (p : P) (hp : p.1 ∈ Icc (ell - 3 * epsilon) (ell + 3 * epsilon)) :
      PhiP p = p ∧ PhiP.symm p = p := by
    apply hPfix
    intro hmem
    have hh := (hSpsub hmem).1.1
    linarith only [hp.2, hh, hsep, he]
  have hMfixp (p : P) (hp : p.1 ∈ Icc (r - 3 * epsilon) (r + 3 * epsilon)) :
      PhiM p = p ∧ PhiM.symm p = p := by
    apply hMfix
    intro hmem
    have hh := (hSmsub hmem).1.2
    linarith only [hp.1, hh, hsep, he]
  refine ⟨epsilon, min dm dp, he, by linarith only [heeta, he], hsep,
    lt_min hdm hdp, (min_le_left dm dp).trans_lt hdmq, Rm, Rp, hRm, hRp,
    cbar, hcb, hcbe, (fun z => (hcbrange z).trans (hcmrange z)), ?_, D, G,
    PhiM, PhiP, Sm, Sp, hSm, hSp, hSmsub, hSpsub, hMs, hMis, hPs, hPis,
    hMfix, hPfix, ?_, ?_, hPfixm, hMfixp, ?_, hQt.trans hQmt, hQ, hQi,
    hQh, hQih, (hPproduct _).2.2.2.2.2.2 hQmsBand, ?_, ?_, ?_, ?_⟩
  · intro z hz q
    rw [hcbout z (fun hp => hz (Or.inr hp)), hcmout z (fun hm => hz (Or.inl hm))]
  · intro p
    exact ⟨(hMh p).1, (hMh p).2, hPh p⟩
  · intro z q hq
    exact ⟨(hMcircle z q hq).1, (hMcircle z q hq).2, hPcircle z q hq⟩
  · rw [hQs, hQms]
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
