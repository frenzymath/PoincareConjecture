import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsPhaseTransition
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsAnnularEvolution












set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_stackRadializedDiscChart
    (E : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hE : ContDiffOn ℝ ∞ E E.source)
    (hEi : ContDiffOn ℝ ∞ E.symm E.target)
    (hEh : ∀ p ∈ E.source, (E p).1 = p.1)
    (hEs : univ ×ˢ closedBall (0 : E2) 1 ⊆ E.source)
    (hEt : univ ×ˢ closedBall (0 : E2) 1 ⊆ E.target)
    (hEC : MapsTo E (univ ×ˢ sphere (0 : E2) 1)
      (univ ×ˢ sphere (0 : E2) 1))
    (hEiC : MapsTo E.symm (univ ×ˢ sphere (0 : E2) 1)
      (univ ×ˢ sphere (0 : E2) 1))
    (hEiB : MapsTo E.symm (univ ×ˢ ball (0 : E2) 1)
      (univ ×ˢ ball (0 : E2) 1))
    (A a b B : ℝ) (hAa : A < a) (hab : a < b) (hbB : b < B) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧
      ∃ Φ : Diffeomorph 𝓘(ℝ, ℝ × E2) 𝓘(ℝ, ℝ × E2) (ℝ × E2) (ℝ × E2) ∞,
      ∃ S : Set (ℝ × E2),
        let D := Φ.symm.toHomeomorph.toOpenPartialHomeomorph.trans E
        IsCompact S ∧ S ⊆ Ioo A B ×ˢ (univ : Set E2) ∧
        (∀ p, p ∉ S → Φ p = p ∧ Φ.symm p = p) ∧
        (∀ p, (Φ p).1 = p.1 ∧ (Φ.symm p).1 = p.1) ∧
        (∀ z : ℝ, ∀ q ∈ sphere (0 : E2) 1,
          Φ (z, q) = (z, q) ∧ Φ.symm (z, q) = (z, q)) ∧
        D.source = Φ.symm ⁻¹' E.source ∧ D.target = E.target ∧
        ContDiffOn ℝ ∞ D D.source ∧ ContDiffOn ℝ ∞ D.symm D.target ∧
        (univ ×ˢ closedBall (0 : E2) 1 ⊆ D.source) ∧
        (univ ×ˢ closedBall (0 : E2) 1 ⊆ D.target) ∧
        (∀ p ∈ D.source, (D p).1 = p.1) ∧
        (∀ p ∈ D.target, (D.symm p).1 = p.1) ∧
        (∀ J : Set ℝ,
          D '' (J ×ˢ ball (0 : E2) 1) = E '' (J ×ˢ ball 0 1) ∧
          D '' (J ×ˢ closedBall (0 : E2) 1) = E '' (J ×ˢ closedBall 0 1)) ∧
        ∀ z ∈ Icc a b, ∀ x : E2, |‖x‖ - 1| < δ →
          (z, x) ∈ D.source ∧ (z, x) ∈ D.target ∧
          D (z, x) = (z, ‖x‖ • (E (z, (circleDirection x : E2))).2) ∧
          D.symm (z, x) = (z, ‖x‖ • (E.symm (z, (circleDirection x : E2))).2) := by
  have hCs : univ ×ˢ sphere (0 : E2) 1 ⊆ E.source :=
    fun _ hp => hEs ⟨hp.1, sphere_subset_closedBall hp.2⟩
  have hCt : univ ×ˢ sphere (0 : E2) 1 ⊆ E.target :=
    fun _ hp => hEt ⟨hp.1, sphere_subset_closedBall hp.2⟩
  obtain ⟨R, hRs, hRt, hRf, hRif, hR, hRi, hRh, hRn, hRboundary⟩ :=
    exists_stackCircleRadialChart E hE hEi hEh hCs hCt hEC hEiC
  let Q := E.trans R.symm
  obtain ⟨_hQsource, _hQtarget, hQ, _hQi, hQh, hQC, hQfixed, hQnormal⟩ :=
    stackCirclePhaseTransition_spec E R hE hEi hEh hCs hEiB hR hRi hRs
      hRh hRn (fun p hp => (hRboundary p hp).1)
  let g : (ℝ × E2) → E2 := fun p => (Q p).2
  have hfixed (z : ℝ) (q : E2) (hq : q ∈ sphere (0 : E2) 1) : g (z, q) = q :=
    congrArg Prod.snd (hQfixed (z, q) ⟨mem_univ _, hq⟩)
  obtain ⟨d0, hd0, _hd0quarter, e, heq, hes, he, hei, hAnnQ, _hinner⟩ :=
    exists_stackAnnularInterpolationChart g Q.source Q.open_source hQ.snd A a b B
      hAa hab hbB (fun _ hp => hQC ⟨mem_univ _, hp.2⟩)
      (fun z _ q hq => hfixed z q hq)
      (fun z _ q hq => hQnormal z q (mem_sphere_zero_iff_norm.mp hq))
  obtain ⟨rho, _hrho, _hrhoc, _hrhos, hnear, _hrange, hW, hWc, hWt, hWh, hWq, _hcoords⟩ :=
    exists_stackAnnularCutoff g A a b B d0 hAa hab hbB hd0 e heq hes he hei
      (fun z _ q hq => hfixed z q hq)
  obtain ⟨F, _H, S, _hSeq, hSc, hSsub, _hF, _hFi, _hF0, hFh,
      hFiber, _hH, _hHi, hCircle, _hDisc, _hSupport, hFix, _hTrack, hEndpoint, hProduct⟩ :=
    exists_stackAnnularEvolution g A a b B d0 hAa hab hbB hd0 e heq hes he rho
      hnear hW hWc hWt hWh hWq
  let Φ := F 1
  have hΦcircle (z : ℝ) (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      Φ (z, q) = (z, q) ∧ Φ.symm (z, q) = (z, q) := by
    have hf : Φ (z, q) = (z, q) := (hCircle 1 z q (mem_sphere_zero_iff_norm.mp hq)).1
    refine ⟨hf, ?_⟩
    simpa only [Diffeomorph.symm_apply_apply] using (congrArg Φ.symm hf).symm
  have hAnnSource (z : ℝ) (hz : z ∈ Icc a b) (x : E2)
      (hx : |‖x‖ - 1| ≤ d0) : (z, x) ∈ Q.source := by
    apply hAnnQ
    exact ⟨⟨hAa.trans_le hz.1, hz.2.trans_lt hbB⟩, by
      change |‖x‖ - 1| < 2 * d0
      linarith only [hx, hd0]⟩
  have hΦend (z : ℝ) (hz : z ∈ Icc a b) (x : E2)
      (hx : |‖x‖ - 1| ≤ d0) : Φ (z, x) = Q (z, x) :=
    Prod.ext ((hFh 1 (z, x)).1.trans (hQh _ (hAnnSource z hz x hx)).symm)
      ((hFiber 1 z x).1.symm.trans (hEndpoint z hz x hx))
  let D := Φ.symm.toHomeomorph.toOpenPartialHomeomorph.trans E
  have hDs : D.source = Φ.symm ⁻¹' E.source := by
    change univ ∩ Φ.symm ⁻¹' E.source = _
    exact univ_inter _
  have hDt : D.target = E.target := by
    change E.target ∩ E.symm ⁻¹' univ = E.target
    simp only [preimage_univ, inter_univ]
  let K : Set (ℝ × E2) := Icc a b ×ˢ sphere (0 : E2) 1
  let U : Set (ℝ × E2) := {p | |‖(Φ.symm p).2‖ - 1| < d0}
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_sphere (0 : E2) 1)
  have hU : IsOpen U := isOpen_lt
    (Φ.symm.continuous.snd.norm.sub continuous_const).abs continuous_const
  have hKU : K ⊆ U := by
    intro p hp
    change |‖(Φ.symm (p.1, p.2)).2‖ - 1| < d0
    rw [(hΦcircle p.1 p.2 hp.2).2, mem_sphere_zero_iff_norm.mp hp.2]
    simpa only [sub_self, abs_zero] using hd0
  obtain ⟨d, hd, hband⟩ := hK.exists_thickening_subset_open hU hKU
  obtain ⟨δ, hδ, hδmin⟩ := exists_between
    (show (0 : ℝ) < min (1 / 4) d from lt_min (by norm_num) hd)
  have hδquarter : δ < 1 / 4 := (lt_min_iff.mp hδmin).1
  have hδd : δ < d := (lt_min_iff.mp hδmin).2
  have hdist (x : E2) : dist x (circleDirection x : E2) = |‖x‖ - 1| := by
    rw [dist_eq_norm]
    have hsub : x - (circleDirection x : E2) =
        (‖x‖ - 1) • (circleDirection x : E2) := by
      rw [sub_smul, one_smul, circleDirection_norm_smul]
    rw [hsub, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]
  have hpreimage (z : ℝ) (hz : z ∈ Icc a b) (x : E2)
      (hx : |‖x‖ - 1| < δ) : |‖(Φ.symm (z, x)).2‖ - 1| < d0 := by
    apply hband
    apply mem_thickening_iff.mpr
    refine ⟨(z, (circleDirection x : E2)), ⟨hz, (circleDirection x).2⟩, ?_⟩
    simpa only [dist_prod_same_left, hdist] using hx.trans hδd
  have hforward (z : ℝ) (hz : z ∈ Icc a b) (x : E2)
      (hx : |‖x‖ - 1| < δ) : (z, x) ∈ D.source ∧ D (z, x) = R (z, x) := by
    let w := Φ.symm (z, x)
    have hwh : w.1 = z := (hFh 1 (z, x)).2
    have hwform : (z, w.2) = w := Prod.ext hwh.symm rfl
    have hwr : |‖w.2‖ - 1| ≤ d0 := (hpreimage z hz x hx).le
    have hwQ : w ∈ Q.source := hwform ▸ hAnnSource z hz w.2 hwr
    have hmatch : Φ w = Q w := hwform ▸ hΦend z hz w.2 hwr
    have hEw : E w = R (z, x) := by
      calc
        E w = R (Q w) := (R.right_inv hwQ.2).symm
        _ = R (Φ w) := congrArg R hmatch.symm
        _ = R (z, x) := by simp only [w, Diffeomorph.apply_symm_apply]
    refine ⟨?_, hEw⟩
    rw [hDs]
    exact hwQ.1
  refine ⟨δ, hδ, hδquarter, Φ, S, hSc, hSsub, hFix 1, hFh 1, hΦcircle,
    hDs, hDt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hE.comp Φ.symm.contDiff.contDiffOn (fun _ hp => hp.2)
  · exact Φ.contDiff.comp_contDiffOn (hEi.mono inter_subset_left)
  · intro p hp
    rw [hDs]
    apply hEs
    have hh := (hProduct 1 (univ : Set ℝ)).2.2.2
    exact hh ▸ mem_image_of_mem Φ.symm hp
  · rw [hDt]
    exact hEt
  · intro p hp
    exact (hEh (Φ.symm p) hp.2).trans (hFh 1 p).2
  · intro p hp
    have hpE : p ∈ E.target := hDt ▸ hp
    have hh := hEh (E.symm p) (E.map_target hpE)
    rw [E.right_inv hpE] at hh
    exact (hFh 1 (E.symm p)).1.trans hh.symm
  · intro J
    constructor
    · calc
        D '' (J ×ˢ ball (0 : E2) 1) = E '' (Φ.symm '' (J ×ˢ ball 0 1)) :=
          (image_image E Φ.symm _).symm
        _ = E '' (J ×ˢ ball 0 1) := congrArg (image E) (hProduct 1 J).2.2.1
    · calc
        D '' (J ×ˢ closedBall (0 : E2) 1) = E '' (Φ.symm '' (J ×ˢ closedBall 0 1)) :=
          (image_image E Φ.symm _).symm
        _ = E '' (J ×ˢ closedBall 0 1) := congrArg (image E) (hProduct 1 J).2.2.2
  · intro z hz x hx
    obtain ⟨hpDs, hpD⟩ := hforward z hz x hx
    have hpRt : (z, x) ∈ R.target := by
      rw [hRt]
      refine ⟨mem_univ _, norm_pos_iff.mp ?_⟩
      have hn := (abs_lt.mp hx).1
      linarith only [hn, hδquarter]
    have hyform : (z, (R.symm (z, x)).2) = R.symm (z, x) :=
      Prod.ext (hRh (z, x)).2.symm rfl
    have hyn : |‖(R.symm (z, x)).2‖ - 1| < δ := by
      rw [(hRn (z, x)).2]
      exact hx
    obtain ⟨hys, hyeq⟩ := hforward z hz (R.symm (z, x)).2 hyn
    rw [hyform] at hys hyeq
    have hdy : D (R.symm (z, x)) = (z, x) := hyeq.trans (R.right_inv hpRt)
    have hpDt : (z, x) ∈ D.target := hdy ▸ D.map_source hys
    refine ⟨hpDs, hpDt, hpD.trans (hRf (z, x)), ?_⟩
    calc
      D.symm (z, x) = D.symm (D (R.symm (z, x))) := congrArg D.symm hdy.symm
      _ = R.symm (z, x) := D.left_inv hys
      _ = _ := hRif (z, x)

end PoincareConjecture.M25.Topology3D
