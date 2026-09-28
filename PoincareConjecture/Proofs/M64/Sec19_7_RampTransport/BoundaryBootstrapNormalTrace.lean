import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNormalChart
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceHalfDisk












set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ}
local notation "Target" => EuclideanSpace ℝ (Fin (n + 1))





theorem halfDisk_real_trace_tangent {R : ℝ} {H : ℂ → Target}
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    {c : ℝ → Target} {I : Set ℝ} (hI : IsOpen I)
    (hc : ContDiffOn ℝ ∞ c I) {sigma : ℝ → ℝ} (hsigma : ContDiff ℝ 1 sigma)
    (htrace : ∀ s : ℝ, |s| ≤ R → H (s : ℂ) = c (sigma s))
    {s : ℝ} (hs : |s| < R) (hsI : sigma s ∈ I) :
    fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) (s : ℂ) 1 =
      deriv sigma s • deriv c (sigma s) := by
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  have hreal (t : ℝ) (ht : |t| ≤ R) : (t : ℂ) ∈ K := by
    exact ⟨by simpa only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      using ht, by simp⟩
  have hnear : ∀ᶠ t : ℝ in 𝓝 s, (t : ℂ) ∈ K := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hs)] with t ht
    exact hreal t (abs_lt.mpr ht).le
  have hHd := (hH (s : ℂ) (hreal s hs.le)).differentiableWithinAt (by norm_num)
  have hd := hHd.hasFDerivWithinAt.comp_hasDerivAt s Complex.ofRealCLM.hasDerivAt hnear
  have hcd := (hc.contDiffAt (hI.mem_nhds hsI)).differentiableAt (by simp)
  have hdc := hcd.hasDerivAt.scomp s (hsigma.differentiable (by norm_num) s).hasDerivAt
  have heq : (fun t : ℝ => H (t : ℂ)) =ᶠ[𝓝 s] (fun t => c (sigma t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hs)] with t ht
    exact htrace t (abs_lt.mpr ht).le
  have hd' : HasDerivAt (fun t : ℝ => H (t : ℂ))
      (fderivWithin ℝ H K (s : ℂ) 1) s := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one] using hd
  exact hd'.unique (hdc.congr_of_eventuallyEq heq)





theorem metric_normal_axis_zero
    (B : Target →L[ℝ] Target →L[ℝ] ℝ) (L : Target →L[ℝ] Target)
    (tau v : Target) {a : ℝ} (ha : a ≠ 0) (hpos : 0 < B tau tau)
    (htangent : L (EuclideanSpace.single 0 1) = tau)
    (hnormal : ∀ w : Target, w 0 = 0 → B tau (L w) = 0)
    (hconf : B (a • tau) (L v) = 0) : v 0 = 0 := by
  let w := v - v 0 • EuclideanSpace.single 0 1
  have hw : w 0 = 0 := by simp [w]
  have hv : v = v 0 • EuclideanSpace.single 0 1 + w := by
    dsimp only [w]
    abel
  have hsplit : B tau (L v) = v 0 * B tau tau := by
    calc
      B tau (L v) = B tau (L (v 0 • EuclideanSpace.single 0 1 + w)) :=
        congrArg (fun z => B tau (L z)) hv
      _ = v 0 * B tau tau := by
        simp only [map_add, map_smul, htangent, hnormal w hw, smul_eq_mul, add_zero]
  have hzero : a * (v 0 * B tau tau) = 0 := by
    simpa only [map_smul, smul_apply, smul_eq_mul, hsplit] using hconf
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left ha)).resolve_right hpos.ne'





theorem exists_metric_normal_mixed_trace {R : ℝ} (hR : 0 < R)
    {H : ℂ → Target}
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    (hHs : ContDiffOn ℝ ∞ H (ball (0 : ℂ) R ∩ {z | 0 < z.im}))
    {c : ℝ → Target} {I : Set ℝ} (hI : IsOpen I)
    (hc : ContDiffOn ℝ ∞ c I) {sigma : ℝ → ℝ} (hsigma : ContDiff ℝ 1 sigma)
    (hsigma0 : sigma 0 ∈ I)
    {U : Set Target} (hU : IsOpen U)
    (G : Target → Target →L[ℝ] Target →L[ℝ] ℝ)
    (hG : ContDiffOn ℝ ∞ G U) (hcU : MapsTo c I U)
    (hpos : ∀ t ∈ I, 0 < G (c t) (deriv c t) (deriv c t))
    (htrace : ∀ s : ℝ, |s| ≤ R → H (s : ℂ) = c (sigma s))
    (himm : ∀ s : ℝ, |s| ≤ R → Function.Injective
      (fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) (s : ℂ)))
    (hconf : ∀ s : ℝ, |s| ≤ R →
      G (H (s : ℂ))
        (fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) (s : ℂ) 1)
        (fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) (s : ℂ) Complex.I) = 0) :
    ∃ (Phi : OpenPartialHomeomorph Target Target) (d : ℝ),
      0 < d ∧ d < R ∧ Phi.target ⊆ U ∧
      ContDiffOn ℝ ∞ Phi Phi.source ∧ ContDiffOn ℝ ∞ Phi.symm Phi.target ∧
      MapsTo H (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) Phi.target ∧
      ContDiffOn ℝ 1 (Phi.symm ∘ H) (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) ∧
      ContDiffOn ℝ ∞ (Phi.symm ∘ H) (ball (0 : ℂ) d ∩ {z | 0 < z.im}) ∧
      ∀ s : ℝ, |s| ≤ d →
        (∀ j : Fin (n + 1), j ≠ 0 → (Phi.symm (H (s : ℂ))) j = 0) ∧
        (fderivWithin ℝ (Phi.symm ∘ H)
          (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) (s : ℂ) Complex.I) 0 = 0 := by
  let J : Set ℝ := (fun t => sigma 0 + t) ⁻¹' I
  let c0 : ℝ → Target := fun t => c (sigma 0 + t)
  have hJ : IsOpen J := hI.preimage (continuous_const.add continuous_id)
  have h0J : 0 ∈ J := by simpa only [J, mem_preimage, add_zero] using hsigma0
  have hc0 : ContDiffOn ℝ ∞ c0 J :=
    hc.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ ht => ht)
  have hdc0 (t : ℝ) (ht : t ∈ J) : deriv c0 t = deriv c (sigma 0 + t) := by
    have hcd := (hc.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)
    have hd := hcd.hasDerivAt.scomp t ((hasDerivAt_id t).const_add (sigma 0))
    simpa only [c0, Function.comp_def, one_smul] using hd.deriv
  have hpos0 (t : ℝ) (ht : t ∈ J) : 0 < G (c0 t) (deriv c0 t) (deriv c0 t) := by
    rw [hdc0 t ht]
    exact hpos _ ht
  obtain ⟨Phi, hPhi0, hPhiU, hPhiBase, hPhi, hPhiInv, _haxis,
      htangent, hnormal, haxisInv⟩ :=
    m64_exists_smooth_metric_normal_chart hJ h0J hc0 hU G hG
      (fun _ ht => hcU ht) hpos0
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  have hzeroK : (0 : ℂ) ∈ K := ⟨mem_closedBall_self hR.le, by simp⟩
  have hH0 : H 0 = c0 0 := by
    simpa only [Complex.ofReal_zero, c0, add_zero] using htrace 0 (by simpa using hR.le)
  have hH0target : H 0 ∈ Phi.target := by
    rw [hH0, ← hPhiBase]
    exact Phi.map_source hPhi0
  obtain ⟨rho, hrho, hnearH⟩ := Metric.mem_nhdsWithin_iff.mp
    ((hH.continuousOn 0 hzeroK).preimage_mem_nhdsWithin
      (Phi.open_target.mem_nhds hH0target))
  have hsingle (t : ℝ) : (EuclideanSpace.single 0 t : Target) =
      t • EuclideanSpace.single 0 1 := by
    ext j
    by_cases hj : j = 0 <;> simp [hj]
  have haxisCont : Continuous (fun s => (EuclideanSpace.single 0 (sigma s - sigma 0) : Target)) :=
    ((hsigma.continuous.sub continuous_const).smul continuous_const).congr
      (fun s => (hsingle (sigma s - sigma 0)).symm)
  have haxisZero : (EuclideanSpace.single 0 (sigma 0 - sigma 0) : Target) = 0 := by
    rw [hsingle, sub_self, zero_smul]
  have hnearAxis : ∀ᶠ s : ℝ in 𝓝 0,
      (EuclideanSpace.single 0 (sigma s - sigma 0) : Target) ∈ Phi.source :=
    haxisCont.continuousAt.preimage_mem_nhds
      (by simpa only [haxisZero] using Phi.open_source.mem_nhds hPhi0)
  have hnearI : ∀ᶠ s : ℝ in 𝓝 0, sigma s ∈ I :=
    hsigma.continuous.continuousAt.preimage_mem_nhds (hI.mem_nhds hsigma0)
  obtain ⟨eta, heta, hnearLabel⟩ := Metric.mem_nhds_iff.mp (hnearAxis.and hnearI)
  let d := min R (min rho eta) / 2
  have hd : 0 < d := half_pos (lt_min hR (lt_min hrho heta))
  have hdR : d < R := by
    have h := min_le_left R (min rho eta)
    dsimp only [d] at *
    linarith
  have hdrho : d < rho := by
    have h := (min_le_right R (min rho eta)).trans (min_le_left rho eta)
    dsimp only [d] at *
    linarith
  have hdeta : d < eta := by
    have h := (min_le_right R (min rho eta)).trans (min_le_right rho eta)
    dsimp only [d] at *
    linarith
  let Kd := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
  let Wd := ball (0 : ℂ) d ∩ {z | 0 < z.im}
  have hsub : Kd ⊆ K := fun z hz =>
    ⟨closedBall_subset_closedBall hdR.le hz.1, hz.2⟩
  have hWsub : Wd ⊆ ball (0 : ℂ) R ∩ {z | 0 < z.im} := fun z hz =>
    ⟨ball_subset_ball hdR.le hz.1, hz.2⟩
  have hWK : Wd ⊆ Kd := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hmap : MapsTo H Kd Phi.target := by
    intro z hz
    apply hnearH
    refine ⟨?_, hsub hz⟩
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz.1).trans_lt hdrho)
  have hlabel (s : ℝ) (hs : |s| ≤ d) :
      (EuclideanSpace.single 0 (sigma s - sigma 0) : Target) ∈ Phi.source ∧ sigma s ∈ I := by
    apply hnearLabel
    simpa only [mem_ball_zero_iff, Real.norm_eq_abs] using hs.trans_lt hdeta
  let u := Phi.symm ∘ H
  have hu : ContDiffOn ℝ 1 u Kd :=
    (hPhiInv.of_le (by simp)).comp (hH.mono hsub) hmap
  have hus : ContDiffOn ℝ ∞ u Wd :=
    hPhiInv.comp (hHs.mono hWsub) (fun z hz => hmap (hWK hz))
  have huaxis (s : ℝ) (hs : |s| ≤ d) :
      u (s : ℂ) = EuclideanSpace.single 0 (sigma s - sigma 0) := by
    change Phi.symm (H (s : ℂ)) = _
    rw [htrace s (hs.trans hdR.le)]
    have heq : c0 (sigma s - sigma 0) = c (sigma s) := by
      dsimp only [c0]
      congr 1
      ring
    rw [← heq]
    exact haxisInv _ (hlabel s hs).1
  refine ⟨Phi, d, hd, hdR, hPhiU, hPhi, hPhiInv, hmap, hu, hus, ?_⟩
  intro s hs
  have hsK : (s : ℂ) ∈ Kd := by
    exact ⟨by simpa only [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      using hs, by simp⟩
  have hsR : |s| < R := hs.trans_lt hdR
  have hfirst := halfDisk_real_trace_tangent hH hI hc hsigma htrace hsR (hlabel s hs).2
  have hsigmane : deriv sigma s ≠ 0 := by
    intro hz
    have hcol : fderivWithin ℝ H K (s : ℂ) 1 = 0 := by
      rw [hfirst, hz, zero_smul]
    have hone := himm s hsR.le (hcol.trans (map_zero _).symm)
    exact one_ne_zero hone
  constructor
  · intro j hj
    change u (s : ℂ) j = 0
    rw [huaxis s hs]
    simp [hj]
  · have huniq := (M65StrictTrace.halfDisk_differential_domain hd).2.2.1
    have hdu := (hu (s : ℂ) hsK).differentiableWithinAt (by norm_num)
    have hPhiAt := hPhi.contDiffAt (Phi.open_source.mem_nhds (Phi.map_target (hmap hsK)))
    have hPhiD := (hPhiAt.differentiableAt (by simp)).hasFDerivAt
    have hchain := hPhiD.comp_hasFDerivWithinAt (s : ℂ) hdu.hasFDerivWithinAt
    have heq : EqOn H (Phi ∘ u) Kd := fun z hz => (Phi.right_inv (hmap hz)).symm
    have hchainH := (hchain.congr' heq hsK).fderivWithin (huniq _ hsK)
    have hrestrict := fderivWithin_subset hsub (huniq _ hsK)
      ((hH (s : ℂ) (hsub hsK)).differentiableWithinAt (by norm_num))
    rw [hrestrict] at hchainH
    have hnormalColumn := congrArg (fun D : ℂ →L[ℝ] Target => D Complex.I) hchainH
    change fderivWithin ℝ H K (s : ℂ) Complex.I =
      fderiv ℝ Phi (u (s : ℂ)) (fderivWithin ℝ u Kd (s : ℂ) Complex.I) at hnormalColumn
    rw [huaxis s hs] at hnormalColumn
    have htJ : sigma s - sigma 0 ∈ J := by
      change sigma 0 + (sigma s - sigma 0) ∈ I
      convert (hlabel s hs).2 using 1
      ring
    have hcurve : c0 (sigma s - sigma 0) = c (sigma s) := by
      dsimp only [c0]
      congr 1
      ring
    have hcurveDeriv : deriv c0 (sigma s - sigma 0) = deriv c (sigma s) := by
      rw [hdc0 _ htJ]
      congr 1
      ring
    apply metric_normal_axis_zero (G (c0 (sigma s - sigma 0)))
      (fderiv ℝ Phi (EuclideanSpace.single 0 (sigma s - sigma 0)))
      (deriv c0 (sigma s - sigma 0))
      (fderivWithin ℝ u Kd (s : ℂ) Complex.I) hsigmane (hpos0 _ htJ)
      (htangent _ htJ) (hnormal _ htJ)
    have hcross := hconf s hsR.le
    rw [htrace s hsR.le, hfirst, hnormalColumn] at hcross
    simpa only [hcurve, hcurveDeriv] using hcross

end PoincareConjecture.M64.RampTransport
