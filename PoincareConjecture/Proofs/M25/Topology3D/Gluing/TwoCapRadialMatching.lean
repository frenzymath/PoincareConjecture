import PoincareConjecture.Proofs.M25.Mathlib.MonotoneIntervalChart
import PoincareConjecture.Proofs.M25.Mathlib.InwardRadialExtension
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SchoenfliesRadial

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D.SchoenfliesData

theorem exists_inward_matching_radial_chart
    {ψ : UnitTwoSphere × ℝ → E3}
    (S : SchoenfliesData ψ (1 / 4))
    (hψ : IsCollarEmbedding ψ)
    (sigma : OpenPartialHomeomorph ℝ ℝ)
    {v L c h r0 kappa : ℝ}
    (hh : 0 < h)
    (hleft : v < c - h)
    (hright : c + h < L)
    (hr0 : 0 < r0)
    (hkappa : 0 < kappa)
    (hsource : sigma.source = Ioo v L)
    (htarget : sigma.target = Ioi r0)
    (hsigma : ContDiffOn ℝ ∞ (sigma : ℝ → ℝ) sigma.source)
    (hsigmaDeriv : ∀ s ∈ sigma.source,
      0 < deriv (sigma : ℝ → ℝ) s) :
    let R := S.radial (3 / 4)
    let m := S.radial (3 / 8)
    let Rminus := kappa / sigma (c - h * (3 / 4))
    let rminus := kappa / sigma (c - h * (1 / 2))
    ∃ (tau : OpenPartialHomeomorph ℝ ℝ) (k : ℝ),
      0 < m ∧ m < S.radial (1 / 2) ∧
      S.radial (1 / 2) < R ∧
      0 < rminus ∧ rminus < Rminus ∧
      tau.source = Ioo (-R) R ∧
      tau.target = Ioo (-Rminus) Rminus ∧
      ContDiffOn ℝ ∞ (tau : ℝ → ℝ) tau.source ∧
      ContDiffOn ℝ ∞ tau.symm tau.target ∧
      ContinuousOn (tau : ℝ → ℝ) (Icc (-R) R) ∧
      StrictMonoOn (tau : ℝ → ℝ) (Icc (-R) R) ∧
      (∀ r ∈ tau.source, 0 < deriv (tau : ℝ → ℝ) r) ∧
      tau 0 = 0 ∧ tau.symm 0 = 0 ∧
      (∀ t ∈ Icc (1 / 2 : ℝ) (3 / 4),
        tau (S.radial t) = kappa / sigma (c - h * t)) ∧
      (∀ t ∈ Ico (1 / 2 : ℝ) (3 / 4),
        tau.symm (kappa / sigma (c - h * t)) = S.radial t) ∧
      (∀ r ∈ Icc (-R) R, tau (-r) = -tau r) ∧
      tau '' Ioo 0 R = Ioo 0 Rminus ∧
      0 < tau m ∧
      (∀ r ∈ Icc (-m) m,
        0 < 1 + k * r ^ 2 ∧
        tau r = r / Real.sqrt (1 + k * r ^ 2)) ∧
      (∀ r ∈ Icc (-(tau m)) (tau m),
        0 < 1 - k * r ^ 2 ∧
        tau.symm r = r / Real.sqrt (1 - k * r ^ 2)) ∧
      tau '' Ioo (S.radial (1 / 2)) R = Ioo rminus Rminus ∧
      (∀ y ∈ Ioo rminus Rminus,
        ∃ t ∈ Ioo (1 / 2 : ℝ) (3 / 4),
          tau.symm y = S.radial t ∧
          y = kappa / sigma (c - h * t)) := by
  classical
  let d := S.radial (5 / 16)
  let a := S.radial (3 / 8)
  let b := S.radial (1 / 2)
  let R := S.radial (3 / 4)
  let U := S.radial (7 / 8)
  have hrho := S.contDiffOn_radial hψ (by norm_num)
  have hsub : Icc (5 / 16 : ℝ) (7 / 8) ⊆ Ioo (1 / 4 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmono : StrictMonoOn S.radial (Icc (5 / 16 : ℝ) (7 / 8)) :=
    S.radial_strictMono.mono (fun t ht => Ioo_subset_Ico_self (hsub ht))
  obtain ⟨Rho, hRhos, hRhot, hRhof, _, hRhoi, hRhod⟩ :=
    hmono.exists_smooth_openInterval_chart (by norm_num) (hrho.mono hsub)
      (fun t ht => S.deriv_radial_pos hψ (by norm_num)
        (hsub ⟨ht.1.le, ht.2.le⟩))
  have hd : 0 < d := S.radial_pos _ (by norm_num)
  have hda : d < a := S.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have hab : a < b := S.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have hbR : b < R := S.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have hRU : R < U := S.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have ha : 0 < a := hd.trans hda
  have hb : 0 < b := ha.trans hab
  have hR : 0 < R := hb.trans hbR
  have hRhotarget {r : ℝ} (hr : r ∈ Ioo d U) : r ∈ Rho.target := by
    simpa only [hRhot, d, U] using hr
  have hRhoinv_mem {r : ℝ} (hr : r ∈ Ioo d U) :
      Rho.symm r ∈ Ioo (5 / 16 : ℝ) (7 / 8) := by
    simpa only [hRhos] using Rho.map_target (hRhotarget hr)
  have hRhoinv (t : ℝ) (ht : t ∈ Ioo (5 / 16 : ℝ) (7 / 8)) :
      Rho.symm (S.radial t) = t := by
    simpa only [hRhof] using Rho.left_inv (hRhos.symm ▸ ht)
  let height : ℝ → ℝ := fun r => c - h * Rho.symm r
  have hheight_mem {r : ℝ} (hr : r ∈ Ioo d U) : height r ∈ sigma.source := by
    have ht := hRhoinv_mem hr
    have ht0 : 0 < Rho.symm r := by linarith [ht.1]
    have ht1 : Rho.symm r < 1 := by linarith [ht.2]
    rw [hsource]
    change v < c - h * Rho.symm r ∧ c - h * Rho.symm r < L
    constructor
    · have hmul := mul_lt_mul_of_pos_left ht1 hh
      linarith
    · have hmul := mul_pos hh ht0
      linarith
  have hsigma_pos {r : ℝ} (hr : r ∈ Ioo d U) : 0 < sigma (height r) := by
    have hs : r0 < sigma (height r) := by
      simpa only [htarget, mem_Ioi] using sigma.map_source (hheight_mem hr)
    exact hr0.trans hs
  let f : ℝ → ℝ := fun r => kappa / sigma (height r)
  have hf : ContDiffOn ℝ ∞ f (Ioo d U) := by
    apply isOpen_Ioo.contDiffOn_iff.mpr
    intro r hr
    have hi : ContDiffAt ℝ ∞ (Rho.symm : ℝ → ℝ) r :=
      hRhoi.contDiffAt (Rho.open_target.mem_nhds (hRhotarget hr))
    have hhgt : ContDiffAt ℝ ∞ height r :=
      contDiffAt_const.sub (contDiffAt_const.mul hi)
    have hs := (hsigma.contDiffAt
      (sigma.open_source.mem_nhds (hheight_mem hr))).comp r hhgt
    exact contDiffAt_const.div hs (hsigma_pos hr).ne'
  have hfpos : ∀ r ∈ Ioo d U, 0 < f r :=
    fun r hr => div_pos hkappa (hsigma_pos hr)
  have hfderiv : ∀ r ∈ Icc a R, 0 < deriv f r := by
    intro r hr
    have hr' : r ∈ Ioo d U := ⟨hda.trans_le hr.1, hr.2.trans_lt hRU⟩
    have hi : HasDerivAt (Rho.symm : ℝ → ℝ) (deriv (Rho.symm : ℝ → ℝ) r) r :=
      ((hRhoi.contDiffAt (Rho.open_target.mem_nhds (hRhotarget hr'))).differentiableAt
        (by simp)).hasDerivAt
    have hhgt : HasDerivAt height (-(h * deriv (Rho.symm : ℝ → ℝ) r)) r :=
      (hi.const_mul h).const_sub c
    have hs : HasDerivAt (fun s : ℝ => sigma (height s))
        (deriv (sigma : ℝ → ℝ) (height r) *
          (-(h * deriv (Rho.symm : ℝ → ℝ) r))) r :=
      ((hsigma.contDiffAt (sigma.open_source.mem_nhds
        (hheight_mem hr'))).differentiableAt (by simp)).hasDerivAt.comp r hhgt
    have hcalc : HasDerivAt f
        (kappa * (-(deriv (sigma : ℝ → ℝ) (height r) *
          (-(h * deriv (Rho.symm : ℝ → ℝ) r))) / sigma (height r) ^ 2)) r := by
      simpa only [f, div_eq_mul_inv, Pi.inv_apply] using
        (hs.inv (hsigma_pos hr').ne').const_mul kappa
    have hneg : deriv (sigma : ℝ → ℝ) (height r) *
        (-(h * deriv (Rho.symm : ℝ → ℝ) r)) < 0 :=
      mul_neg_of_pos_of_neg (hsigmaDeriv _ (hheight_mem hr'))
        (neg_lt_zero.mpr (mul_pos hh (hRhod r (hRhotarget hr')).1))
    rw [hcalc.deriv]
    exact mul_pos hkappa (div_pos (neg_pos.mpr hneg) (sq_pos_of_pos (hsigma_pos hr')))
  have hclosed (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
      S.radial t ∈ Icc b R := by
    have ht' : t ∈ Ico (1 / 4 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    exact ⟨S.radial_strictMono.monotoneOn (by norm_num) ht' ht.1,
      S.radial_strictMono.monotoneOn ht' (by norm_num) ht.2⟩
  have hformula (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
      f (S.radial t) = kappa / sigma (c - h * t) := by
    dsimp only [f, height]
    rw [hRhoinv t (by constructor <;> linarith [ht.1, ht.2])]
  obtain ⟨tau, k, htaus, htaut, htauf, htaui, htauc, htaum, htaud,
    hzero, hizero, heq, hodd, hhalf, ham, hcenter, hicenter⟩ :=
      Real.exists_smooth_inward_radial_chart hd hda hab hbR hRU hf hfpos hfderiv
  have hmatch (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
      tau (S.radial t) = kappa / sigma (c - h * t) :=
    (heq (hclosed t ht)).trans (hformula t ht)
  have hfb : f b = kappa / sigma (c - h * (1 / 2)) :=
    hformula (1 / 2) (by norm_num)
  have hfR : f R = kappa / sigma (c - h * (3 / 4)) :=
    hformula (3 / 4) (by norm_num)
  have htaub : tau b = kappa / sigma (c - h * (1 / 2)) :=
    hmatch (1 / 2) (by norm_num)
  have htauR : tau R = kappa / sigma (c - h * (3 / 4)) :=
    hmatch (3 / 4) (by norm_num)
  have hrminus : 0 < kappa / sigma (c - h * (1 / 2)) := by
    rw [← hfb]
    exact hfpos b ⟨hda.trans hab, hbR.trans hRU⟩
  have horder : kappa / sigma (c - h * (1 / 2)) <
      kappa / sigma (c - h * (3 / 4)) := by
    rw [← htaub, ← htauR]
    exact htaum ⟨by linarith, hbR.le⟩ ⟨by linarith, le_rfl⟩ hbR
  have hinvmatch (t : ℝ) (ht : t ∈ Ico (1 / 2 : ℝ) (3 / 4)) :
      tau.symm (kappa / sigma (c - h * t)) = S.radial t := by
    have ht' : t ∈ Ico (1 / 4 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have htau : S.radial t ∈ tau.source := by
      rw [htaus]
      exact ⟨by linarith [S.radial_pos t ht'],
        S.radial_strictMono ht' (by norm_num) ht.2⟩
    rw [← hmatch t ⟨ht.1, ht.2.le⟩]
    exact tau.left_inv htau
  have hsubb : Icc b R ⊆ Icc (-R) R :=
    fun r hr => ⟨by linarith [hr.1], hr.2⟩
  have himage : tau '' Ioo b R =
      Ioo (kappa / sigma (c - h * (1 / 2))) (kappa / sigma (c - h * (3 / 4))) := by
    simpa only [htaub, htauR] using
      (htauc.mono hsubb).image_Ioo_of_strictMonoOn hbR.le (htaum.mono hsubb)
  have hrhoimage : S.radial '' Ioo (1 / 2 : ℝ) (3 / 4) = Ioo b R := by
    have hsub' : Icc (1 / 2 : ℝ) (3 / 4) ⊆ Ioo (1 / 4 : ℝ) 1 := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    exact (hrho.continuousOn.mono hsub').image_Ioo_of_strictMonoOn (by norm_num)
      (S.radial_strictMono.mono (fun t ht => Ioo_subset_Ico_self (hsub' ht)))
  refine ⟨tau, k, ha, hab, hbR, hrminus, horder, htaus,
    by simpa only [hfR] using htaut, htauf, htaui, htauc, htaum, htaud,
    hzero, hizero, hmatch, hinvmatch, hodd, by simpa only [hfR] using hhalf,
    ham, hcenter, hicenter, himage, ?_⟩
  intro y hy
  obtain ⟨r, hr, hry⟩ := himage.symm ▸ hy
  obtain ⟨t, ht, htr⟩ := hrhoimage.symm ▸ hr
  have hrs : r ∈ tau.source := by
    rw [htaus]
    exact ⟨by linarith [hr.1], hr.2⟩
  refine ⟨t, ht, ?_, ?_⟩
  · calc
      tau.symm y = r := by rw [← hry, tau.left_inv hrs]
      _ = S.radial t := htr.symm
  · calc
      y = tau r := hry.symm
      _ = tau (S.radial t) := congrArg tau htr.symm
      _ = kappa / sigma (c - h * t) := hmatch t ⟨ht.1.le, ht.2.le⟩

end PoincareConjecture.M25.Topology3D.SchoenfliesData
