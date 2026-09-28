import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SchoenfliesRadial
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SphereRadialExtension
import PoincareConjecture.Proofs.M25.Mathlib.MonotoneIntervalChart
import PoincareConjecture.Proofs.M25.Mathlib.InwardRadialExtension
import PoincareConjecture.Proofs.M25.Mathlib.RadialBallChart

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D.SchoenfliesData

theorem exists_sameHeight_ball_chart
    (hD : DiffSphereIsotopyService)
    {psi1 psi2 : UnitTwoSphere × ℝ → E3}
    (S1 : SchoenfliesData psi1 (1 / 4))
    (S2 : SchoenfliesData psi2 (1 / 4))
    (hpsi1 : IsCollarEmbedding psi1)
    (hpsi2 : IsCollarEmbedding psi2) :
    ∃ Z : OpenPartialHomeomorph E3 E3,
      Z.source = ball 0 (S1.radial (3 / 4)) ∧
      Z.target = ball 0 (S2.radial (3 / 4)) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ Z Z.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ Z.symm Z.target ∧
      Z 0 = 0 ∧ Z.symm 0 = 0 ∧
      (∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (1 / 2) (3 / 4) →
        Z (S1.radial t • (S1.boundary_map q).val) =
          S2.radial t • (S2.boundary_map q).val) ∧
      (∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Ico (1 / 2) (3 / 4) →
        Z.symm (S2.radial t • (S2.boundary_map q).val) =
          S1.radial t • (S1.boundary_map q).val) ∧
      Z '' {x : E3 |
          S1.radial (1 / 2) < ‖x‖ ∧ ‖x‖ < S1.radial (3 / 4)} =
        {y : E3 |
          S2.radial (1 / 2) < ‖y‖ ∧ ‖y‖ < S2.radial (3 / 4)} ∧
      Z.symm '' {y : E3 |
          S2.radial (1 / 2) < ‖y‖ ∧ ‖y‖ < S2.radial (3 / 4)} =
        {x : E3 |
          S1.radial (1 / 2) < ‖x‖ ∧ ‖x‖ < S1.radial (3 / 4)} := by
  classical
  let d0 := S1.radial (5 / 16)
  let a0 := S1.radial (3 / 8)
  let b0 := S1.radial (1 / 2)
  let c0 := S1.radial (3 / 4)
  let R0 := S1.radial (7 / 8)
  let S0 := S2.radial (3 / 4)
  have hsm1 := S1.contDiffOn_radial hpsi1 (by norm_num)
  have hsm2 := S2.contDiffOn_radial hpsi2 (by norm_num)
  have hclosedOpen : Icc (5 / 16 : ℝ) (7 / 8) ⊆ Ioo (1 / 4) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hclosedIco : Icc (5 / 16 : ℝ) (7 / 8) ⊆ Ico (1 / 4) 1 :=
    fun _ ht => Ioo_subset_Ico_self (hclosedOpen ht)
  obtain ⟨R1, hR1s, hR1t, hR1f, _, hR1i, hR1deriv⟩ :=
    (S1.radial_strictMono.mono hclosedIco).exists_smooth_openInterval_chart
      (by norm_num) (hsm1.mono hclosedOpen)
      (fun t ht => S1.deriv_radial_pos hpsi1 (by norm_num)
        (hclosedOpen (Ioo_subset_Icc_self ht)))
  have hd : 0 < d0 := S1.radial_pos _ (by norm_num)
  have hda : d0 < a0 := S1.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have hab : a0 < b0 := S1.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have hbc : b0 < c0 := S1.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have hcR : c0 < R0 := S1.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have ha : 0 < a0 := hd.trans hda
  have hb : 0 < b0 := ha.trans hab
  have hc : 0 < c0 := hb.trans hbc
  have hS : 0 < S0 := S2.radial_pos _ (by norm_num)
  have hinverse {r : ℝ} (hr : r ∈ Ioo d0 R0) : R1.symm r ∈ Ioo (1 / 4 : ℝ) 1 :=
    hclosedOpen (Ioo_subset_Icc_self (hR1s ▸ R1.map_target (hR1t.symm ▸ hr)))
  let f : ℝ → ℝ := fun r => S2.radial (R1.symm r)
  have hf : ContDiffOn ℝ ∞ f (Ioo d0 R0) :=
    hsm2.comp (hR1t ▸ hR1i) (fun _ hr => hinverse hr)
  have hfpos : ∀ r ∈ Ioo d0 R0, 0 < f r :=
    fun r hr => S2.radial_pos _ (Ioo_subset_Ico_self (hinverse hr))
  have hfderiv : ∀ r ∈ Icc a0 c0, 0 < deriv f r := by
    intro r hr
    have hrT : r ∈ R1.target := hR1t.symm ▸ ⟨hda.trans_le hr.1, hr.2.trans_lt hcR⟩
    have hx := hinverse (hR1t ▸ hrT)
    have hd2 := ((hsm2.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt
      (by simp)).hasDerivAt
    have hdi := ((hR1i.contDiffAt (R1.open_target.mem_nhds hrT)).differentiableAt
      (by simp)).hasDerivAt
    have hcomp := hd2.comp r hdi
    change HasDerivAt f
      (deriv S2.radial (R1.symm r) * deriv (R1.symm : ℝ → ℝ) r) r at hcomp
    rw [hcomp.deriv]
    exact mul_pos (S2.deriv_radial_pos hpsi2 (by norm_num) hx) (hR1deriv r hrT).1
  have hfeq (t : ℝ) (ht : t ∈ Icc (3 / 8 : ℝ) (3 / 4)) :
      f (S1.radial t) = S2.radial t := by
    have htR : t ∈ R1.source := by
      rw [hR1s]
      constructor <;> linarith [ht.1, ht.2]
    have hi := R1.left_inv htR
    rw [hR1f] at hi
    exact congrArg S2.radial hi
  have hfc : f c0 = S0 := hfeq _ (by norm_num)
  obtain ⟨tau, k, htaus, htaut, htau, htaui, _, htaum, _, htau0, _,
    htaueq, _, _, htaumpos, htaucenter, htauicenter⟩ :=
    Real.exists_smooth_inward_radial_chart hd hda hab hbc hcR hf hfpos hfderiv
  have htaut' : tau.target = Ioo (-S0) S0 := by rw [htaut, hfc]
  have hnS : tau a0 < S0 := by
    have hamem : a0 ∈ tau.source := by rw [htaus]; constructor <;> linarith
    exact (htaut' ▸ tau.map_source hamem).2
  obtain ⟨Q, hQs, hQt, hQf, _, hQ, hQi, hQ0, hQi0, _, _, _, _, hQannulus⟩ :=
    tau.exists_smooth_radialBall_chart (E := E3) (R := c0) (S := S0)
      (m := a0) (n := tau a0) (k := k) hc hS ha (hab.trans hbc) htaumpos hnS
      htaus htaut' htau htaui (htaum.mono Ioo_subset_Icc_self) htau0
      (fun r hr => htaucenter r ⟨(neg_nonpos.mpr ha.le).trans hr.1, hr.2⟩)
      (fun r hr => htauicenter r ⟨(neg_nonpos.mpr htaumpos.le).trans hr.1, hr.2⟩)
  let fSphere := S1.boundary_map.symm.trans S2.boundary_map
  obtain ⟨D⟩ := hD fSphere
  obtain ⟨d, hdnorm, hdinorm, _, _, hdouter, _, _, _⟩ :=
    D.exists_normPreserving_radialExtension
      (a := b0 / 4) (b := b0 / 2) (by positivity) (by linarith)
  let Z := d.toHomeomorph.toOpenPartialHomeomorph.trans Q
  have hZs : Z.source = ball 0 c0 := by
    change univ ∩ d ⁻¹' Q.source = ball 0 c0
    rw [hQs]
    ext x
    simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, mem_ball_zero_iff, hdnorm]
  have hZt : Z.target = ball 0 S0 := by
    change Q.target ∩ Q.symm ⁻¹' univ = ball 0 S0
    simp only [preimage_univ, inter_univ, hQt]
  have hZ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Z Z.source := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => Q (d x)) Z.source
    apply hQ.contMDiffOn.comp d.contMDiff.contMDiffOn
    intro x hx
    change d x ∈ Q.source
    rw [hQs, mem_ball_zero_iff, hdnorm]
    exact mem_ball_zero_iff.mp (hZs ▸ hx)
  have hZi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Z.symm Z.target := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => d.symm (Q.symm x)) Z.target
    exact d.symm.contMDiff.comp_contMDiffOn
      (hQi.contMDiffOn.mono (fun _ hx => hQt.symm ▸ hZt ▸ hx))
  have hd0 : d 0 = 0 := norm_eq_zero.mp (by rw [hdnorm, norm_zero])
  have hdi0 : d.symm 0 = 0 := norm_eq_zero.mp (by rw [hdinorm, norm_zero])
  have hZ0 : Z 0 = 0 := by change Q (d 0) = 0; rw [hd0, hQ0]
  have hZi0 : Z.symm 0 = 0 := by change d.symm (Q.symm 0) = 0; rw [hQi0, hdi0]
  have htauray (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
      tau (S1.radial t) = S2.radial t := by
    have htI : t ∈ Ico (1 / 4 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hr : S1.radial t ∈ Icc b0 c0 :=
      ⟨S1.radial_strictMono.monotoneOn (by norm_num) htI ht.1,
        S1.radial_strictMono.monotoneOn htI (by norm_num) ht.2⟩
    exact (htaueq hr).trans (hfeq t ⟨by linarith [ht.1], ht.2⟩)
  have hZray (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
      Z (S1.radial t • (S1.boundary_map q).val) =
        S2.radial t • (S2.boundary_map q).val := by
    have htI : t ∈ Ico (1 / 4 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hrpos := S1.radial_pos t htI
    have hbr : b0 ≤ S1.radial t :=
      S1.radial_strictMono.monotoneOn (by norm_num) htI ht.1
    have hangular : d (S1.radial t • (S1.boundary_map q).val) =
        S1.radial t • (S2.boundary_map q).val := by
      have h := hdouter (S1.boundary_map q) (S1.radial t) (by linarith)
      change d (S1.radial t • (S1.boundary_map q).val) = S1.radial t •
        (S2.boundary_map (S1.boundary_map.symm (S1.boundary_map q))).val at h
      rwa [Diffeomorph.symm_apply_apply] at h
    change Q (d (S1.radial t • (S1.boundary_map q).val)) = _
    rw [hangular, hQf]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos,
      mem_sphere_zero_iff_norm.mp (S2.boundary_map q).property, mul_one]
    rw [smul_smul, div_mul_cancel₀ _ hrpos.ne', htauray t ht]
  have hraymem (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ico (1 / 2 : ℝ) (3 / 4)) :
      S1.radial t • (S1.boundary_map q).val ∈ Z.source := by
    rw [hZs, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.mp (S1.boundary_map q).property, mul_one,
      abs_of_pos (S1.radial_pos t ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    exact S1.radial_strictMono ⟨by linarith [ht.1], by linarith [ht.2]⟩
      (by norm_num) ht.2
  let A1 : Set E3 := {x | b0 < ‖x‖ ∧ ‖x‖ < c0}
  let A2 : Set E3 := {y | S2.radial (1 / 2) < ‖y‖ ∧ ‖y‖ < S0}
  have hdannulus : d '' A1 = A1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [A1, mem_ofPred_eq, hdnorm] using hx
    · intro hy
      refine ⟨d.symm y, ?_, d.apply_symm_apply y⟩
      simpa only [A1, mem_ofPred_eq, hdinorm] using hy
  have hZannulus : Z '' A1 = A2 := by
    change (fun x => Q (d x)) '' A1 = A2
    rw [← image_image, hdannulus]
    have heq := hQannulus b0 ⟨hb.le, hbc⟩
    rw [htauray (1 / 2) (by norm_num)] at heq
    exact heq
  have hA1s : A1 ⊆ Z.source := fun _ hx =>
    hZs.symm ▸ mem_ball_zero_iff.mpr hx.2
  refine ⟨Z, hZs, hZt, hZ, hZi, hZ0, hZi0, hZray, ?_, hZannulus, ?_⟩
  · intro q t ht
    rw [← hZray q t ⟨ht.1, ht.2.le⟩]
    exact Z.left_inv (hraymem q t ht)
  · change Z.symm '' A2 = A1
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hZannulus.symm ▸ hx
      rw [Z.left_inv (hA1s hz)]
      exact hz
    · intro x hx
      exact ⟨Z x, hZannulus ▸ mem_image_of_mem Z hx, Z.left_inv (hA1s hx)⟩

end PoincareConjecture.M25.Topology3D.SchoenfliesData
