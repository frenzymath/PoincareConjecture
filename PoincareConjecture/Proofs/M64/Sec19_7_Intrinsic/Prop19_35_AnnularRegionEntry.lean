import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcDefiningFunction
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalRegularity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Matrix

namespace PoincareConjecture

private theorem positive_after_positive_derivative
    {f : ℝ → ℝ} {v : ℝ} (hf : HasDerivAt f v 0) (hzero : f 0 = 0) (hv : 0 < v) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t := by
  have hs := hf.tendsto_slope_zero_right.eventually_const_lt hv
  filter_upwards [hs, self_mem_nhdsWithin] with t ht htpos
  have htpos' : 0 < t := htpos
  simp only [zero_add, hzero, sub_zero, smul_eq_mul] at ht
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr htpos')).mp ht

private theorem circle_radial_tangent_decomposition (p : ℝ) (w : AnnulusCoordinates) :
    (inner ℝ (intrinsicAnnulusBoundary 1 p) w) • intrinsicAnnulusBoundary 1 p +
      (inner ℝ (!₂[-Real.sin p, Real.cos p] : AnnulusCoordinates) w) •
        !₂[-Real.sin p, Real.cos p] = w := by
  ext i
  fin_cases i
  all_goals
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, intrinsicAnnulusBoundary,
      PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Real.inner_apply, one_mul]
  · change (Real.cos p * w 0 + Real.sin p * w 1) * Real.cos p +
        (-Real.sin p * w 0 + Real.cos p * w 1) * (-Real.sin p) = w 0
    linear_combination (w 0) * (Real.sin_sq_add_cos_sq p)
  · change (Real.cos p * w 0 + Real.sin p * w 1) * Real.sin p +
        (-Real.sin p * w 0 + Real.cos p * w 1) * Real.cos p = w 1
    linear_combination (w 1) * (Real.sin_sq_add_cos_sq p)

theorem m64Intrinsic_inward_curve_enters_annular_region
    {a b p : ℝ}
    (hinj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b)) (hp : p ∈ Ioo a b)
    {C U V : Set AnnulusCoordinates} (hC : IsCompact C)
    (hpC : intrinsicAnnulusBoundary 1 p ∉ C)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪ C)
    (hfV : frontier V = frontier U) (hsub : closure U ⊆ standardAnnulusDomain)
    {q : ℝ → AnnulusCoordinates} {v : AnnulusCoordinates}
    (hq0 : q 0 = intrinsicAnnulusBoundary 1 p) (hdq : HasDerivAt q v 0)
    (hinward : 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) v) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ t ∈ Ioo (0 : ℝ) epsilon, q t ∈ U := by
  let tangent : AnnulusCoordinates := !₂[-Real.sin p, Real.cos p]
  have htangent : HasDerivAt (intrinsicAnnulusBoundary 1) tangent p := by
    simpa only [tangent, one_mul, neg_one_mul] using
      m64Intrinsic_hasDerivAt_boundary 1 p
  have hregular : deriv (intrinsicAnnulusBoundary 1) p ≠ 0 := by
    rw [htangent.deriv]
    intro hz
    have hs := congrArg (fun w : AnnulusCoordinates => w 0) hz
    have hc := congrArg (fun w : AnnulusCoordinates => w 1) hz
    change -Real.sin p = 0 at hs
    change Real.cos p = 0 at hc
    nlinarith [Real.sin_sq_add_cos_sq p]
  have hnorm (s : ℝ) : ‖intrinsicAnnulusBoundary 1 s‖ = 1 := by
    have h := m64Intrinsic_boundary_self_inner 1 s
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (intrinsicAnnulusBoundary 1 s)]
  obtain ⟨phi, ell, hdphi, hzero, hell, hside⟩ :=
    m64Intrinsic_exists_arc_defining_function (m64Intrinsic_contDiff_boundary 1)
      hinj hp hregular hC hpC hU hV hdisj hfU hfV
  have hminimum : IsLocalMin (phi ∘ intrinsicAnnulusBoundary 1) p := by
    have hnear := ((m64Intrinsic_contDiff_boundary 1).continuous.tendsto p).eventually hside
    filter_upwards [hnear, isOpen_Ioo.mem_nhds hp] with s hs hsab
    change phi (intrinsicAnnulusBoundary 1 p) ≤ phi (intrinsicAnnulusBoundary 1 s)
    rw [hzero]
    apply hs.mp
    apply frontier_subset_closure
    rw [hfU]
    exact Or.inl ⟨s, Ioo_subset_Icc_self hsab, rfl⟩
  have heltangent : ell tangent = 0 :=
    hminimum.hasDerivAt_eq_zero (hdphi.comp_hasDerivAt p htangent)
  have hradial (w : AnnulusCoordinates) :
      ell w = inner ℝ (intrinsicAnnulusBoundary 1 p) w *
        ell (intrinsicAnnulusBoundary 1 p) := by
    calc
      ell w = ell ((inner ℝ (intrinsicAnnulusBoundary 1 p) w) •
          intrinsicAnnulusBoundary 1 p + (inner ℝ tangent w) • tangent) :=
        congrArg ell (circle_radial_tangent_decomposition p w).symm
      _ = _ := by
        rw [map_add, map_smul, map_smul, heltangent, smul_zero, add_zero, smul_eq_mul]
  have helne : ell (intrinsicAnnulusBoundary 1 p) ≠ 0 := by
    intro hz
    apply hell
    ext w
    change ell w = 0
    rw [hradial w, hz, mul_zero]
  have helpos : 0 < ell (intrinsicAnnulusBoundary 1 p) := by
    apply lt_of_le_of_ne _ (Ne.symm helne)
    by_contra hn
    have helneg : ell (intrinsicAnnulusBoundary 1 p) < 0 := lt_of_not_ge hn
    let ray : ℝ → AnnulusCoordinates := fun t =>
      (1 - t) • intrinsicAnnulusBoundary 1 p
    have hray0 : ray 0 = intrinsicAnnulusBoundary 1 p := by simp only [ray, sub_zero, one_smul]
    have hdray : HasDerivAt ray (-intrinsicAnnulusBoundary 1 p) 0 := by
      convert!
        ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))).smul_const
          (intrinsicAnnulusBoundary 1 p) using 1
      simp only [zero_sub, neg_one_smul]
    have hdphi' : HasFDerivAt phi ell (ray 0) := hray0.symm ▸ hdphi
    have hdf : HasDerivAt (phi ∘ ray) (-ell (intrinsicAnnulusBoundary 1 p)) 0 := by
      simpa only [map_neg] using hdphi'.comp_hasDerivAt 0 hdray
    have hfpos := positive_after_positive_derivative hdf
      (by simpa only [Function.comp_apply, hray0] using hzero) (neg_pos.mpr helneg)
    have hrayside := hdray.continuousAt.tendsto.eventually (hray0.symm ▸ hside)
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨t, ht, htpos, htside⟩ :=
      (hsmall.and (hfpos.and (hrayside.filter_mono nhdsWithin_le_nhds))).exists
    have hbad := (hsub (htside.mpr htpos.le)).1
    change 1 ≤ ‖(1 - t) • intrinsicAnnulusBoundary 1 p‖ at hbad
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.2), hnorm, mul_one] at hbad
    linarith [ht.1]
  have hellv : 0 < ell v := by rw [hradial]; exact mul_pos hinward helpos
  have hdphi' : HasFDerivAt phi ell (q 0) := hq0.symm ▸ hdphi
  have hpositive := positive_after_positive_derivative (hdphi'.comp_hasDerivAt 0 hdq)
    (by simpa only [Function.comp_apply, hq0] using hzero) hellv
  have hqside := hdq.continuousAt.tendsto.eventually (hq0.symm ▸ hside)
  have havoid : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∉ C :=
    hdq.continuousAt.preimage_mem_nhds
      (hC.isClosed.isOpen_compl.mem_nhds (hq0.symm ▸ hpC))
  obtain ⟨eta, heta, hinside⟩ := m64Intrinsic_inward_curve_enters_annulus hq0 hdq hinward
  have hentry : ∀ᶠ t in 𝓝[>] (0 : ℝ), q t ∈ U := by
    filter_upwards [hpositive, hqside.filter_mono nhdsWithin_le_nhds,
      havoid.filter_mono nhdsWithin_le_nhds, Ioo_mem_nhdsGT heta] with t htpos htside htC hteta
    have hcl : q t ∈ closure U := htside.mpr htpos.le
    have hnotfront : q t ∉ frontier U := by
      rw [hfU]
      rintro (⟨s, _, hs⟩ | htC')
      · have hgt := (hinside t hteta).1
        rw [← hs, hnorm] at hgt
        exact (lt_irrefl (1 : ℝ)) hgt
      · exact htC htC'
    by_contra hn
    exact hnotfront ⟨hcl, by simpa only [hU.interior_eq] using hn⟩
  obtain ⟨epsilon, hepsilon, hinterval⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hentry
  exact ⟨epsilon, hepsilon, fun t ht => hinterval ⟨ht.1, ht.2.le⟩⟩

end PoincareConjecture
