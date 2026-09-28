import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Polar.Metric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open Set Filter TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData

variable {X : Type*} [MetricSpace X] {p : X} {hcomparison : RayComparison p} {n : ℕ}



theorem continuous_polarConeImage (d : UnitSliceRadialChartData hcomparison n) (c : ℝ) :
    Continuous (fun q : ℝ × d.Level => asymptoticConeDilation hcomparison
      (Real.toNNReal (q.1 / c)) (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) q.2))) := by
  have hlevel : Continuous (fun z : d.Level =>
      d.ambientChart (openLevelIncl d.potential d.source (1 / 2) z)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp d.levelHomeomorph.continuous)
  exact (continuous_asymptoticConeDilation hcomparison).comp
    ((continuous_real_toNNReal.comp (continuous_fst.div_const c)).prodMk
      (hlevel.comp continuous_snd))




theorem exists_polar_openPartialHomeomorph
    (d : UnitSliceRadialChartData hcomparison n) (c : ℝ≥0) (hc : 0 < c) (z : d.Level) :
    ∃ Q : OpenPartialHomeomorph (ℝ × d.Level) (UnitSliceAmbient n),
      ((c : ℝ), z) ∈ Q.source ∧
      Q ((c : ℝ), z) = openLevelIncl d.potential d.source (1 / 2) z ∧
      Q.target ⊆ d.ambientChart.source ∧
      (∀ q ∈ Q.source, 0 < q.1 ∧ Q q = d.polarMap c q ∧
        asymptoticConeDilation hcomparison (Real.toNNReal (q.1 / c))
          (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) q.2)) ∈ d.ambientChart.target) ∧
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ Q ((c : ℝ), z) ∧
      ContMDiffAt (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ Q.symm
        (openLevelIncl d.potential d.source (1 / 2) z) ∧
      (∀ y ∈ Q.target,
        (Q.symm y).1 = (c : ℝ) * (asymptoticConeRadius hcomparison (d.ambientChart y) : ℝ)) ∧
      (∀ y ∈ Q.target,
        d.ambientChart (openLevelIncl d.potential d.source (1 / 2) (Q.symm y).2) =
          asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison (d.ambientChart y))⁻¹
            (d.ambientChart y)) := by
  classical
  have hc' : 0 < (c : ℝ) := hc
  let I := 𝓘(ℝ, ℝ).prod (𝓡 n)
  let o : ℝ × d.Level := ((c : ℝ), z)
  let C : OpenPartialHomeomorph (ℝ × d.Level) (ℝ × EuclideanSpace ℝ (Fin n)) :=
    { toPartialEquiv := extChartAt I o
      open_source := isOpen_extChartAt_source o
      open_target := isOpen_extChartAt_target o
      continuousOn_toFun := continuousOn_extChartAt o
      continuousOn_invFun := continuousOn_extChartAt_symm o }
  let f := d.polarMap (c : ℝ)
  let F := writtenInExtChartAt I (𝓡 (n + 1)) o f
  have hf : ContMDiffAt I (𝓡 (n + 1)) ∞ f o := d.contMDiffAt_polarMap hc z
  have hF : ContDiffAt ℝ ∞ F (C o) := by
    simpa [F, C, I, contDiffWithinAt_univ] using (contMDiffAt_iff.mp hf).2
  have hderiv : mfderiv I (𝓡 (n + 1)) f o = fderiv ℝ F (C o) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [F, C, I]
  have hFinv : (fderiv ℝ F (C o)).IsInvertible := by
    rw [← hderiv]
    exact d.isInvertible_mfderiv_polarMap c hc z
  obtain ⟨A, hA⟩ := hFinv
  have hdF : HasFDerivAt F A.toContinuousLinearMap (C o) := by
    rw [hA]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  let R := hF.toOpenPartialHomeomorph F hdF (by simp)
  have hoR : C o ∈ R.source := hF.mem_toOpenPartialHomeomorph_source hdF (by simp)
  let S : Set (ℝ × d.Level) := {q | 0 < q.1 ∧
    asymptoticConeDilation hcomparison (Real.toNNReal (q.1 / c))
      (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) q.2)) ∈ d.ambientChart.target}
  have hS : IsOpen S := (isOpen_lt continuous_const continuous_fst).inter
    (d.ambientChart.open_target.preimage (d.continuous_polarConeImage c))
  have hoS : o ∈ S := by
    refine ⟨hc, ?_⟩
    change asymptoticConeDilation hcomparison (Real.toNNReal ((c : ℝ) / c))
      (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) z)) ∈ d.ambientChart.target
    rw [div_self hc'.ne', Real.toNNReal_one, asymptoticConeDilation_one]
    exact d.ambientChart.map_source z.1.2
  let Q := (C.trans R).restrOpen S hS
  have hoQ : o ∈ Q.source := ⟨⟨mem_extChartAt_source o, hoR⟩, hoS⟩
  have hQf : EqOn Q f Q.source := by
    intro q hq
    change F (C q) = f q
    simp only [F, writtenInExtChartAt, Function.comp_apply]
    change f (C.symm (C q)) = f q
    rw [C.left_inv hq.1.1]
  have hQcone (q : ℝ × d.Level) (hq : q ∈ Q.source) :
      d.ambientChart (Q q) = asymptoticConeDilation hcomparison (Real.toNNReal (q.1 / c))
        (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) q.2)) := by
    rw [hQf hq]
    change d.ambientChart (d.ambientChart.symm (asymptoticConeDilation hcomparison
      (Real.toNNReal (1 + (q.1 / c - 1))) _)) = _
    rw [show 1 + (q.1 / c - 1) = q.1 / c by ring]
    exact d.ambientChart.right_inv hq.2.2
  have hQsource (q : ℝ × d.Level) (hq : q ∈ Q.source) : Q q ∈ d.ambientChart.source := by
    rw [hQf hq]
    change d.ambientChart.symm (asymptoticConeDilation hcomparison
      (Real.toNNReal (1 + (q.1 / c - 1))) _) ∈ _
    rw [show 1 + (q.1 / c - 1) = q.1 / c by ring]
    exact d.ambientChart.map_target hq.2.2
  have hQo : Q o = openLevelIncl d.potential d.source (1 / 2) z :=
    (hQf hoQ).trans (d.radiusCoordinate_center hc z.1.2)
  have hforward : ContMDiffAt I (𝓡 (n + 1)) ∞ Q o := by
    apply hf.congr_of_eventuallyEq
    filter_upwards [Q.open_source.mem_nhds hoQ] with q hq
    exact hQf hq
  have hRinv : ContDiffAt ℝ ∞ R.symm (F (C o)) := hF.to_localInverse hdF (by simp)
  have hRC : R.symm (F (C o)) = C o := R.left_inv hoR
  have hCinverse : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) I ∞ C.symm (C o) := by
    exact (contMDiffOn_extChartAt_symm o).contMDiffAt (extChartAt_target_mem_nhds o)
  have hFo : F (C o) = openLevelIncl d.potential d.source (1 / 2) z := by
    exact (show F (C o) = Q o from rfl).trans hQo
  have hinverse : ContMDiffAt (𝓡 (n + 1)) I ∞ Q.symm
      (openLevelIncl d.potential d.source (1 / 2) z) := by
    rw [← hFo]
    have hC' : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) I ∞ C.symm (R.symm (F (C o))) := by
      rw [hRC]
      exact hCinverse
    exact hC'.comp (F (C o)) (contMDiffAt_iff_contDiffAt.mpr hRinv)
  refine ⟨Q, hoQ, hQo, ?_, (fun q hq => ⟨hq.2.1, hQf hq, hq.2.2⟩), hforward, hinverse, ?_, ?_⟩
  · intro y hy
    have hh := hQsource (Q.symm y) (Q.map_target hy)
    rwa [Q.right_inv hy] at hh
  · intro y hy
    have hq := Q.map_target hy
    have hh := congrArg (asymptoticConeRadius hcomparison) (hQcone (Q.symm y) hq)
    rw [Q.right_inv hy, asymptoticConeRadius_dilation] at hh
    have hunit : asymptoticConeRadius hcomparison
        (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) (Q.symm y).2)) = 1 :=
      (d.levelHomeomorph (Q.symm y).2).1.property
    rw [hunit, mul_one] at hh
    have hr := congrArg (fun a : ℝ≥0 => (a : ℝ)) hh
    rw [Real.coe_toNNReal _ (div_nonneg hq.2.1.le c.coe_nonneg)] at hr
    exact ((div_eq_iff hc'.ne').mp hr.symm).trans (mul_comm _ _)
  · intro y hy
    have hq := Q.map_target hy
    have hh := hQcone (Q.symm y) hq
    rw [Q.right_inv hy] at hh
    have hunit : asymptoticConeRadius hcomparison
        (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) (Q.symm y).2)) = 1 :=
      (d.levelHomeomorph (Q.symm y).2).1.property
    have hr := congrArg (asymptoticConeRadius hcomparison) hh
    rw [asymptoticConeRadius_dilation, hunit, mul_one] at hr
    rw [hr, hh, asymptoticConeDilation_mul]
    have hnonzero : Real.toNNReal ((Q.symm y).1 / (c : ℝ)) ≠ 0 :=
      (Real.toNNReal_pos.mpr (div_pos hq.2.1 hc')).ne'
    rw [inv_mul_cancel₀ hnonzero, asymptoticConeDilation_one]



theorem exists_polar_local_inverse_at
    (d : UnitSliceRadialChartData hcomparison n) (c : ℝ≥0) (hc : 0 < c)
    (q : ℝ × d.Level) (hq : 0 < q.1)
    (htarget : asymptoticConeDilation hcomparison (Real.toNNReal (q.1 / c))
      (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) q.2)) ∈ d.ambientChart.target) :
    ∃ R : OpenPartialHomeomorph (ℝ × d.Level) (UnitSliceAmbient n),
      q ∈ R.source ∧ EqOn R (d.polarMap c) R.source ∧
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ R q ∧
      ContMDiffAt (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ R.symm (R q) := by
  let r : ℝ≥0 := ⟨q.1, hq.le⟩
  have hr : 0 < r := hq
  have hc' : 0 < (c : ℝ) := hc
  let k : ℝ≥0 := r / c
  have hk : 0 < k := div_pos hr hc
  obtain ⟨P, hqP, hPq, hPtarget, hP, hPsmooth, hPinverse, _, _⟩ :=
    d.exists_polar_openPartialHomeomorph r hr q.2
  change P q = _ at hPq
  let T := (d.dilate k hk).ambientChart.trans d.ambientChart.symm
  have hzT : openLevelIncl d.potential d.source (1 / 2) q.2 ∈ T.source := by
    refine ⟨q.2.1.2, ?_⟩
    change asymptoticConeDilation hcomparison k
      (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) q.2)) ∈ d.ambientChart.target
    convert htarget using 2
    ext
    simp only [k, r, NNReal.coe_div, Real.coe_toNNReal _ (div_pos hq hc').le]
    rfl
  let R := P.trans T
  have hqR : q ∈ R.source := ⟨hqP, by change P q ∈ T.source; rwa [hPq]⟩
  have hRf : EqOn R (d.polarMap c) R.source := by
    intro w hw
    have hPw := hP w hw.1
    have hcone : d.ambientChart (P w) = asymptoticConeDilation hcomparison
        (Real.toNNReal (w.1 / r)) (d.ambientChart (openLevelIncl d.potential d.source (1 / 2) w.2)) := by
      rw [hPw.2.1]
      change d.ambientChart (d.ambientChart.symm (asymptoticConeDilation hcomparison
        (Real.toNNReal (1 + (w.1 / r - 1))) _)) = _
      rw [show 1 + (w.1 / r - 1) = w.1 / r by ring]
      exact d.ambientChart.right_inv hPw.2.2
    change d.ambientChart.symm (asymptoticConeDilation hcomparison k (d.ambientChart (P w))) = _
    rw [hcone, asymptoticConeDilation_mul]
    have hscale : k * Real.toNNReal (w.1 / r) = Real.toNNReal (w.1 / c) := by
      ext
      simp only [NNReal.coe_mul, k, NNReal.coe_div,
        Real.coe_toNNReal _ (div_pos hPw.1 (show 0 < (r : ℝ) from hr)).le,
        Real.coe_toNNReal _ (div_pos hPw.1 hc').le]
      field_simp
    rw [hscale]
    change _ = d.ambientChart.symm (asymptoticConeDilation hcomparison
      (Real.toNNReal (1 + (w.1 / c - 1))) _)
    rw [show 1 + (w.1 / c - 1) = w.1 / c by ring]
  obtain ⟨hT, hTinv, _⟩ := d.smooth_homothety_in_radial_charts d k hk
  have hTsmooth := hT.contMDiffAt (T.open_source.mem_nhds hzT)
  have hRsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ R q := by
    apply (show ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ T (P q) from hPq ▸ hTsmooth).comp q
    exact hPsmooth
  have hRinverse : ContMDiffAt (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ R.symm (R q) := by
    have hTq : T.symm (T (P q)) = P q := T.left_inv hqR.2
    have hPi : ContMDiffAt (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ P.symm (T.symm (R q)) := by
      change ContMDiffAt _ _ _ _ (T.symm (T (P q)))
      rw [hTq, hPq]
      exact hPinverse
    exact hPi.comp (R q) (hTinv.contMDiffAt (T.open_target.mem_nhds (T.map_source hqR.2)))
  exact ⟨R, hqR, hRf, hRsmooth, hRinverse⟩



theorem exists_smooth_polar_openPartialHomeomorph
    (d : UnitSliceRadialChartData hcomparison n) (c : ℝ≥0) (hc : 0 < c) (z : d.Level) :
    ∃ Q : OpenPartialHomeomorph (ℝ × d.Level) (UnitSliceAmbient n),
      ((c : ℝ), z) ∈ Q.source ∧
      Q ((c : ℝ), z) = openLevelIncl d.potential d.source (1 / 2) z ∧
      Q.target ⊆ d.ambientChart.source ∧
      (∀ q ∈ Q.source, 0 < q.1 ∧ Q q = d.polarMap c q) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ Q Q.source ∧
      ContMDiffOn (𝓡 (n + 1)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ Q.symm Q.target ∧
      (∀ y ∈ Q.target,
        (Q.symm y).1 = (c : ℝ) * (asymptoticConeRadius hcomparison (d.ambientChart y) : ℝ)) ∧
      (∀ y ∈ Q.target,
        d.ambientChart (openLevelIncl d.potential d.source (1 / 2) (Q.symm y).2) =
          asymptoticConeDilation hcomparison (asymptoticConeRadius hcomparison (d.ambientChart y))⁻¹
            (d.ambientChart y)) := by
  obtain ⟨Q, hzQ, hQz, hQtarget, hQ, _, _, hradius, hangle⟩ :=
    d.exists_polar_openPartialHomeomorph c hc z
  refine ⟨Q, hzQ, hQz, hQtarget, (fun q hq => ⟨(hQ q hq).1, (hQ q hq).2.1⟩), ?_, ?_, hradius, hangle⟩
  · intro q hq
    obtain ⟨R, hqR, hR, hsmooth, _⟩ :=
      d.exists_polar_local_inverse_at c hc q (hQ q hq).1 (hQ q hq).2.2
    apply ContMDiffAt.contMDiffWithinAt
    apply hsmooth.congr_of_eventuallyEq
    filter_upwards [Q.open_source.mem_nhds hq, R.open_source.mem_nhds hqR] with w hwQ hwR
    exact (hQ w hwQ).2.1.trans (hR hwR).symm
  · intro y hy
    let q := Q.symm y
    have hq : q ∈ Q.source := Q.map_target hy
    obtain ⟨R, hqR, hR, _, hinverse⟩ :=
      d.exists_polar_local_inverse_at c hc q (hQ q hq).1 (hQ q hq).2.2
    have hRq : R q = y := (hR hqR).trans ((hQ q hq).2.1.symm.trans (Q.right_inv hy))
    have hyR : y ∈ R.target := hRq ▸ R.map_source hqR
    have hnear : ∀ᶠ w in 𝓝 y, (w ∈ Q.target ∧ w ∈ R.target) ∧ R.symm w ∈ Q.source := by
      have hcont := R.symm.continuousOn.continuousAt (R.open_target.mem_nhds hyR)
      have hpoint : R.symm y ∈ Q.source := by rw [← hRq, R.left_inv hqR]; exact hq
      exact inter_mem (inter_mem (Q.open_target.mem_nhds hy) (R.open_target.mem_nhds hyR))
        (hcont.preimage_mem_nhds (Q.open_source.mem_nhds hpoint))
    have hEq : (Q.symm : UnitSliceAmbient n → ℝ × d.Level) =ᶠ[𝓝 y] R.symm := by
      filter_upwards [hnear] with w hw
      apply Q.injOn (Q.map_target hw.1.1) hw.2
      rw [Q.right_inv hw.1.1, (hQ (R.symm w) hw.2).2.1, ← hR (R.map_target hw.1.2), R.right_inv hw.1.2]
    apply ContMDiffAt.contMDiffWithinAt
    apply (show ContMDiffAt _ _ ∞ R.symm y from hRq ▸ hinverse).congr_of_eventuallyEq
    exact hEq

end Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData
