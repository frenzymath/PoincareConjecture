import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ScalarHeightFlow
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_radial_filling
    (rho : ℝ → ℝ)
    (hrho : ContDiffOn ℝ ∞ rho (Set.Ioo (-3 / 2 : ℝ) (3 / 2)))
    (hbound : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 1 / 4 < rho t ∧ rho t < 2) :
    ∃ B : BallNeighborhoodChart E2 E2,
      B.chart.source = Set.univ ∧ B.chart.target = Set.univ ∧
      (∃ (W : E2 → E2) (K L : ℝ≥0)
        (hK : LipschitzWith K W) (hL : ∀ y, ‖W y‖ ≤ L)
        (hW : ContDiff ℝ ∞ W) (hcW : HasCompactSupport W),
        B.chart = (boundedFlowDiffeomorph W hK hL hW hcW 1).toHomeomorph.toOpenPartialHomeomorph ∧
        (∀ y : E2, B.chart.symm y = boundedFlow W hK hL y (-1)) ∧
        ∃ C : Set E2, IsCompact C ∧
          C ⊆ {y : E2 | 1 / 8 < ‖y‖ ∧ ‖y‖ < 4} ∧
          tsupport (fun y : E2 => B.chart y - y) ⊆ C ∧
          tsupport (fun y : E2 => B.chart.symm y - y) ⊆ C) ∧
      B.chart (0 : E2) = 0 ∧
      ∀ v : E2,
        (v ∈ B.inside ↔ ‖v‖ < rho (v 0 / ‖v‖)) ∧
        (v ∈ B.closedRegion ↔ ‖v‖ ≤ rho (v 0 / ‖v‖)) ∧
        (v ∈ B.boundary ↔ ‖v‖ = rho (v 0 / ‖v‖)) := by
  let theta : E2 → ℝ := fun p => p 0 / ‖p‖
  have hcoord (p : E2) : -‖p‖ ≤ p 0 ∧ p 0 ≤ ‖p‖ := by
    have hn : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    constructor <;> nlinarith only [hn, norm_nonneg p, sq_nonneg (p 1)]
  have htheta (p : E2) : theta p ∈ Icc (-1 : ℝ) 1 := by
    by_cases hp : p = 0
    · simp only [theta, hp, norm_zero, div_zero]
      norm_num
    · have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp
      exact ⟨(le_div_iff₀ hn).mpr (by simpa only [neg_mul, one_mul] using (hcoord p).1),
        (div_le_iff₀ hn).mpr (by simpa only [one_mul] using (hcoord p).2)⟩
  have hthetai (p : E2) : theta p ∈ Ioo (-3 / 2 : ℝ) (3 / 2) :=
    ⟨by linarith [(htheta p).1], by linarith [(htheta p).2]⟩
  have hrhop (p : E2) : 0 < rho (theta p) := by linarith [(hbound _ (htheta p)).1]
  let K0 : Set E2 := {p | 1 / 4 ≤ ‖p‖ ∧ ‖p‖ ≤ 2}
  let U0 : Set E2 := {p | 1 / 8 < ‖p‖ ∧ ‖p‖ < 4}
  have hK0 : IsCompact K0 := (isCompact_closedBall (0 : E2) 2).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    (fun p hp => mem_closedBall_zero_iff.mpr hp.2)
  have hU0 : IsOpen U0 := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hKU : K0 ⊆ U0 := fun p hp => ⟨by linarith [hp.1], by linarith [hp.2]⟩
  obtain ⟨chi, hchi, hcchi, hsChi, hnear, _hRange⟩ :=
    exists_compact_smooth_cutoff hK0 hU0 hKU
  have hchiOne (p : E2) (hp : p ∈ K0) : chi p = 1 :=
    (eventually_nhdsSet_iff_forall.mp hnear p hp).self_of_nhds
  let V : E2 → E2 := fun p => Real.log (rho (theta p)) • p
  have hV : ContDiffOn ℝ ∞ V U0 := by
    intro p hp
    have hp0 : p ≠ 0 := by
      intro hh
      have hh' := hp.1
      rw [hh, norm_zero] at hh'
      norm_num at hh'
    have hth : ContDiffAt ℝ ∞ theta p :=
      (EuclideanSpace.proj 0).contDiff.contDiffAt.div (contDiffAt_norm ℝ hp0)
        (norm_ne_zero_iff.mpr hp0)
    have hr : ContDiffAt ℝ ∞ (fun q => rho (theta q)) p :=
      (hrho.contDiffAt (isOpen_Ioo.mem_nhds (hthetai p))).comp p hth
    exact ((hr.log (hrhop p).ne').smul contDiffAt_id).contDiffWithinAt
  let W : E2 → E2 := fun p => chi p • V p
  have hW : ContDiff ℝ ∞ W := contDiff_cutoff_smul hU0 chi hchi hsChi V hV
  have hcW : HasCompactSupport W := hcchi.smul_right
  have hWs : tsupport W ⊆ tsupport chi := tsupport_smul_subset_left chi V
  have hW0 : W 0 = 0 := by simp only [W, V, smul_zero]
  obtain ⟨K, L, hK, hL⟩ := compactField_bounds W hW hcW
  let G := boundedFlowDiffeomorph W hK hL hW hcW 1
  let B : BallNeighborhoodChart E2 E2 := {
    chart := G.toHomeomorph.toOpenPartialHomeomorph
    closedBall_subset_source := subset_univ _
    smooth := G.contMDiff_toFun.contDiff.contDiffOn
    smooth_symm := G.contMDiff_invFun.contDiff.contDiffOn }
  have hB (p : E2) : B.chart p = boundedFlow W hK hL p 1 := rfl
  have hBi (p : E2) : B.chart.symm p = boundedFlow W hK hL p (-1) := rfl
  have hfixed (s : ℝ) : boundedFlow W hK hL 0 s = 0 :=
    boundedFlow_eq_self W hK hL 0 hW0 s
  have hsupport (s : ℝ) :
      tsupport (fun p => boundedFlow W hK hL p s - p) ⊆ tsupport chi :=
    closure_minimal
      ((boundedFlow_support_subset W hK hL s).trans ((subset_tsupport W).trans hWs))
      (isClosed_tsupport chi)
  have hunitTheta (u : E2) (hu : ‖u‖ = 1) (a : ℝ) (ha : 0 < a) :
      theta (a • u) = u 0 := by
    change (a * u 0) / ‖a • u‖ = u 0
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hu, mul_one]
    field_simp [ha.ne']
  have hunitBound (u : E2) (hu : ‖u‖ = 1) : 1 / 4 < rho (u 0) ∧ rho (u 0) < 2 := by
    have ht := htheta u
    simpa only [theta, hu, div_one] using hbound _ ht
  have hfieldRay (u : E2) (hu : ‖u‖ = 1) (a : ℝ) (ha : 0 < a) :
      W (a • u) = (chi (a • u) * Real.log (rho (u 0)) * a) • u := by
    dsimp only [W, V]
    rw [hunitTheta u hu a ha, smul_smul, smul_smul]

  have hunitTrack (u : E2) (hu : ‖u‖ = 1) :
      boundedFlow W hK hL u 1 = rho (u 0) • u := by
    let a := Real.log (rho (u 0))
    have hR := hunitBound u hu
    have hRp : 0 < rho (u 0) := by linarith only [hR.1]
    have hea : Real.exp a = rho (u 0) := Real.exp_log hRp
    have htrack (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        Real.exp (s * a) • u ∈ K0 := by
      change 1 / 4 ≤ ‖Real.exp (s * a) • u‖ ∧ ‖Real.exp (s * a) • u‖ ≤ 2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hu, mul_one]
      by_cases ha : 0 ≤ a
      · have hlo : (1 : ℝ) ≤ Real.exp (s * a) := Real.one_le_exp_iff.mpr (mul_nonneg hs.1 ha)
        have hhi : Real.exp (s * a) ≤ rho (u 0) := by
          rw [← hea]
          exact Real.exp_le_exp.mpr (by nlinarith only [hs.2, ha])
        exact ⟨by linarith only [hlo], hhi.trans hR.2.le⟩
      · have ha' : a ≤ 0 := (lt_of_not_ge ha).le
        have hlo : rho (u 0) ≤ Real.exp (s * a) := by
          rw [← hea]
          exact Real.exp_le_exp.mpr (by nlinarith only [hs.2, ha'])
        have hhi : Real.exp (s * a) ≤ 1 :=
          Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs.1 ha')
        exact ⟨hR.1.le.trans hlo, by linarith only [hhi]⟩
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun t => Real.exp (t * a) • u)
          (W (Real.exp (s * a) • u)) s := by
      rw [hfieldRay u hu _ (Real.exp_pos _), hchiOne _ (htrack s hs), one_mul]
      simpa only [one_mul, id_eq, a, mul_comm] using
        (((hasDerivAt_id s).mul_const a).exp.smul_const u)
    have heq : EqOn (boundedFlow W hK hL u)
        (fun s => Real.exp (s * a) • u) (Icc (0 : ℝ) 1) := by
      apply ODE_solution_unique_of_mem_Icc_right
        (v := fun _ p => W p) (s := fun _ => univ) (fun _ _ => hK.lipschitzOnWith)
      · exact fun s _ => (boundedFlow_hasDerivAt W hK hL u s).continuousAt.continuousWithinAt
      · exact fun s _ => (boundedFlow_hasDerivAt W hK hL u s).hasDerivWithinAt
      · exact fun _ _ => mem_univ _
      · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
      · exact fun s hs => (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt
      · exact fun _ _ => mem_univ _
      · simp only [boundedFlow_zero, zero_mul, Real.exp_zero, one_smul]
    simpa only [one_mul, hea] using heq (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)

  have hRay (u : E2) (hu : ‖u‖ = 1) :
      ∃ f : ℝ → ℝ → ℝ,
        (∀ s, StrictMono (f s)) ∧ (∀ s, f s 0 = 0) ∧
        f 1 1 = rho (u 0) ∧
        (∀ r, 0 < r → ∀ s, boundedFlow W hK hL (r • u) s = f s r • u) ∧
        (∀ r, f 1 (f (-1) r) = r) := by
    let v : ℝ → ℝ := fun r => chi (r • u) * Real.log (rho (u 0)) * r
    have hv : ContDiff ℝ ∞ v :=
      ((hchi.comp (contDiff_id.smul contDiff_const)).mul contDiff_const).mul contDiff_id
    have hvs : Function.support v ⊆ Icc (-4 : ℝ) 4 := by
      intro r hr
      have hc : chi (r • u) ≠ 0 := by
        intro hh
        exact hr (by simp only [v, hh, zero_mul])
      have hp := hsChi (subset_tsupport chi hc)
      have hh : |r| < 4 := by
        simpa only [norm_smul, Real.norm_eq_abs, hu, mul_one] using hp.2
      exact ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩
    have hvc : HasCompactSupport v :=
      (isCompact_Icc : IsCompact (Icc (-4 : ℝ) 4)).of_isClosed_subset
        (isClosed_tsupport v) (closure_minimal hvs isClosed_Icc)
    obtain ⟨Kv, Lv, hKv, hLv⟩ := compactField_bounds v hv hvc
    let f : ℝ → ℝ → ℝ := fun s r => boundedFlow v hKv hLv r s
    have hfMono (s : ℝ) : StrictMono (f s) := boundedFlow_strictMono v hKv hLv hv hvc s
    have hv0 : v 0 = 0 := by simp only [v, mul_zero]
    have hfZero (s : ℝ) : f s 0 = 0 := boundedFlow_eq_self v hKv hLv 0 hv0 s
    have hfPos (r : ℝ) (hr : 0 < r) (s : ℝ) : 0 < f s r := by
      have hh := hfMono s hr
      rwa [hfZero] at hh
    have hfRay (r : ℝ) (hr : 0 < r) (s : ℝ) :
        boundedFlow W hK hL (r • u) s = f s r • u := by
      have hd (t : ℝ) : HasDerivAt (fun s => f s r • u) (W (f t r • u)) t := by
        rw [hfieldRay u hu _ (hfPos r hr t)]
        exact (boundedFlow_hasDerivAt v hKv hLv r t).smul_const u
      have heq := boundedField_solution_unique W hK
        (boundedFlow_hasDerivAt W hK hL (r • u)) hd
        (by simp only [f, boundedFlow_zero])
      exact congrFun heq s
    have hfUnit : f 1 1 = rho (u 0) := by
      have hh := hfRay 1 (by norm_num) 1
      rw [one_smul, hunitTrack u hu] at hh
      have hn := congrArg norm hh
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by linarith [(hunitBound u hu).1] : 0 < rho (u 0)),
        abs_of_pos (hfPos 1 (by norm_num) 1), hu, mul_one, mul_one] at hn
      exact hn.symm
    refine ⟨f, hfMono, hfZero, hfUnit, hfRay, ?_⟩
    intro r
    simpa only [f, neg_neg] using boundedFlow_neg v hKv hLv r (-1)
  refine ⟨B, rfl, rfl, ⟨W, K, L, hK, hL, hW, hcW, rfl, hBi,
    tsupport chi, hcchi, hsChi, hsupport 1, hsupport (-1)⟩, hfixed 1, ?_⟩
  intro p
  have himage (T : Set E2) : p ∈ B.chart '' T ↔ B.chart.symm p ∈ T := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      change G.symm (G q) ∈ T
      simpa only [G.symm_apply_apply] using hq
    · intro hp
      exact ⟨B.chart.symm p, hp, G.apply_symm_apply p⟩
  change (p ∈ B.chart '' ball 0 1 ↔ _) ∧
    (p ∈ B.chart '' closedBall 0 1 ↔ _) ∧ (p ∈ B.chart '' sphere 0 1 ↔ _)
  rw [himage, himage, himage, mem_ball_zero_iff, mem_closedBall_zero_iff,
    mem_sphere_zero_iff_norm]
  by_cases hp : p = 0
  · rw [hp, hBi, hfixed, norm_zero]
    have hr : 0 < rho 0 := by simpa only [theta, norm_zero, div_zero] using hrhop 0
    simp only [div_zero, zero_lt_one, hr, zero_le_one, hr.le, zero_ne_one, hr.ne,
      iff_self, and_self]
  · let r := ‖p‖
    let u : E2 := r⁻¹ • p
    have hr : 0 < r := norm_pos_iff.mpr hp
    have hu : ‖u‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      exact inv_mul_cancel₀ hr.ne'
    have hru : r • u = p := by
      dsimp only [u]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hu0 : u 0 = theta p := by
      change r⁻¹ * p 0 = p 0 / r
      ring
    obtain ⟨f, hfMono, hfZero, hfUnit, hfRay, hfInv⟩ := hRay u hu
    let q := f (-1) r
    have hq : 0 < q := by
      have hh := hfMono (-1) hr
      rwa [hfZero] at hh
    have hqInv : f 1 q = r := hfInv r
    have hnormInv : ‖B.chart.symm p‖ = q := by
      rw [hBi, ← hru, hfRay r hr (-1), norm_smul, Real.norm_eq_abs,
        abs_of_pos hq, hu, mul_one]
    have hlt : q < 1 ↔ r < rho (theta p) := by
      rw [← (hfMono 1).lt_iff_lt, hqInv, hfUnit, hu0]
    have hle : q ≤ 1 ↔ r ≤ rho (theta p) := by
      rw [← (hfMono 1).le_iff_le, hqInv, hfUnit, hu0]
    have heq : q = 1 ↔ r = rho (theta p) := by
      constructor
      · intro hh
        rw [hh, hfUnit, hu0] at hqInv
        exact hqInv.symm
      · intro hh
        apply (hfMono 1).injective
        rw [hqInv, hfUnit, hu0]
        exact hh
    rw [hnormInv]
    exact ⟨hlt, hle, heq⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
