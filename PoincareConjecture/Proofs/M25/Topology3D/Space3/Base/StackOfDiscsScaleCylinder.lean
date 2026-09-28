import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsScaleNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockTracks
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

variable {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}


theorem clockEvolution_image_Icc_of_zero_endpoints
    (omega : ℝ × ℝ → ℝ) {A B : ℝ≥0}
    (hA : LipschitzWith A (clockField omega))
    (hB : ∀ p, ‖clockField omega p‖ ≤ B)
    (homega : ContDiff ℝ ∞ omega) (hc : HasCompactSupport omega)
    (d : ℝ) (hd : 0 < d)
    (hzero : ∀ t, omega (t, 0) = 0) (hend : ∀ t, omega (t, d) = 0) :
    ∀ a b : ℝ, clockEvolution omega hA hB a b '' Icc 0 d = Icc 0 d := by
  intro a b
  let F := clockEvolutionDiffeomorph omega hA hB homega hc a b
  have hF0 : F 0 = 0 := clockEvolution_eq_self omega hA hB 0 hzero a b
  have hFd : F d = d := clockEvolution_eq_self omega hA hB d hend a b
  have hcont : ContinuousOn F (Icc 0 d) := F.contMDiff.continuous.continuousOn
  have hmono : StrictMonoOn F (Icc 0 d) :=
    ContinuousOn.strictMonoOn_of_injOn_Icc hd.le (by rw [hF0, hFd]; exact hd.le)
      hcont F.injective.injOn
  change F '' Icc 0 d = Icc 0 d
  simpa only [hF0, hFd] using hcont.image_Icc_of_monotoneOn hd.le hmono.monotoneOn


noncomputable def stackCapScaleCylinderField (C : SurgeryCapTag psi u)
    (lambda : ℝ) (rho : ℝ × E3 → ℝ) (theta : UnitCircle) (p : ℝ × ℝ) : ℝ :=
  rho (p.1, C.tube (theta.1,
    C.cutHeight + C.sign * C.removal + C.sign * p.2)) *
      (deriv (stackCapScale C.scale lambda) p.1 /
        stackCapScale C.scale lambda p.1) * p.2


theorem stackCapScaleCylinderField_spec (C : SurgeryCapTag psi u)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < C.scale)
    (rho : ℝ × E3 → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrhoc : HasCompactSupport rho)
    (theta : UnitCircle) (d : ℝ)
    (hend : ∀ t, rho (t, C.tube (theta.1,
      C.cutHeight + C.sign * C.removal + C.sign * d)) = 0) :
    let omega := stackCapScaleCylinderField C lambda rho theta
    ContDiff ℝ ∞ omega ∧ HasCompactSupport omega ∧
      (∀ t, omega (t, 0) = 0) ∧ (∀ t, omega (t, d) = 0) := by
  let s := C.cutHeight + C.sign * C.removal
  let omega := stackCapScaleCylinderField C lambda rho theta
  let Y := fun w : ℝ => C.tube (theta.1, s + C.sign * w)
  have hs (w : ℝ) : (theta.1, s + C.sign * w) ∈ C.tube.source :=
    C.tube_source ⟨sphere_subset_closedBall theta.2, mem_univ _⟩
  have hY : ContDiff ℝ ∞ Y := by
    apply contDiffOn_univ.mp
    exact C.tube_smooth.comp
      (contDiff_const.prodMk (contDiff_const.add (contDiff_const.mul contDiff_id))).contDiffOn
      (fun w _ => hs w)
  obtain ⟨hscale, hderiv, hbound, _, _⟩ := stackCapScale_spec C.scale lambda hlambda hsmall
  have hsmooth : ContDiff ℝ ∞ omega :=
    (((hrho.comp (contDiff_fst.prodMk (hY.comp contDiff_snd))).mul
      ((hderiv.comp contDiff_fst).div (hscale.comp contDiff_fst)
        (fun p => (hbound p.1).2.2.ne'))).mul contDiff_snd)
  obtain ⟨R, hR⟩ := hrhoc.isCompact.isBounded.exists_norm_le
  have hsupport : Function.support omega ⊆ closedBall (0 : ℝ × ℝ) (R + |s|) := by
    intro p hp
    have hr : rho (p.1, Y p.2) ≠ 0 := by
      intro hz
      apply hp
      change rho (p.1, Y p.2) * _ * p.2 = 0
      rw [hz, zero_mul, zero_mul]
    have hpoint := hR (p.1, Y p.2) (subset_tsupport rho hr)
    have ht : ‖p.1‖ ≤ R := (norm_fst_le (p.1, Y p.2)).trans hpoint
    have hy : ‖Y p.2‖ ≤ R := (norm_snd_le (p.1, Y p.2)).trans hpoint
    have hheight : inner ℝ (u : E3) (Y p.2) = s + C.sign * p.2 := C.tube_height _ (hs p.2)
    have habs : |p.2| = |inner ℝ (u : E3) (Y p.2) - s| := by
      rw [hheight, add_sub_cancel_left, abs_mul, C.sign_abs, one_mul]
    have hw : ‖p.2‖ ≤ R + |s| := by
      rw [Real.norm_eq_abs, habs]
      have hinner : |inner ℝ (u : E3) (Y p.2)| ≤ ‖Y p.2‖ := by
        simpa only [norm_eq_of_mem_sphere u, one_mul] using
          abs_real_inner_le_norm (u : E3) (Y p.2)
      exact (abs_sub _ _).trans (add_le_add (hinner.trans hy) le_rfl)
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le (ht.trans (le_add_of_nonneg_right (abs_nonneg s))) hw
  refine ⟨hsmooth, ?_, ?_, ?_⟩
  · exact (isCompact_closedBall (0 : ℝ × ℝ) (R + |s|)).of_isClosed_subset
      (isClosed_tsupport omega) (closure_minimal hsupport isClosed_closedBall)
  · intro t
    simp only [stackCapScaleCylinderField, mul_zero]
  · intro t
    simp only [stackCapScaleCylinderField, hend t, zero_mul]


theorem stackCapScaleCylinder_clock_tracks (C : SurgeryCapTag psi u)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (rho : ℝ × E3 → ℝ) (theta : UnitCircle) :
    let V := fun p => rho p • chartTimeField (stackCapScaleChart C lambda hlambda) p
    let omega := stackCapScaleCylinderField C lambda rho theta
    ∀ {A B A' B' : ℝ≥0}
      (hA : LipschitzWith A (clockField V)) (hB : ∀ p, ‖clockField V p‖ ≤ B)
      (hA' : LipschitzWith A' (clockField omega))
      (hB' : ∀ p, ‖clockField omega p‖ ≤ B') (a b w : ℝ),
      clockEvolution V hA hB a b
        (C.tube (theta.1, C.cutHeight + C.sign * C.removal + C.sign * w)) =
      C.tube (theta.1, C.cutHeight + C.sign * C.removal + C.sign *
        clockEvolution omega hA' hB' a b w) := by
  dsimp only
  intro A B A' B' hA hB hA' hB' a b w
  let s := C.cutHeight + C.sign * C.removal
  let V := fun p => rho p • chartTimeField (stackCapScaleChart C lambda hlambda) p
  let omega := stackCapScaleCylinderField C lambda rho theta
  let eta := fun t => clockEvolution omega hA' hB' a t w
  let gamma := fun t => C.tube (theta.1, s + C.sign * eta t)
  have hs (t : ℝ) : (theta.1, s + C.sign * eta t) ∈ C.tube.source :=
    C.tube_source ⟨sphere_subset_closedBall theta.2, mem_univ _⟩
  have hd (t : ℝ) : HasDerivAt gamma (V (t, gamma t)) t := by
    have heta := clockEvolution_hasDerivAt omega hA' hB' a t w
    have harg : HasDerivAt (fun r => (theta.1, s + C.sign * eta r))
        (0, C.sign * omega (t, eta t)) t :=
      (hasDerivAt_const t theta.1).prodMk ((heta.const_mul C.sign).const_add s)
    have hT := (C.tube_smooth.contDiffAt (C.tube.open_source.mem_nhds (hs t))).differentiableAt
      (by simp)
    have hcomp := hT.hasFDerivAt.comp_hasDerivAt t harg
    have hvector : ((0 : E2), C.sign * omega (t, eta t)) =
        (C.sign * omega (t, eta t)) • ((0 : E2), (1 : ℝ)) := by
      simp only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
    rw [hvector, map_smul] at hcomp
    have hVeq : V (t, gamma t) = (C.sign * omega (t, eta t)) •
        fderiv ℝ C.tube (theta.1, s + C.sign * eta t) (0, 1) := by
      change rho (t, gamma t) • chartTimeField (stackCapScaleChart C lambda hlambda)
        (t, C.tube (theta.1, s + C.sign * eta t)) = _
      rw [stackCapScaleChart_field_tube C lambda hlambda t theta.1 _ (hs t), smul_smul]
      congr 1
      dsimp only [omega, stackCapScaleCylinderField, gamma, s]
      ring
    rw [hVeq]
    exact hcomp
  have ha : a ∈ Ioo (min a b - 1) (max a b + 1) :=
    ⟨by linarith [min_le_left a b], by linarith [le_max_left a b]⟩
  have hb : b ∈ Ioo (min a b - 1) (max a b + 1) :=
    ⟨by linarith [min_le_right a b], by linarith [le_max_right a b]⟩
  have htrack := clockEvolution_tracks V hA hB gamma ha (fun t _ => hd t) hb
  simpa only [gamma, eta, clockEvolution_self] using htrack


theorem stackCapScaleField_preserves_core (C : SurgeryCapTag psi u)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < C.scale)
    (rho : ℝ × E3 → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrhoc : HasCompactSupport rho)
    (K L N : Set E3) (d : ℝ) (hd : 0 < d)
    (hstrip : N ∩ K = (fun p : E2 × ℝ => C.tube
      (p.1, C.cutHeight + C.sign * C.removal + C.sign * p.2)) ''
        (sphere (0 : E2) 1 ×ˢ Ico 0 d))
    (hclosed : (fun p : E2 × ℝ => C.tube
      (p.1, C.cutHeight + C.sign * C.removal + C.sign * p.2)) ''
        (sphere (0 : E2) 1 ×ˢ Icc 0 d) ⊆ K)
    (hend : ∀ theta : UnitCircle, C.tube (theta.1,
      C.cutHeight + C.sign * C.removal + C.sign * d) ∉ N)
    (havoid : ∀ t y, y ∈ (K \ N) ∪ L → rho (t, y) = 0) :
    let V := fun p => rho p • chartTimeField (stackCapScaleChart C lambda hlambda) p
    ∀ {A B : ℝ≥0} (hA : LipschitzWith A (clockField V))
      (hB : ∀ p, ‖clockField V p‖ ≤ B),
      (∀ a b, clockEvolution V hA hB a b '' K = K) ∧
      (∀ a b y, y ∈ (K \ N) ∪ L → clockEvolution V hA hB a b y = y) ∧
      ∀ a b y, y ∈ C.seam → clockEvolution V hA hB a b y = y := by
  dsimp only
  intro A B hA hB
  let V := fun p => rho p • chartTimeField (stackCapScaleChart C lambda hlambda) p
  have hfixed (a b : ℝ) (y : E3) (hy : y ∈ (K \ N) ∪ L) :
      clockEvolution V hA hB a b y = y :=
    clockEvolution_eq_self V hA hB y (fun t => by
      change rho (t, y) • _ = 0
      rw [havoid t y hy, zero_smul]) a b
  have hsub (a b : ℝ) : MapsTo (clockEvolution V hA hB a b) K K := by
    intro y hy
    by_cases hyN : y ∈ N
    · have hm : y ∈ N ∩ K := ⟨hyN, hy⟩
      rw [hstrip] at hm
      obtain ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩ := hm
      let theta : UnitCircle := ⟨x, hx⟩
      let omega := stackCapScaleCylinderField C lambda rho theta
      have hz (t : ℝ) : rho (t, C.tube (theta.1,
          C.cutHeight + C.sign * C.removal + C.sign * d)) = 0 := by
        apply havoid
        exact Or.inl ⟨hclosed ⟨(theta.1, d), ⟨theta.2, hd.le, le_rfl⟩, rfl⟩, hend theta⟩
      obtain ⟨homega, hoc, hozero, hoend⟩ :=
        stackCapScaleCylinderField_spec C lambda hlambda hsmall rho hrho hrhoc theta d hz
      obtain ⟨A', B', hA', hB'⟩ := clockField_bounds omega homega hoc
      have hi := clockEvolution_image_Icc_of_zero_endpoints omega hA' hB' homega hoc
        d hd hozero hoend a b
      have hw' : clockEvolution omega hA' hB' a b w ∈ Icc 0 d := by
        rw [← hi]
        exact ⟨w, ⟨hw.1, hw.2.le⟩, rfl⟩
      rw [stackCapScaleCylinder_clock_tracks C lambda hlambda rho theta hA hB hA' hB']
      exact hclosed ⟨(theta.1, clockEvolution omega hA' hB' a b w),
        ⟨theta.2, hw'⟩, rfl⟩
    · rw [hfixed a b y (Or.inl ⟨hy, hyN⟩)]
      exact hy
  refine ⟨?_, hfixed, ?_⟩
  · intro a b
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hsub a b hx
    · intro y hy
      exact ⟨clockEvolution V hA hB b a y, hsub b a hy,
        clockEvolution_reverse V hA hB b a y⟩
  · intro a b y hy
    rw [C.seam_eq_image] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    obtain ⟨_, _, htrack, _, _, hstart, _, _, _, _, _, hseam⟩ :=
      stackCapScaleCap_spec C lambda hlambda hsmall
    have hconstant (t : ℝ) : stackCapScaleCap C lambda t q =
        C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q :=
      (hseam t q hq).trans (hstart q)
    apply clockEvolution_eq_self V hA hB
    intro t
    have hc : HasDerivAt (fun _ : ℝ =>
        C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q)
        (chartTimeField (stackCapScaleChart C lambda hlambda)
          (t, C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q)) t := by
      simpa only [hconstant] using htrack t q
    have hv := hc.unique (hasDerivAt_const t _)
    change rho _ • _ = 0
    rw [hv, smul_zero]

end PoincareConjecture.M25.Topology3D
