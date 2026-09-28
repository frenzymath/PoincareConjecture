import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic








set_option autoImplicit false

open Set Filter Topology
open scoped ContDiff BigOperators

namespace PoincareConjecture.M04

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem iteratedFDeriv_affine_on
    {O : Set P} (hO : IsOpen O) {f : P → ℝ}
    (hf : ContDiffOn ℝ 3 f O) (A : V →L[ℝ] P) (b : P)
    {x : V} (hx : b + A x ∈ O) {k : ℕ} (hk : (k : ℕ∞ω) ≤ 3) :
    iteratedFDeriv ℝ k (fun z => f (b + A z)) x =
      (iteratedFDeriv ℝ k f (b + A x)).compContinuousLinearMap (fun _ => A) := by
  let U : Set P := (fun y => b + y) ⁻¹' O
  have hU : IsOpen U := hO.preimage (continuous_const.add continuous_id)
  have hg : ContDiffOn ℝ 3 (fun y => f (b + y)) U :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hy => hy)
  have hAx : A x ∈ U := hx
  have hpre : IsOpen (A ⁻¹' U) := hU.preimage A.continuous
  have hga := hg.contDiffAt (hU.mem_nhds hAx)
  have hcomp : ContDiffAt ℝ 3 (fun z => f (b + A z)) x :=
    hga.comp x A.contDiff.contDiffAt
  have h := A.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn
    hpre.uniqueDiffOn hAx hk
  simp only [Function.comp_def] at h
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn
    (hcomp.of_le hk) hAx,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn (hga.of_le hk) hAx] at h
  simpa only [Function.comp_def, iteratedFDeriv_comp_add_left] using h

private theorem iteratedFDeriv_slice_norm_le
    {O : Set (P × V)} (hO : IsOpen O) {f : P × V → ℝ}
    (hf : ContDiffOn ℝ 3 f O) {p : P} {z : V} (hpz : (p, z) ∈ O)
    {k : ℕ} (hk : (k : ℕ∞ω) ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun w => f (p, w)) z‖ ≤
      ‖iteratedFDeriv ℝ k f (p, z)‖ := by
  have he : iteratedFDeriv ℝ k (fun w => f (p, w)) z =
      (iteratedFDeriv ℝ k f (p, z)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P V) := by
    simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
      iteratedFDeriv_affine_on hO hf (ContinuousLinearMap.inr ℝ P V)
        (p, (0 : V)) (by simpa using hpz) hk
  rw [he]
  refine ((iteratedFDeriv ℝ k f (p, z)).norm_compContinuousLinearMap_le
    (fun _ => ContinuousLinearMap.inr ℝ P V)).trans ?_
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ P V)

private theorem iteratedDeriv_line_eq
    {O : Set V} (hO : IsOpen O) {f : V → ℝ}
    (hf : ContDiffOn ℝ 3 f O) (z : V) {t : ℝ} (ht : t • z ∈ O)
    {k : ℕ} (hk : (k : ℕ∞ω) ≤ 3) :
    iteratedDeriv k (fun s : ℝ => f (s • z)) t =
      iteratedFDeriv ℝ k f (t • z) (fun _ => z) := by
  unfold iteratedDeriv
  have h := iteratedFDeriv_affine_on hO hf
    (ContinuousLinearMap.toSpanSingleton ℝ z) (0 : V) (by simpa using ht) hk
  simpa only [zero_add, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, one_smul] using
    congrArg (fun A => A (fun _ : Fin k => (1 : ℝ))) h

set_option maxHeartbeats 800000 in



theorem exists_uniform_quadratic_taylor_bound [FiniteDimensional ℝ V]
    (K : Set P) (hK : IsCompact K) (O : Set (P × V)) (hO : IsOpen O)
    (f : P × V → ℝ) (hf : ContDiffOn ℝ 3 f O)
    (hzero : ∀ p ∈ K, (p, (0 : V)) ∈ O) :
    ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ B ∧
      K ×ˢ Metric.closedBall (0 : V) ρ ⊆ O ∧
      ∀ p ∈ K,
        ‖fderiv ℝ (fun z => f (p, z)) 0‖ ≤ B ∧
        ‖fderiv ℝ (fderiv ℝ (fun z => f (p, z))) 0‖ ≤ B ∧
        (∀ v w, fderiv ℝ (fderiv ℝ (fun z => f (p, z))) 0 v w =
          fderiv ℝ (fderiv ℝ (fun z => f (p, z))) 0 w v) ∧
        ∀ z, ‖z‖ ≤ ρ →
          |f (p, z) - f (p, 0) - fderiv ℝ (fun w => f (p, w)) 0 z -
              fderiv ℝ (fderiv ℝ (fun w => f (p, w))) 0 z z / 2| ≤
            B * ‖z‖ ^ 3 := by
  obtain ⟨U, W, _hU, hW, hKU, h0W, hUW⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (0 : V))) hO
      (by
        rintro ⟨p, z⟩ ⟨hp, hz⟩
        rcases mem_singleton_iff.mp hz with rfl
        exact hzero p hp)
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW 0 (h0W (mem_singleton 0))
  let ρ : ℝ := min 1 (r / 2)
  have hρ : 0 < ρ := lt_min zero_lt_one (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρr : ρ < r := (min_le_right _ _).trans_lt (by linarith)
  have hKO : K ×ˢ Metric.closedBall (0 : V) ρ ⊆ O := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    exact hUW ⟨hKU hp, hrW ((Metric.mem_ball).2
      ((Metric.mem_closedBall.mp hz).trans_lt hρr))⟩
  have hcompact : IsCompact (K ×ˢ Metric.closedBall (0 : V) ρ) :=
    hK.prod (isCompact_closedBall _ _)
  obtain ⟨b₁, hb₁⟩ := hcompact.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv (k := 1) hf hO
      (by norm_num : (1 : ℕ∞ω) ≤ 3)).mono hKO)
  obtain ⟨b₂, hb₂⟩ := hcompact.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv (k := 2) hf hO
      (by norm_num : (2 : ℕ∞ω) ≤ 3)).mono hKO)
  obtain ⟨b₃, hb₃⟩ := hcompact.exists_bound_of_continuousOn
    ((ContinuousOn.continuousOn_iteratedFDeriv (k := 3) hf hO
      (by norm_num : (3 : ℕ∞ω) ≤ 3)).mono hKO)
  let B : ℝ := max 1 (max b₁ (max b₂ b₃))
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hb₁B : b₁ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hb₂B : b₂ ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hb₃B : b₃ ≤ B :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨ρ, B, hρ, hρ1, hB, hKO, ?_⟩
  intro p hp
  let slice : V → ℝ := fun z => f (p, z)
  let S : Set V := (fun z => (p, z)) ⁻¹' O
  have hS : IsOpen S := hO.preimage (continuous_const.prodMk continuous_id)
  have hslice : ContDiffOn ℝ 3 slice S :=
    hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => hz)
  have hS0 : (0 : V) ∈ S := hzero p hp
  have hslice0 : ContDiffAt ℝ 3 slice 0 := hslice.contDiffAt (hS.mem_nhds hS0)
  have hp0 : (p, (0 : V)) ∈ K ×ˢ Metric.closedBall (0 : V) ρ :=
    ⟨hp, Metric.mem_closedBall_self hρ.le⟩
  have hfirst : ‖fderiv ℝ slice 0‖ ≤ B := by
    rw [← norm_iteratedFDeriv_one]
    exact (iteratedFDeriv_slice_norm_le hO hf (hzero p hp) (by norm_num)).trans
      ((hb₁ _ hp0).trans hb₁B)
  have hsecond : ‖fderiv ℝ (fderiv ℝ slice) 0‖ ≤ B := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact (iteratedFDeriv_slice_norm_le hO hf (hzero p hp) (by norm_num)).trans
      ((hb₂ _ hp0).trans hb₂B)
  refine ⟨hfirst, hsecond, hslice0.isSymmSndFDerivAt (by norm_num [minSmoothness]), ?_⟩
  intro z hz
  let line : ℝ → ℝ := fun t => slice (t • z)
  have htz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (p, t • z) ∈ K ×ˢ Metric.closedBall (0 : V) ρ := by
    refine ⟨hp, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    simpa only [one_mul] using mul_le_mul ht.2 hz (norm_nonneg z) zero_le_one
  have hlineAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 3 line t := by
    have hs : ContDiffAt ℝ 3 slice (t • z) :=
      hslice.contDiffAt (hS.mem_nhds (hKO (htz t ht)))
    have hscale : ContDiffAt ℝ 3 (fun s : ℝ => s • z) t :=
      contDiffAt_id.smul contDiffAt_const
    have hcomp := hs.comp t hscale
    exact hcomp
  have hline : ContDiffOn ℝ 3 line (Icc (0 : ℝ) 1) :=
    fun t ht => (hlineAt t ht).contDiffWithinAt
  have hthird (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin 3 line (Icc (0 : ℝ) 1) t‖ ≤ B * ‖z‖ ^ 3 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (hlineAt t ht) ht]
    rw [iteratedDeriv_line_eq hS hslice z (hKO (htz t ht)) (by norm_num)]
    have hn : ‖iteratedFDeriv ℝ 3 slice (t • z)‖ ≤ B :=
      (iteratedFDeriv_slice_norm_le hO hf (hKO (htz t ht)) (by norm_num)).trans
        ((hb₃ _ (htz t ht)).trans hb₃B)
    calc
      ‖iteratedFDeriv ℝ 3 slice (t • z) (fun _ => z)‖ ≤
          ‖iteratedFDeriv ℝ 3 slice (t • z)‖ * ∏ _ : Fin 3, ‖z‖ :=
        (iteratedFDeriv ℝ 3 slice (t • z)).le_opNorm _
      _ ≤ B * ‖z‖ ^ 3 := by
        simpa using mul_le_mul_of_nonneg_right hn
          (pow_nonneg (norm_nonneg z) 3)
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hd₁ : iteratedDerivWithin 1 line (Icc (0 : ℝ) 1) 0 =
      fderiv ℝ slice 0 z := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hlineAt 0 h01).of_le (by norm_num)) h01]
    simpa only [zero_smul, iteratedFDeriv_one_apply] using
      iteratedDeriv_line_eq hS hslice z (by simpa using hS0)
        (k := 1) (t := 0) (by norm_num)
  have hd₂ : iteratedDerivWithin 2 line (Icc (0 : ℝ) 1) 0 =
      fderiv ℝ (fderiv ℝ slice) 0 z z := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hlineAt 0 h01).of_le (by norm_num)) h01]
    simpa only [zero_smul, iteratedFDeriv_two_apply] using
      iteratedDeriv_line_eq hS hslice z (by simpa using hS0)
        (k := 2) (t := 0) (by norm_num)
  have hpoly : taylorWithinEval line 2 (Icc (0 : ℝ) 1) 0 1 =
      slice 0 + fderiv ℝ slice 0 z + fderiv ℝ (fderiv ℝ slice) 0 z z / 2 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hd₁, hd₂, line] <;> ring
  have htaylor := taylor_mean_remainder_bound (f := line) (n := 2)
    (C := B * ‖z‖ ^ 3) (a := 0) (b := 1) (x := 1)
    zero_le_one hline ⟨zero_le_one, le_rfl⟩ hthird
  rw [hpoly] at htaylor
  have harg : line 1 - (slice 0 + fderiv ℝ slice 0 z +
      fderiv ℝ (fderiv ℝ slice) 0 z z / 2) =
      f (p, z) - f (p, 0) - fderiv ℝ slice 0 z -
        fderiv ℝ (fderiv ℝ slice) 0 z z / 2 := by
    dsimp [line, slice]
    simp only [one_smul]
    ring
  rw [harg, Real.norm_eq_abs] at htaylor
  norm_num only [sub_zero, one_pow, mul_one, Nat.factorial, Nat.cast_ofNat] at htaylor
  change |f (p, z) - f (p, 0) - fderiv ℝ slice 0 z -
    fderiv ℝ (fderiv ℝ slice) 0 z z / 2| ≤ B * ‖z‖ ^ 3
  nlinarith [show 0 ≤ B * ‖z‖ ^ 3 by positivity]

end PoincareConjecture.M04

