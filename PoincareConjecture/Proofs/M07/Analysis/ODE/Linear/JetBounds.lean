





import PoincareConjecture.Proofs.M07.Analysis.ODE.ParameterLinear
import PoincareConjecture.Proofs.M07.Analysis.ODE.ParameterDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace Poincare.ODE.Linear

open Poincare.ODE.Parameter

universe u

variable {P F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance : NormedAddCommGroup (F →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (P →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (P →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

def augment (A : F →L[ℝ] F) (B : P →L[ℝ] F →L[ℝ] F) :
    (F × (P →L[ℝ] F)) →L[ℝ] (F × (P →L[ℝ] F)) :=
  (A.comp (ContinuousLinearMap.fst ℝ F (P →L[ℝ] F))).prod
    (((ContinuousLinearMap.compL ℝ P F F A).comp (ContinuousLinearMap.snd ℝ F (P →L[ℝ] F))) +
      B.flip.comp (ContinuousLinearMap.fst ℝ F (P →L[ℝ] F)))

@[simp] theorem augment_apply (A : F →L[ℝ] F)
    (B : P →L[ℝ] F →L[ℝ] F) (z : F × (P →L[ℝ] F)) :
    augment A B z = (A z.1, A.comp z.2 + B.flip z.1) := rfl

theorem norm_augment_le (A : F →L[ℝ] F) (B : P →L[ℝ] F →L[ℝ] F) :
    ‖augment A B‖ ≤ ‖A‖ + ‖B‖ := by
  refine (augment A B).opNorm_le_bound (add_nonneg (norm_nonneg A) (norm_nonneg B)) ?_
  intro z
  rw [augment_apply, Prod.norm_def]
  apply max_le
  · exact (A.le_opNorm z.1).trans
      (mul_le_mul (le_add_of_nonneg_right (norm_nonneg B)) (norm_fst_le z)
        (norm_nonneg z.1) (add_nonneg (norm_nonneg A) (norm_nonneg B)))
  · calc
      ‖A.comp z.2 + B.flip z.1‖ ≤ ‖A.comp z.2‖ + ‖B.flip z.1‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖z.2‖ + ‖B‖ * ‖z.1‖ := by
        apply add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        simpa using B.flip.le_opNorm z.1
      _ ≤ ‖A‖ * ‖z‖ + ‖B‖ * ‖z‖ := add_le_add
        (mul_le_mul_of_nonneg_left (norm_snd_le z) (norm_nonneg A))
        (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg B))
      _ = (‖A‖ + ‖B‖) * ‖z‖ := by ring

def augmentL :
    ((F →L[ℝ] F) × (P →L[ℝ] F →L[ℝ] F)) →L[ℝ]
      ((F × (P →L[ℝ] F)) →L[ℝ] (F × (P →L[ℝ] F))) := by
  let L : ((F →L[ℝ] F) × (P →L[ℝ] F →L[ℝ] F)) →ₗ[ℝ]
      ((F × (P →L[ℝ] F)) →L[ℝ] (F × (P →L[ℝ] F))) :=
    { toFun := fun z => augment z.1 z.2
      map_add' := by
        intro z w
        ext v q <;> simp only [add_apply, Prod.fst_add, Prod.snd_add,
          augment_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearMap.flip_apply] <;> abel
      map_smul' := by intro c z; ext v q <;> simp [augment_apply] }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) L 2 ?_
  intro z
  exact (norm_augment_le z.1 z.2).trans (by
    calc ‖z.1‖ + ‖z.2‖ ≤ ‖z‖ + ‖z‖ := add_le_add (norm_fst_le z) (norm_snd_le z)
      _ = 2 * ‖z‖ := by ring)

theorem norm_augmentL_le : ‖(augmentL :
    ((F →L[ℝ] F) × (P →L[ℝ] F →L[ℝ] F)) →L[ℝ]
      ((F × (P →L[ℝ] F)) →L[ℝ] (F × (P →L[ℝ] F))))‖ ≤ 2 := by
  refine (augmentL (P := P) (F := F)).opNorm_le_bound (by norm_num) ?_
  intro z
  exact (norm_augment_le z.1 z.2).trans (by
    have hfst := norm_fst_le z
    have hsnd := norm_snd_le z
    linarith)

theorem norm_iteratedFDeriv_parameterFDeriv_slice
    {f : ℝ × P → F} {W : Set (ℝ × P)} (hW : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) {t : ℝ} {p : P} (hz : (t, p) ∈ W) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q => parameterFDeriv f (t, q)) p‖ =
      ‖iteratedFDeriv ℝ (k + 1) (fun q => f (t, q)) p‖ := by
  have heq : (fun q => parameterFDeriv f (t, q)) =ᶠ[𝓝 p]
      fderiv ℝ (fun q => f (t, q)) := by
    have hn : ∀ᶠ q in 𝓝 p, (t, q) ∈ W :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hW.mem_nhds hz)
    filter_upwards [hn] with q hq
    exact parameterFDeriv_eq_slice
      (((hf _ hq).contDiffAt (hW.mem_nhds hq)).differentiableAt (by simp))
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds, norm_iteratedFDeriv_fderiv]

theorem norm_iteratedFDeriv_augment_le
    {A : ℝ × P → F →L[ℝ] F} {W : Set (ℝ × P)} (hW : IsOpen W)
    (hA : ContDiffOn ℝ ∞ A W) {t : ℝ} {p : P} (hz : (t, p) ∈ W) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (fun q => augment (A (t, q)) (parameterFDeriv A (t, q))) p‖ ≤
      2 * max ‖iteratedFDeriv ℝ k (fun q => A (t, q)) p‖
        ‖iteratedFDeriv ℝ (k + 1) (fun q => A (t, q)) p‖ := by
  have hAp : ContDiffAt ℝ ∞ (fun q => A (t, q)) p :=
    ((hA _ hz).contDiffAt (hW.mem_nhds hz)).comp p
      (contDiffAt_const.prodMk contDiffAt_id)
  have hDAp : ContDiffAt ℝ ∞ (fun q => parameterFDeriv A (t, q)) p :=
    (((contDiffOn_parameterFDeriv hW hA) _ hz).contDiffAt (hW.mem_nhds hz)).comp p
      (contDiffAt_const.prodMk contDiffAt_id)
  have hk : (k : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl k
  let L := augmentL (P := P) (F := F)
  have h := L.norm_iteratedFDeriv_comp_left (hAp.prodMk hDAp) hk
  have hb := mul_le_mul_of_nonneg_right (norm_augmentL_le (P := P) (F := F))
    (norm_nonneg (iteratedFDeriv ℝ k
      (fun q => (A (t, q), parameterFDeriv A (t, q))) p))
  have heq : ‖iteratedFDeriv ℝ k (fun q => (A (t, q), parameterFDeriv A (t, q))) p‖ =
      max ‖iteratedFDeriv ℝ k (fun q => A (t, q)) p‖
        ‖iteratedFDeriv ℝ (k + 1) (fun q => A (t, q)) p‖ := by
    rw [iteratedFDeriv_prodMk hAp hDAp hk, ContinuousMultilinearMap.opNorm_prod,
      norm_iteratedFDeriv_parameterFDeriv_slice hW hA hz k]
  exact h.trans (hb.trans_eq (congrArg (fun x : ℝ => 2 * x) heq))

private theorem hasDerivAt_time_slice {y : ℝ × P → F} {t : ℝ} {p : P}
    (hy : DifferentiableAt ℝ y (t, p)) :
    HasDerivAt (fun s => y (s, p)) (timeFDeriv y (t, p)) t := by
  convert (hy.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t p)).hasDerivAt using 1 <;> rfl

theorem timeFDeriv_augment
    {A : ℝ × P → F →L[ℝ] F} {y : ℝ × P → F} {W : Set (ℝ × P)}
    (hW : IsOpen W) (hA : ContDiffOn ℝ ∞ A W) (hy : ContDiffOn ℝ ∞ y W)
    (hode : ∀ z ∈ W, timeFDeriv y z = A z (y z)) {z : ℝ × P} (hz : z ∈ W) :
    timeFDeriv (fun w => (y w, parameterFDeriv y w)) z =
      augment (A z) (parameterFDeriv A z) (y z, parameterFDeriv y z) := by
  have hyz := (hy z hz).contDiffAt (hW.mem_nhds hz)
  have hAz := (hA z hz).contDiffAt (hW.mem_nhds hz)
  have hdp : HasDerivAt (fun t => parameterFDeriv y (t, z.2))
      ((A z).comp (parameterFDeriv y z) + (parameterFDeriv A z).flip (y z)) z.1 := by
    have h := hasDerivAt_parameterFDeriv_of_ode hW
      (hy.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hz
      (hAz.differentiableAt (by simp)) (differentiableAt_const (c := (0 : F)))
      (fun w hw => by simpa using hode w hw)
    simpa [parameterFDeriv] using h
  have ht := (hasDerivAt_time_slice (hyz.differentiableAt (by simp))).congr_deriv (hode z hz)
  have hboth := ht.prodMk hdp
  have hdyz := ((contDiffOn_parameterFDeriv hW hy) z hz).contDiffAt (hW.mem_nhds hz)
  rw [timeFDeriv_eq_slice ((hyz.prodMk hdyz).differentiableAt (by simp))]
  exact hboth.deriv

theorem norm_iteratedFDeriv_linearODE_le [CompleteSpace F]
    (n : ℕ) {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    {U : Set P} (hU : IsOpen U) {W : Set (ℝ × P)} (hW : IsOpen W)
    (hUW : Icc a b ×ˢ U ⊆ W)
    {A : ℝ × P → F →L[ℝ] F} {y : ℝ × P → F} {y₀ : F}
    (hA : ContDiffOn ℝ ∞ A W) (hy : ContDiffOn ℝ ∞ y W)
    (hode : ∀ z ∈ W, timeFDeriv y z = A z (y z))
    (hinit : ∀ p ∈ U, y (a, p) = y₀)
    (hbound : ∀ j ≤ n, ∀ t ∈ Icc a b, ∀ p ∈ U,
      ‖iteratedFDeriv ℝ j (fun q => A (t, q)) p‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) {p : P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q => y (t, q)) p‖ ≤
      ‖y₀‖ * Real.exp ((2 : ℝ) ^ n * C * (t - a)) := by
  induction n generalizing F C with
  | zero =>
    have hd (s : ℝ) (hs : s ∈ Icc a b) :
        HasDerivAt (fun u => y (u, p)) (A (s, p) (y (s, p))) s :=
      (hasDerivAt_time_slice (((hy _ (hUW ⟨hs, hp⟩)).contDiffAt
        (hW.mem_nhds (hUW ⟨hs, hp⟩))).differentiableAt (by simp))).congr_deriv
          (hode _ (hUW ⟨hs, hp⟩))
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (show ‖y (a, p)‖ ≤ ‖y₀‖ by rw [hinit p hp])
      (K := C) (ε := 0) (fun s hs => by
        simpa only [add_zero] using ((A (s, p)).le_opNorm (y (s, p))).trans
          (mul_le_mul_of_nonneg_right
            (by simpa only [norm_iteratedFDeriv_zero] using
              hbound 0 le_rfl s (Ico_subset_Icc_self hs) p hp) (norm_nonneg _))) t ht
    simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul, gronwallBound_ε0] using h
  | succ n ih =>
    let Y : ℝ × P → F × (P →L[ℝ] F) := fun z => (y z, parameterFDeriv y z)
    let Q : ℝ × P → (F × (P →L[ℝ] F)) →L[ℝ] (F × (P →L[ℝ] F)) :=
      fun z => augment (A z) (parameterFDeriv A z)
    have hY : ContDiffOn ℝ ∞ Y W := hy.prodMk (contDiffOn_parameterFDeriv hW hy)
    have hQ : ContDiffOn ℝ ∞ Q W :=
      (augmentL (P := P) (F := F)).contDiff.comp_contDiffOn
        (hA.prodMk (contDiffOn_parameterFDeriv hW hA))
    have hQY : ∀ z ∈ W, timeFDeriv Y z = Q z (Y z) :=
      fun z hz => timeFDeriv_augment hW hA hy hode hz
    have hYinit : ∀ q ∈ U, Y (a, q) = (y₀, 0) := by
      intro q hq
      have hz : (a, q) ∈ W := hUW ⟨⟨le_rfl, hab⟩, hq⟩
      have heq : (fun v => y (a, v)) =ᶠ[𝓝 q] fun _ => y₀ := by
        filter_upwards [hU.mem_nhds hq] with v hv
        exact hinit v hv
      have hD : parameterFDeriv y (a, q) = 0 := by
        rw [parameterFDeriv_eq_slice
          (((hy _ hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)),
          heq.fderiv_eq]
        exact (hasFDerivAt_const y₀ q).fderiv
      exact Prod.ext (hinit q hq) hD
    have hQbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
        ‖iteratedFDeriv ℝ j (fun v => Q (s, v)) q‖ ≤ 2 * C := by
      intro j hj s hs q hq
      exact (norm_iteratedFDeriv_augment_le hW hA (hUW ⟨hs, hq⟩) j).trans
        (mul_le_mul_of_nonneg_left
          (max_le (hbound j (hj.trans (Nat.le_succ n)) s hs q hq)
            (hbound (j + 1) (Nat.add_le_add_right hj 1) s hs q hq)) (by norm_num))
    have h := ih (F := F × (P →L[ℝ] F)) (mul_nonneg (by norm_num) hC)
      hQ hY hQY hYinit hQbound
    have hz : (t, p) ∈ W := hUW ⟨ht, hp⟩
    have hyp : ContDiffAt ℝ ∞ (fun q => y (t, q)) p :=
      ((hy _ hz).contDiffAt (hW.mem_nhds hz)).comp p
        (contDiffAt_const.prodMk contDiffAt_id)
    have hdyp : ContDiffAt ℝ ∞ (fun q => parameterFDeriv y (t, q)) p :=
      (((contDiffOn_parameterFDeriv hW hy) _ hz).contDiffAt (hW.mem_nhds hz)).comp p
        (contDiffAt_const.prodMk contDiffAt_id)
    change ‖iteratedFDeriv ℝ n (fun q => (y (t, q), parameterFDeriv y (t, q))) p‖ ≤ _ at h
    rw [iteratedFDeriv_prodMk hyp hdyp (ENat.natCast_le_of_coe_top_le_withTop le_rfl n),
      ContinuousMultilinearMap.opNorm_prod,
      norm_iteratedFDeriv_parameterFDeriv_slice hW hy hz n] at h
    have hfinal := (le_max_right _ _).trans h
    simpa [Prod.norm_def, pow_succ, mul_assoc] using hfinal

end Poincare.ODE.Linear
