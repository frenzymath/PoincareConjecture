import PoincareConjecture.Proofs.M03.Existence.DeTurckTameCompositionNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckInverseCompositionNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckTameRemainderNative

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.DeTurckQuasilinearEstimateNative

open TensorProbeNative DeTurckTameCompositionNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type*} [Fintype iota]

private theorem directionalWord_add
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota) {f g : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) :
    directionalWord F w (fun x => f x + g x) =
      fun x => directionalWord F w f x + directionalWord F w g x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    rw [directionalWord_cons, ih]
    exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (F i x))
      (mfderiv_add
        ((directionalWord_contMDiff F w hf).mdifferentiable (by simp) x)
        ((directionalWord_contMDiff F w hg).mdifferentiable (by simp) x))

private theorem directionalWord_sub
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota) {f g : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) :
    directionalWord F w (fun x => f x - g x) =
      fun x => directionalWord F w f x - directionalWord F w g x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    rw [directionalWord_cons, ih]
    exact scalarDirectional_sub (F i)
      ((directionalWord_contMDiff F w hf).mdifferentiable (by simp) x)
      ((directionalWord_contMDiff F w hg).mdifferentiable (by simp) x)

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsFiniteMeasure μ]

private theorem memLp_continuous {f : M → ℝ} (hf : Continuous f) : MemLp f 2 μ :=
  ContinuousMap.memLp (p := 2) (μ := μ) ℝ (⟨f, hf⟩ : C(M, ℝ))

private theorem lpNorm_mul_le_sup {f g : M → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ x, ‖f x‖ ≤ a) :
    lpNorm (fun x => f x * g x) 2 μ ≤ a * lpNorm g 2 μ := by
  have hdom : MemLp (fun x => a * ‖g x‖) 2 μ :=
    (memLp_continuous μ hg).norm.const_mul a
  calc
    _ ≤ lpNorm (fun x => a * ‖g x‖) 2 μ := by
      apply lpNorm_mono_real hdom
      intro x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
    _ = a * lpNorm g 2 μ := by
      have heq : (fun x => a * ‖g x‖) = a • (fun x => ‖g x‖) := rfl
      rw [heq, lpNorm_const_smul, lpNorm_norm hg.aestronglyMeasurable]
      simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg ha]

private theorem lpNorm_list_sum_le {jota : Type*} (l : List jota) (f : jota → M → ℝ)
    (hf : ∀ j ∈ l, Continuous (f j)) :
    lpNorm (fun x => (l.map (fun j => f j x)).sum) 2 μ ≤
      (l.map (fun j => lpNorm (f j) 2 μ)).sum := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (lpNorm_add_le (memLp_continuous μ (hf j List.mem_cons_self))
      (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (add_le_add_right (ih (fun k hk => hf k (List.mem_cons_of_mem j hk))) _)

theorem lpNorm_directionalWord_mul_second_le
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (w : List iota)
    (hw : w.length ≤ 2 * r) (i j : iota) {f u : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfLow : ∀ v : List iota, v.length ≤ r → ∀ x,
      ‖directionalWord F v f x‖ ≤ a)
    (huLow : ∀ v : List iota, v.length ≤ r + 1 → ∀ x,
      ‖directionalWord F v u x‖ ≤ b)
    (hfHigh : ∀ v : List iota, v.length ≤ 2 * r →
      lpNorm (directionalWord F v f) 2 μ ≤ A)
    (huHigh : ∀ v : List iota, v.length ≤ 2 * r + 2 →
      lpNorm (directionalWord F v u) 2 μ ≤ B) :
    lpNorm (directionalWord F w
      (fun x => f x * directionalWord F [i, j] u x)) 2 μ ≤
      (2 : ℝ) ^ w.length * (a * B + b * A) := by
  have hsecond := directionalWord_contMDiff F [i, j] hu
  have heq : directionalWord F w (fun x => f x * directionalWord F [i, j] u x) =
      fun x => ((splitDirectionalWord w).map (fun p =>
        directionalWord F p.1 f x * directionalWord F p.2
          (directionalWord F [i, j] u) x)).sum :=
    funext (directionalWord_mul F w hf hsecond)
  rw [heq]
  apply (lpNorm_list_sum_le μ (splitDirectionalWord w)
    (fun p x => directionalWord F p.1 f x * directionalWord F p.2
      (directionalWord F [i, j] u) x)
    (fun p _ => (directionalWord_contMDiff F p.1 hf).continuous.mul
      (directionalWord_contMDiff F p.2 hsecond).continuous)).trans
  have hterm (p : List iota × List iota) (hp : p ∈ splitDirectionalWord w) :
      lpNorm (fun x => directionalWord F p.1 f x * directionalWord F p.2
        (directionalWord F [i, j] u) x) 2 μ ≤ a * B + b * A := by
    have hlength := splitDirectionalWord_order w p hp
    by_cases hleft : p.1.length ≤ r
    · have hright : (p.2 ++ [i, j]).length ≤ 2 * r + 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hhigh : lpNorm (directionalWord F p.2
          (directionalWord F [i, j] u)) 2 μ ≤ B := by
        simpa only [directionalWord_append] using huHigh (p.2 ++ [i, j]) hright
      apply ((lpNorm_mul_le_sup μ (directionalWord_contMDiff F p.1 hf).continuous
        (directionalWord_contMDiff F p.2 hsecond).continuous ha
        (hfLow p.1 hleft)).trans (mul_le_mul_of_nonneg_left hhigh ha)).trans
      exact le_add_of_nonneg_right (mul_nonneg hb hA)
    · have hright : (p.2 ++ [i, j]).length ≤ r + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hlow : ∀ x, ‖directionalWord F p.2
          (directionalWord F [i, j] u) x‖ ≤ b := by
        simpa only [directionalWord_append] using huLow (p.2 ++ [i, j]) hright
      have hcomm : (fun x => directionalWord F p.1 f x * directionalWord F p.2
          (directionalWord F [i, j] u) x) =
          (fun x => directionalWord F p.2 (directionalWord F [i, j] u) x *
            directionalWord F p.1 f x) := by
        funext x
        exact mul_comm _ _
      rw [hcomm]
      apply ((lpNorm_mul_le_sup μ (directionalWord_contMDiff F p.2 hsecond).continuous
        (directionalWord_contMDiff F p.1 hf).continuous hb hlow).trans
        (mul_le_mul_of_nonneg_left (hfHigh p.1 (by omega)) hb)).trans
      exact le_add_of_nonneg_left (mul_nonneg ha hB)
  calc
    _ ≤ ((splitDirectionalWord w).map (fun _ => a * B + b * A)).sum :=
      List.sum_le_sum hterm
    _ = (2 : ℝ) ^ w.length * (a * B + b * A) := by
      have hconst (l : List (List iota × List iota)) :
          (l.map (fun _ => a * B + b * A)).sum =
            (l.length : ℝ) * (a * B + b * A) := by
        induction l with
        | nil => simp
        | cons p l ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons,
            Nat.cast_add, Nat.cast_one, ih]
          ring
      rw [hconst, splitDirectionalWord_length, Nat.cast_pow, Nat.cast_ofNat]

theorem lpNorm_directionalWord_principal_sub_le
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (w : List iota)
    (hw : w.length ≤ 2 * r) (i j : iota) {f g u v : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    {a b c d A B C D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfLow : ∀ z : List iota, z.length ≤ r → ∀ x,
      ‖directionalWord F z f x‖ ≤ a)
    (huvLow : ∀ z : List iota, z.length ≤ r + 1 → ∀ x,
      ‖directionalWord F z (fun y => u y - v y) x‖ ≤ b)
    (hfgLow : ∀ z : List iota, z.length ≤ r → ∀ x,
      ‖directionalWord F z (fun y => f y - g y) x‖ ≤ c)
    (hvLow : ∀ z : List iota, z.length ≤ r + 1 → ∀ x,
      ‖directionalWord F z v x‖ ≤ d)
    (hfHigh : ∀ z : List iota, z.length ≤ 2 * r →
      lpNorm (directionalWord F z f) 2 μ ≤ A)
    (huvHigh : ∀ z : List iota, z.length ≤ 2 * r + 2 →
      lpNorm (directionalWord F z (fun y => u y - v y)) 2 μ ≤ B)
    (hfgHigh : ∀ z : List iota, z.length ≤ 2 * r →
      lpNorm (directionalWord F z (fun y => f y - g y)) 2 μ ≤ C)
    (hvHigh : ∀ z : List iota, z.length ≤ 2 * r + 2 →
      lpNorm (directionalWord F z v) 2 μ ≤ D) :
    lpNorm (directionalWord F w (fun x =>
      f x * directionalWord F [i, j] u x -
        g x * directionalWord F [i, j] v x)) 2 μ ≤
      (2 : ℝ) ^ w.length * ((a * B + b * A) + (c * D + d * C)) := by
  let P : M → ℝ := fun x => f x * directionalWord F [i, j] (fun y => u y - v y) x
  let Q : M → ℝ := fun x => (f x - g x) * directionalWord F [i, j] v x
  have hP : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ P :=
    hf.mul (directionalWord_contMDiff F [i, j] (hu.sub hv))
  have hQ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ Q :=
    (hf.sub hg).mul (directionalWord_contMDiff F [i, j] hv)
  have heq : (fun x => f x * directionalWord F [i, j] u x -
      g x * directionalWord F [i, j] v x) = fun x => P x + Q x := by
    funext x
    dsimp only [P, Q]
    rw [directionalWord_sub F [i, j] hu hv]
    ring
  rw [heq, directionalWord_add F w hP hQ]
  have hfirst := lpNorm_directionalWord_mul_second_le μ F r w hw i j hf (hu.sub hv)
    ha hb hA hB hfLow huvLow hfHigh huvHigh
  have hsecond := lpNorm_directionalWord_mul_second_le μ F r w hw i j (hf.sub hg) hv
    hc hd hC hD hfgLow hvLow hfgHigh hvHigh
  calc
    _ ≤ lpNorm (directionalWord F w P) 2 μ + lpNorm (directionalWord F w Q) 2 μ :=
      lpNorm_add_le
        (memLp_continuous μ (directionalWord_contMDiff F w hP).continuous)
        (by norm_num : (1 : ENNReal) ≤ 2)
    _ ≤ (2 : ℝ) ^ w.length * (a * B + b * A) +
        (2 : ℝ) ^ w.length * (c * D + d * C) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem lpNorm_directionalWord_principal_sub_mixed_le
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (w : List iota)
    (hw : w.length ≤ 2 * r) (i j : iota) {f g u v : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    {A B tu tv td Hd Hv : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (htu : 0 ≤ tu) (htv : 0 ≤ tv)
    (htd : 0 ≤ td) (hHd : 0 ≤ Hd) (hHv : 0 ≤ Hv)
    (htraceDiff : td ≤ Hd) (htraceRight : tv ≤ Hv)
    (hfLow : ∀ z : List iota, z.length ≤ r → ∀ x,
      ‖directionalWord F z f x‖ ≤ A * tu)
    (huvLow : ∀ z : List iota, z.length ≤ r + 1 → ∀ x,
      ‖directionalWord F z (fun y => u y - v y) x‖ ≤ B * td)
    (hfgLow : ∀ z : List iota, z.length ≤ r → ∀ x,
      ‖directionalWord F z (fun y => f y - g y) x‖ ≤ A * td)
    (hvLow : ∀ z : List iota, z.length ≤ r + 1 → ∀ x,
      ‖directionalWord F z v x‖ ≤ B * tv)
    (hfHigh : ∀ z : List iota, z.length ≤ 2 * r →
      lpNorm (directionalWord F z f) 2 μ ≤ A * tu)
    (huvHigh : ∀ z : List iota, z.length ≤ 2 * r + 2 →
      lpNorm (directionalWord F z (fun y => u y - v y)) 2 μ ≤ B * Hd)
    (hfgHigh : ∀ z : List iota, z.length ≤ 2 * r →
      lpNorm (directionalWord F z (fun y => f y - g y)) 2 μ ≤ A * td)
    (hvHigh : ∀ z : List iota, z.length ≤ 2 * r + 2 →
      lpNorm (directionalWord F z v) 2 μ ≤ B * Hv) :
    lpNorm (directionalWord F w (fun x =>
      f x * directionalWord F [i, j] u x -
        g x * directionalWord F [i, j] v x)) 2 μ ≤
      (2 : ℝ) ^ (w.length + 1) * A * B * (max tu tv * Hd + td * Hv) := by
  have h := lpNorm_directionalWord_principal_sub_le μ F r w hw i j hf hg hu hv
    (mul_nonneg hA htu) (mul_nonneg hB htd) (mul_nonneg hA htd) (mul_nonneg hB htv)
    (mul_nonneg hA htu) (mul_nonneg hB hHd) (mul_nonneg hA htd) (mul_nonneg hB hHv)
    hfLow huvLow hfgLow hvLow hfHigh huvHigh hfgHigh hvHigh
  have hcross1 : td * tu ≤ tu * Hd := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left htraceDiff htu
  have hcross2 : tv * td ≤ td * Hv := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left htraceRight htd
  have hfirst : tu * Hd ≤ max tu tv * Hd :=
    mul_le_mul_of_nonneg_right (le_max_left tu tv) hHd
  have hsum : tu * Hd + td * tu + td * Hv + tv * td ≤
      2 * (max tu tv * Hd + td * Hv) := by linarith
  have hfactor : 0 ≤ (2 : ℝ) ^ w.length * A * B := by positivity
  calc
    _ ≤ (2 : ℝ) ^ w.length * ((A * tu * (B * Hd) + B * td * (A * tu)) +
        (A * td * (B * Hv) + B * tv * (A * td))) := h
    _ = (2 : ℝ) ^ w.length * A * B *
        (tu * Hd + td * tu + td * Hv + tv * td) := by ring
    _ ≤ (2 : ℝ) ^ w.length * A * B *
        (2 * (max tu tv * Hd + td * Hv)) := mul_le_mul_of_nonneg_left hsum hfactor
    _ = _ := by rw [pow_succ]; ring

private theorem directionalWord_const_mul
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota) (c : ℝ) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    directionalWord F w (fun x => c * f x) = fun x => c * directionalWord F w f x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    rw [directionalWord_cons, ih]
    change scalarDirectional (F i) (fun y => c * directionalWord F w f y) x =
      c * scalarDirectional (F i) (directionalWord F w f) x
    have hc : scalarDirectional (F i) (fun _ : M => c) x = 0 := by
      simp only [scalarDirectional, mfderiv_const, ContinuousLinearMap.zero_apply]
    simpa only [hc, mul_zero, add_zero] using
      (scalarDirectional_mul (F i) (ψ := fun _ : M => c)
        (f := directionalWord F w f) mdifferentiableAt_const
        ((directionalWord_contMDiff F w hf).mdifferentiable (by simp) x))

structure ScalarDerivativeBounds
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (C : ℝ) (f : M → ℝ) : Prop where
  nonneg : 0 ≤ C
  smooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f
  low : ∀ w : List iota, w.length ≤ r → ∀ x, ‖directionalWord F w f x‖ ≤ C
  high : ∀ w : List iota, w.length ≤ 2 * r → lpNorm (directionalWord F w f) 2 μ ≤ C

namespace ScalarDerivativeBounds

variable {μ} {F : iota → SmoothField (n := n) (M := M)} {r : ℕ}
  {C D : ℝ} {f g : M → ℝ}

theorem zero : ScalarDerivativeBounds μ F r 0 (fun _ : M => 0) := by
  have hz (w : List iota) : directionalWord F w (fun _ : M => (0 : ℝ)) = 0 := by
    induction w with
    | nil => rfl
    | cons i w ih =>
      simp only [directionalWord_cons, ih]
      funext x
      exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (F i x))
        (mfderiv_const (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (c := (0 : ℝ)))
  refine ⟨le_rfl, contMDiff_const, ?_, ?_⟩
  · intro w _ x
    simp only [hz, Pi.zero_apply, norm_zero, le_refl]
  · intro w _
    simp only [hz, lpNorm_zero, le_refl]

theorem add (hf : ScalarDerivativeBounds μ F r C f)
    (hg : ScalarDerivativeBounds μ F r D g) :
    ScalarDerivativeBounds μ F r (C + D) (fun x => f x + g x) := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, hf.smooth.add hg.smooth, ?_, ?_⟩
  · intro w hw x
    rw [directionalWord_add F w hf.smooth hg.smooth]
    exact (norm_add_le _ _).trans (add_le_add (hf.low w hw x) (hg.low w hw x))
  · intro w hw
    rw [directionalWord_add F w hf.smooth hg.smooth]
    exact (lpNorm_add_le
      (memLp_continuous μ (directionalWord_contMDiff F w hf.smooth).continuous)
      (by norm_num : (1 : ENNReal) ≤ 2)).trans (add_le_add (hf.high w hw) (hg.high w hw))

theorem sub (hf : ScalarDerivativeBounds μ F r C f)
    (hg : ScalarDerivativeBounds μ F r D g) :
    ScalarDerivativeBounds μ F r (C + D) (fun x => f x - g x) := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, hf.smooth.sub hg.smooth, ?_, ?_⟩
  · intro w hw x
    rw [directionalWord_sub F w hf.smooth hg.smooth]
    exact (norm_sub_le _ _).trans (add_le_add (hf.low w hw x) (hg.low w hw x))
  · intro w hw
    rw [directionalWord_sub F w hf.smooth hg.smooth]
    exact (lpNorm_sub_le
      (memLp_continuous μ (directionalWord_contMDiff F w hf.smooth).continuous)
      (by norm_num : (1 : ENNReal) ≤ 2)).trans (add_le_add (hf.high w hw) (hg.high w hw))

theorem scale (hf : ScalarDerivativeBounds μ F r C f) (c : ℝ) :
    ScalarDerivativeBounds μ F r (|c| * C) (fun x => c * f x) := by
  refine ⟨mul_nonneg (abs_nonneg c) hf.nonneg, contMDiff_const.mul hf.smooth, ?_, ?_⟩
  · intro w hw x
    rw [directionalWord_const_mul F w c hf.smooth, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf.low w hw x) (abs_nonneg c)
  · intro w hw
    rw [directionalWord_const_mul F w c hf.smooth]
    have heq : (fun x => c * directionalWord F w f x) = c • directionalWord F w f := rfl
    rw [heq, lpNorm_const_smul]
    simpa only [coe_nnnorm, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (hf.high w hw) (abs_nonneg c)

theorem mul (hf : ScalarDerivativeBounds μ F r C f)
    (hg : ScalarDerivativeBounds μ F r D g) :
    ScalarDerivativeBounds μ F r ((2 : ℝ) ^ (2 * r + 1) * C * D)
      (fun x => f x * g x) := by
  refine ⟨mul_nonneg (mul_nonneg (by positivity) hf.nonneg) hg.nonneg,
    hf.smooth.mul hg.smooth, ?_, ?_⟩
  · intro w hw x
    apply (DeTurckInverseCompositionNative.norm_directionalWord_mul_le F r w hw
      hf.smooth hg.smooth hf.nonneg hg.nonneg hf.low hg.low x).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (by omega : r ≤ 2 * r + 1)) hf.nonneg) hg.nonneg
  · intro w hw
    have h := lpNorm_directionalWord_mul_le μ F (2 * r) w hw hf.smooth hg.smooth
      hf.nonneg hg.nonneg hf.nonneg hg.nonneg
      (fun z hz => hf.low z (by omega)) (fun z hz => hg.low z (by omega)) hf.high hg.high
    calc
      _ ≤ (2 : ℝ) ^ w.length * (C * D + D * C) := h
      _ ≤ (2 : ℝ) ^ (2 * r) * (C * D + D * C) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw)
          (add_nonneg (mul_nonneg hf.nonneg hg.nonneg) (mul_nonneg hg.nonneg hf.nonneg))
      _ = _ := by rw [pow_succ]; ring

theorem finSum {q : ℕ} (f : Fin q → M → ℝ)
    (hf : ∀ i, ScalarDerivativeBounds μ F r C (f i)) :
    ScalarDerivativeBounds μ F r ((q : ℝ) * C) (fun x => ∑ i, f i x) := by
  have hC : 0 ≤ (q : ℝ) * C := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      (Finset.sum_nonneg (s := Finset.univ) (fun i _ => (hf i).nonneg))
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => ∑ i, f i x) :=
    ContMDiff.sum (t := Finset.univ) (fun i _ => (hf i).smooth)
  have heq (w : List iota) : directionalWord F w (fun x => ∑ i, f i x) =
      fun x => ∑ i, directionalWord F w (f i) x :=
    funext (DeTurckInverseCompositionNative.directionalWord_sum Finset.univ F w f
      (fun i _ => (hf i).smooth))
  refine ⟨hC, hs, ?_, ?_⟩
  · intro w hw x
    rw [heq]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin q, C := Finset.sum_le_sum (fun i _ => (hf i).low w hw x)
      _ = _ := by simp
  · intro w hw
    rw [heq]
    have heqSum : (fun x => ∑ i, directionalWord F w (f i) x) =
        ∑ i, directionalWord F w (f i) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heqSum]
    apply (lpNorm_sum_le (s := Finset.univ)
      (fun i _ => memLp_continuous μ
        (directionalWord_contMDiff F w (hf i).smooth).continuous)
      (by norm_num : (1 : ENNReal) ≤ 2)).trans
    calc
      _ ≤ ∑ _i : Fin q, C := Finset.sum_le_sum (fun i _ => (hf i).high w hw)
      _ = _ := by simp

end ScalarDerivativeBounds

def budgetProduct (r : ℕ) (a b : ℝ × ℝ) : ℝ × ℝ :=
  ((2 : ℝ) ^ (2 * r + 1) * a.1 * b.1,
    (2 : ℝ) ^ (2 * r + 1) * (a.2 * b.1 + a.1 * b.2))

def budgetScale (c : ℝ) (a : ℝ × ℝ) : ℝ × ℝ := (|c| * a.1, |c| * a.2)

def budgetSum (q : ℕ) (a : ℝ × ℝ) : ℝ × ℝ := ((q : ℝ) * a.1, (q : ℝ) * a.2)

structure ScalarDifferenceBounds
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (δ : ℝ)
    (a : ℝ × ℝ) (f g : M → ℝ) : Prop where
  slope_nonneg : 0 ≤ a.2
  left : ScalarDerivativeBounds μ F r a.1 f
  right : ScalarDerivativeBounds μ F r a.1 g
  difference : ScalarDerivativeBounds μ F r (a.2 * δ) (fun x => f x - g x)

namespace ScalarDifferenceBounds

variable {μ} {F : iota → SmoothField (n := n) (M := M)} {r : ℕ} {δ : ℝ}
  {a b : ℝ × ℝ} {f g h k : M → ℝ}

theorem refl {C : ℝ} (hf : ScalarDerivativeBounds μ F r C f) :
    ScalarDifferenceBounds μ F r δ (C, 0) f f := by
  refine ⟨le_rfl, hf, hf, ?_⟩
  simpa only [sub_self, zero_mul] using
    (ScalarDerivativeBounds.zero (μ := μ) (F := F) (r := r))

theorem add (hf : ScalarDifferenceBounds μ F r δ a f g)
    (hh : ScalarDifferenceBounds μ F r δ b h k) :
    ScalarDifferenceBounds μ F r δ (a + b) (fun x => f x + h x) (fun x => g x + k x) := by
  refine ⟨add_nonneg hf.slope_nonneg hh.slope_nonneg, hf.left.add hh.left,
    hf.right.add hh.right, ?_⟩
  convert hf.difference.add hh.difference using 1 <;>
    first | (dsimp only [Prod.fst_add, Prod.snd_add]; ring) | (funext x; ring)

theorem sub (hf : ScalarDifferenceBounds μ F r δ a f g)
    (hh : ScalarDifferenceBounds μ F r δ b h k) :
    ScalarDifferenceBounds μ F r δ (a + b) (fun x => f x - h x) (fun x => g x - k x) := by
  refine ⟨add_nonneg hf.slope_nonneg hh.slope_nonneg, hf.left.sub hh.left,
    hf.right.sub hh.right, ?_⟩
  convert hf.difference.sub hh.difference using 1 <;>
    first | (dsimp only [Prod.fst_add, Prod.snd_add]; ring) | (funext x; ring)

theorem scale (hf : ScalarDifferenceBounds μ F r δ a f g) (c : ℝ) :
    ScalarDifferenceBounds μ F r δ (budgetScale c a)
      (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨mul_nonneg (abs_nonneg c) hf.slope_nonneg, hf.left.scale c,
    hf.right.scale c, ?_⟩
  convert hf.difference.scale c using 1 <;>
    first | (dsimp only [budgetScale]; ring) | (funext x; ring)

theorem neg (hf : ScalarDifferenceBounds μ F r δ a f g) :
    ScalarDifferenceBounds μ F r δ a (fun x => -f x) (fun x => -g x) := by
  simpa only [budgetScale, abs_neg, abs_one, one_mul, neg_one_mul] using
    hf.scale (-1)

theorem mul (hf : ScalarDifferenceBounds μ F r δ a f g)
    (hh : ScalarDifferenceBounds μ F r δ b h k) :
    ScalarDifferenceBounds μ F r δ (budgetProduct r a b)
      (fun x => f x * h x) (fun x => g x * k x) := by
  refine ⟨mul_nonneg (by positivity)
      (add_nonneg (mul_nonneg hf.slope_nonneg hh.left.nonneg)
        (mul_nonneg hf.left.nonneg hh.slope_nonneg)),
    hf.left.mul hh.left, hf.right.mul hh.right, ?_⟩
  convert (hf.difference.mul hh.left).add (hf.right.mul hh.difference) using 1 <;>
    first | (dsimp only [budgetProduct]; ring) | (funext x; ring)

theorem finSum {q : ℕ} (f g : Fin q → M → ℝ)
    (hf : ∀ i, ScalarDifferenceBounds μ F r δ a (f i) (g i)) :
    ScalarDifferenceBounds μ F r δ (budgetSum q a)
      (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) := by
  have hL : 0 ≤ (q : ℝ) * a.2 := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      (Finset.sum_nonneg (s := Finset.univ) (fun i _ => (hf i).slope_nonneg))
  refine ⟨hL, ScalarDerivativeBounds.finSum f (fun i => (hf i).left),
    ScalarDerivativeBounds.finSum g (fun i => (hf i).right), ?_⟩
  have h := ScalarDerivativeBounds.finSum (fun i x => f i x - g i x)
    (fun i => (hf i).difference)
  simpa only [budgetSum, Finset.sum_sub_distrib, mul_assoc] using h

end ScalarDifferenceBounds

def christoffelBudget (q r : ℕ) (p a : ℝ × ℝ) : ℝ × ℝ :=
  budgetScale (1 / 2) (budgetSum q (budgetProduct r a (p + p + p)))

def inverseFirstBudget (q r : ℕ) (p a : ℝ × ℝ) : ℝ × ℝ :=
  budgetSum q (budgetSum q (budgetProduct r (budgetProduct r a p) a))

def ricciLowerBudget (q r : ℕ) (gamma gamma1 : ℝ × ℝ) : ℝ × ℝ :=
  budgetSum q ((gamma1 + gamma1) +
    budgetSum q (budgetProduct r gamma gamma + budgetProduct r gamma gamma))

def deTurckBudget (q r : ℕ) (a gamma : ℝ × ℝ) (c : ℝ) : ℝ × ℝ :=
  budgetSum q (budgetSum q (budgetProduct r a (gamma + (c, 0))))

def deTurckFirstBudget (q r : ℕ) (a inverse1 gamma gamma1 : ℝ × ℝ)
    (c c1 : ℝ) : ℝ × ℝ :=
  budgetSum q (budgetSum q (budgetProduct r inverse1 (gamma + (c, 0)) +
    budgetProduct r a (gamma1 + (c1, 0))))

def lieLowerBudget (q r : ℕ) (v p W W1 : ℝ × ℝ) : ℝ × ℝ :=
  budgetSum q (budgetProduct r W p + budgetProduct r v W1 + budgetProduct r v W1)

def lowerJetSourceBudget (q r : ℕ) (v p a : ℝ × ℝ) (c c1 : ℝ) : ℝ × ℝ :=
  let gamma := christoffelBudget q r p a
  let inverse1 := inverseFirstBudget q r p a
  let gamma1 := christoffelBudget q r p inverse1
  let ricci := ricciLowerBudget q r gamma gamma1
  let W := deTurckBudget q r a gamma c
  let W1 := deTurckFirstBudget q r a inverse1 gamma gamma1 c c1
  budgetScale (-2) ricci + lieLowerBudget q r v p W W1

theorem lowerJetSource_directional_difference_bounds
    (F : iota → SmoothField (n := n) (M := M)) (r : ℕ) (δ : ℝ)
    (v p a : ℝ × ℝ) (c c1 : ℝ)
    (background : M → DeTurckNative.MetricJet2 (n := n))
    (G H : M → DeTurckNative.MetricLowerJet n)
    (hvalue : ∀ i j : Fin n, ScalarDifferenceBounds μ F r δ v
      (fun x => (G x).1 i j) (fun x => (H x).1 i j))
    (hfirst : ∀ b i j : Fin n, ScalarDifferenceBounds μ F r δ p
      (fun x => (G x).2 b i j) (fun x => (H x).2 b i j))
    (hinverse : ∀ i j : Fin n, ScalarDifferenceBounds μ F r δ a
      (fun x => (G x).1⁻¹ i j) (fun x => (H x).1⁻¹ i j))
    (hbackground : ∀ k i j : Fin n, ScalarDerivativeBounds μ F r c
      (fun x => DeTurckNative.christoffelJet (background x) k i j))
    (hbackground1 : ∀ b k i j : Fin n, ScalarDerivativeBounds μ F r c1
      (fun x => DeTurckNative.christoffelSecond (background x) b k i j)) :
    ∀ i j : Fin n, ScalarDifferenceBounds μ F r δ (lowerJetSourceBudget n r v p a c c1)
      (fun x => DeTurckNative.lowerJetSource (background x) (G x) i j)
      (fun x => DeTurckNative.lowerJetSource (background x) (H x) i j) := by
  let JG : M → DeTurckNative.MetricJet2 (n := n) :=
    fun x => DeTurckNative.chartStateJet (DeTurckNative.lowerJetState (G x) 0)
  let JH : M → DeTurckNative.MetricJet2 (n := n) :=
    fun x => DeTurckNative.chartStateJet (DeTurckNative.lowerJetState (H x) 0)
  let gamma := christoffelBudget n r p a
  let inverse1 := inverseFirstBudget n r p a
  let gamma1 := christoffelBudget n r p inverse1
  let ricci := ricciLowerBudget n r gamma gamma1
  let W := deTurckBudget n r a gamma c
  let W1 := deTurckFirstBudget n r a inverse1 gamma gamma1 c c1
  have hgamma (k i j : Fin n) : ScalarDifferenceBounds μ F r δ gamma
      (fun x => DeTurckNative.christoffelJet (JG x) k i j)
      (fun x => DeTurckNative.christoffelJet (JH x) k i j) := by
    exact (ScalarDifferenceBounds.finSum _ _ (fun l =>
      (hinverse k l).mul (((hfirst i l j).add (hfirst j l i)).sub (hfirst l i j)))).scale
        (1 / 2)
  have hinverse1 (b k l : Fin n) : ScalarDifferenceBounds μ F r δ inverse1
      (fun x => DeTurckNative.inverseFirst (JG x) b k l)
      (fun x => DeTurckNative.inverseFirst (JH x) b k l) := by
    exact (ScalarDifferenceBounds.finSum _ _ (fun u =>
      ScalarDifferenceBounds.finSum _ _ (fun w =>
        ((hinverse k u).mul (hfirst b u w)).mul (hinverse w l)))).neg
  have hgamma1 (b k i j : Fin n) : ScalarDifferenceBounds μ F r δ gamma1
      (fun x => DeTurckNative.christoffelSecond (JG x) b k i j)
      (fun x => DeTurckNative.christoffelSecond (JH x) b k i j) := by
    have h := (ScalarDifferenceBounds.finSum _ _ (fun l =>
      (hinverse1 b k l).mul (((hfirst i l j).add (hfirst j l i)).sub (hfirst l i j)))).scale
        (1 / 2)
    simpa only [gamma1, christoffelBudget, DeTurckNative.christoffelSecond,
      JG, JH, DeTurckNative.chartStateJet, DeTurckNative.lowerJetState,
      Pi.zero_apply, Matrix.zero_apply,
      add_zero, sub_zero, mul_zero] using h
  have hricci (i j : Fin n) : ScalarDifferenceBounds μ F r δ ricci
      (fun x => DeTurckNative.ricciJet (JG x) i j)
      (fun x => DeTurckNative.ricciJet (JH x) i j) := by
    exact ScalarDifferenceBounds.finSum _ _ (fun k =>
      ((hgamma1 k k i j).sub (hgamma1 i k k j)).add
        (ScalarDifferenceBounds.finSum _ _ (fun l =>
          ((hgamma l i j).mul (hgamma k k l)).sub
            ((hgamma l k j).mul (hgamma k i l)))))
  have hW (k : Fin n) : ScalarDifferenceBounds μ F r δ W
      (fun x => DeTurckNative.deTurckVector (background x) (JG x) k)
      (fun x => DeTurckNative.deTurckVector (background x) (JH x) k) := by
    exact ScalarDifferenceBounds.finSum _ _ (fun b =>
      ScalarDifferenceBounds.finSum _ _ (fun d =>
        (hinverse b d).mul ((hgamma k b d).sub (ScalarDifferenceBounds.refl (hbackground k b d)))))
  have hW1 (b k : Fin n) : ScalarDifferenceBounds μ F r δ W1
      (fun x => DeTurckNative.deTurckVectorFirst (background x) (JG x) b k)
      (fun x => DeTurckNative.deTurckVectorFirst (background x) (JH x) b k) := by
    exact ScalarDifferenceBounds.finSum _ _ (fun u =>
      ScalarDifferenceBounds.finSum _ _ (fun w =>
        ((hinverse1 b u w).mul
          ((hgamma k u w).sub (ScalarDifferenceBounds.refl (hbackground k u w)))).add
        ((hinverse u w).mul
          ((hgamma1 b k u w).sub (ScalarDifferenceBounds.refl (hbackground1 b k u w))))))
  intro i j
  exact ((hricci i j).scale (-2)).add (ScalarDifferenceBounds.finSum _ _ (fun k =>
    (((hW k).mul (hfirst k i j)).add ((hvalue k j).mul (hW1 i k))).add
      ((hvalue i k).mul (hW1 j k))))

private theorem scalarDirectional_finset_sum_at {jota : Type*} (s : Finset jota)
    (V : SmoothField (n := n) (M := M)) (f : jota → M → ℝ) (x : M)
    (hf : ∀ j ∈ s, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j) x) :
    scalarDirectional V (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, scalarDirectional V (f j) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, scalarDirectional, mfderiv_const,
      ContinuousLinearMap.zero_apply, Pi.zero_apply]
    rfl
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ∑ k ∈ s, f k y) x :=
      ContMDiffAt.sum (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    have hsum := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (V x))
      (mfderiv_add ((hf j (Finset.mem_insert_self j s)).mdifferentiableAt (by simp))
        (hs.mdifferentiableAt (by simp)))
    change scalarDirectional V (fun y => f j y + ∑ k ∈ s, f k y) x =
      scalarDirectional V (f j) x + scalarDirectional V (fun y => ∑ k ∈ s, f k y) x at hsum
    rw [hsum, ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))]

theorem second_derivative_eq_of_field_sum
    {alpha : Type*} (F : iota → SmoothField (n := n) (M := M))
    (V : alpha → (x : M) → TangentSpace (𝓡 n) x) (c : alpha → iota → M → ℝ)
    {U : Set M} (hU : IsOpen U)
    (hc : ∀ a i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (c a i) U)
    (hV : ∀ a x, x ∈ U → V a x = ∑ i, c a i x • F i x)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (a b : alpha) {x : M} (hx : x ∈ U) :
    (show ℝ from mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => (show ℝ from mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f y (V b y))) x (V a x)) =
      (∑ i, ∑ j, c a i x * c b j x * directionalWord F [i, j] f x) +
        ∑ i, ∑ j, c a i x * scalarDirectional (F i) (c b j) x *
          scalarDirectional (F j) f x := by
  classical
  let q : M → ℝ := fun y => mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f y (V b y)
  have hexpand (s : M → ℝ) (d : alpha) (y : M) (hy : y ∈ U) :
      (show ℝ from mfderiv (𝓡 n) 𝓘(ℝ, ℝ) s y (V d y)) =
        ∑ i, c d i y * scalarDirectional (F i) s y := by
    rw [hV d y hy, map_sum]
    simp only [map_smul, smul_eq_mul, scalarDirectional]
  have hlocal : q =ᶠ[𝓝 x] fun y => ∑ j, c b j y * scalarDirectional (F j) f y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hexpand f b y hy
  have hcAt (j : iota) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (c b j) x :=
    (hc b j).contMDiffAt (hU.mem_nhds hx)
  have hdf (j : iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional (F j) f) := by
    simpa only [directionalWord_cons, directionalWord_nil] using
      directionalWord_contMDiff F [j] hf
  have hinner (i : iota) : scalarDirectional (F i) q x =
      ∑ j, (c b j x * directionalWord F [i, j] f x +
        scalarDirectional (F i) (c b j) x * scalarDirectional (F j) f x) := by
    have heq := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (F i x))
      (hlocal.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))
    change scalarDirectional (F i) q x =
      scalarDirectional (F i) (fun y => ∑ j, c b j y * scalarDirectional (F j) f y) x at heq
    rw [heq, scalarDirectional_finset_sum_at Finset.univ (F i)
      (fun j y => c b j y * scalarDirectional (F j) f y) x
      (fun j _ => (hcAt j).mul (hdf j x))]
    apply Finset.sum_congr rfl
    intro j _
    rw [scalarDirectional_mul (F i) ((hcAt j).mdifferentiableAt (by simp))
      ((hdf j x).mdifferentiableAt (by simp))]
    simp only [directionalWord_cons, directionalWord_nil]
    ring
  change (show ℝ from mfderiv (𝓡 n) 𝓘(ℝ, ℝ) q x (V a x)) = _
  rw [hexpand q a x hx]
  simp_rw [hinner, Finset.mul_sum, mul_add]
  simp only [Finset.sum_add_distrib, mul_assoc]

def differentiatedCoefficientSplits : List iota → List (List iota × List iota)
  | [] => []
  | i :: w =>
      (splitDirectionalWord w).map (fun p => (i :: p.1, p.2)) ++
        (differentiatedCoefficientSplits w).map (fun p => (p.1, i :: p.2))

theorem splitDirectionalWord_eq_differentiatedCoefficientSplits (w : List iota) :
    splitDirectionalWord w = differentiatedCoefficientSplits w ++ [([], w)] := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [splitDirectionalWord, differentiatedCoefficientSplits, ih,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc]

theorem differentiatedCoefficientSplits_order (w : List iota)
    (p : List iota × List iota) (hp : p ∈ differentiatedCoefficientSplits w) :
    0 < p.1.length ∧ p.1.length + p.2.length = w.length := by
  have hpos : 0 < p.1.length := by
    induction w generalizing p with
    | nil => simp only [differentiatedCoefficientSplits, List.not_mem_nil] at hp
    | cons i w ih =>
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        simp only [List.length_cons]
        omega
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact ih q hq
  have hmem : p ∈ splitDirectionalWord w := by
    rw [splitDirectionalWord_eq_differentiatedCoefficientSplits]
    exact List.mem_append_left _ hp
  exact ⟨hpos, splitDirectionalWord_order w p hmem⟩

theorem differentiatedCoefficientSplits_length (w : List iota) :
    (differentiatedCoefficientSplits w).length + 1 = 2 ^ w.length := by
  have h := congrArg List.length (splitDirectionalWord_eq_differentiatedCoefficientSplits w)
  simpa only [splitDirectionalWord_length, List.length_append, List.length_cons,
    List.length_nil, zero_add] using h.symm

theorem directionalWord_mul_top_split
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota) {a u : M → ℝ}
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u) (x : M) :
    directionalWord F w (fun y => a y * u y) x =
      a x * directionalWord F w u x +
        ((differentiatedCoefficientSplits w).map (fun p =>
          directionalWord F p.1 a x * directionalWord F p.2 u x)).sum := by
  rw [directionalWord_mul F w ha hu x,
    splitDirectionalWord_eq_differentiatedCoefficientSplits]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, directionalWord_nil]
  exact add_comm _ _

theorem lpNorm_directionalWord_mul_second_top_le
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota) (i j : iota)
    {a u : M → ℝ}
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    {epsilon A B : ℝ} (hepsilon : 0 ≤ epsilon) (hA : 0 ≤ A)
    (ha0 : ∀ x, ‖a x‖ ≤ epsilon)
    (haHigher : ∀ v : List iota, 0 < v.length → v.length ≤ w.length → ∀ x,
      ‖directionalWord F v a x‖ ≤ A)
    (huLower : ∀ v : List iota, v.length ≤ w.length + 1 →
      lpNorm (directionalWord F v u) 2 μ ≤ B) :
    lpNorm (directionalWord F w (fun x => a x * directionalWord F [i, j] u x)) 2 μ ≤
      epsilon * lpNorm (directionalWord F (w ++ [i, j]) u) 2 μ +
        (differentiatedCoefficientSplits w).length * (A * B) := by
  let l := differentiatedCoefficientSplits w
  let term : List iota × List iota → M → ℝ := fun p x =>
    directionalWord F p.1 a x * directionalWord F (p.2 ++ [i, j]) u x
  have hterm (p : List iota × List iota) : Continuous (term p) :=
    ((directionalWord_contMDiff F p.1 ha).mul
      (directionalWord_contMDiff F (p.2 ++ [i, j]) hu)).continuous
  have heq : directionalWord F w (fun x => a x * directionalWord F [i, j] u x) =
      fun x => a x * directionalWord F (w ++ [i, j]) u x +
        (l.map (fun p => term p x)).sum := by
    funext x
    simpa only [directionalWord_append, l, term] using
      directionalWord_mul_top_split F w ha (directionalWord_contMDiff F [i, j] hu) x
  have htail : lpNorm (fun x => (l.map (fun p => term p x)).sum) 2 μ ≤
      l.length * (A * B) := by
    calc
      _ ≤ (l.map (fun p => lpNorm (term p) 2 μ)).sum :=
        lpNorm_list_sum_le μ l term (fun p _ => hterm p)
      _ ≤ (l.map (fun _ => A * B)).sum := by
        apply List.sum_le_sum
        intro p hp
        obtain ⟨hpos, hlen⟩ := differentiatedCoefficientSplits_order w p hp
        have hlower : (p.2 ++ [i, j]).length ≤ w.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        exact (lpNorm_mul_le_sup μ (directionalWord_contMDiff F p.1 ha).continuous
          (directionalWord_contMDiff F (p.2 ++ [i, j]) hu).continuous hA
          (haHigher p.1 hpos (by omega))).trans
            (mul_le_mul_of_nonneg_left (huLower (p.2 ++ [i, j]) hlower) hA)
      _ = _ := by
        induction l with
        | nil => simp
        | cons p l ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons,
            Nat.cast_add, Nat.cast_one, ih]
          ring
  rw [heq]
  exact (lpNorm_add_le
    (memLp_continuous μ (ha.mul (directionalWord_contMDiff F (w ++ [i, j]) hu)).continuous)
    (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (add_le_add (lpNorm_mul_le_sup μ ha.continuous
        (directionalWord_contMDiff F (w ++ [i, j]) hu).continuous hepsilon ha0) htail)

theorem contracted_second_derivative_eq_of_field_sum
    {alpha : Type*} [Fintype alpha]
    (F : iota → SmoothField (n := n) (M := M))
    (V : alpha → (x : M) → TangentSpace (𝓡 n) x) (c : alpha → iota → M → ℝ)
    {U : Set M} (hU : IsOpen U)
    (hc : ∀ a i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (c a i) U)
    (hV : ∀ a x, x ∈ U → V a x = ∑ i, c a i x • F i x)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (q : alpha → alpha → ℝ) {x : M} (hx : x ∈ U) :
    (∑ a, ∑ b, q a b *
      (show ℝ from mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y => (show ℝ from mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f y (V b y))) x (V a x))) =
      (∑ a, ∑ b, ∑ i, ∑ j,
        (q a b * c a i x * c b j x) * directionalWord F [i, j] f x) +
      ∑ a, ∑ b, ∑ i, ∑ j,
        (q a b * c a i x * scalarDirectional (F i) (c b j) x) *
          scalarDirectional (F j) f x := by
  simp_rw [second_derivative_eq_of_field_sum F V c hU hc hV hf _ _ hx,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;>
    apply Finset.sum_congr rfl <;> intro b _ <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

end PoincareConjecture.DeTurckQuasilinearEstimateNative
