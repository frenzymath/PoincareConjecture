import PoincareConjecture.Proofs.M03.Existence.EuclideanMollificationNative
import PoincareConjecture.Proofs.M03.Existence.NativeDirectionalProductNative
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Convolution
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.DeTurckTameCompositionNative

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem weighted_integral_sq_le_mass {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w q : α → ℝ} (hw : Integrable w μ) (hwq : Integrable (fun x => w x * q x) μ)
    (hwq2 : Integrable (fun x => w x * q x ^ 2) μ) (hw0 : ∀ x, 0 ≤ w x) :
    (∫ x, w x * q x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * ∫ x, w x * q x ^ 2 ∂μ := by
  let m := ∫ x, w x ∂μ
  have hm0 : 0 ≤ m := integral_nonneg hw0
  by_cases hm : m = 0
  · have hwz : w =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg hw0 hw).mp hm
    have hwqz : (∫ x, w x * q x ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hwz] with x hx
      simp only [hx, Pi.zero_apply, zero_mul]
    rw [hwqz]
    change (0 : ℝ) ^ 2 ≤ m * _
    simp only [hm, zero_pow (by omega : 2 ≠ 0), zero_mul, le_refl]
  · have hmp : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
    have hnorm : ∫ x, m⁻¹ * w x ∂μ = 1 := by
      rw [integral_const_mul]
      exact inv_mul_cancel₀ hm
    have hq : Integrable (fun x => (m⁻¹ * w x) * q x) μ := by
      simpa only [mul_assoc] using hwq.const_mul m⁻¹
    have hq2 : Integrable (fun x => (m⁻¹ * w x) * q x ^ 2) μ := by
      simpa only [mul_assoc] using hwq2.const_mul m⁻¹
    have h := EuclideanMollificationNative.weighted_integral_sq_le
      (hw.const_mul m⁻¹) hq hq2
      (fun x => mul_nonneg (inv_nonneg.mpr hm0) (hw0 x)) hnorm
    simp only [mul_assoc, integral_const_mul] at h
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg m)
    have hleft (a : ℝ) : m ^ 2 * (m⁻¹ * a) ^ 2 = a ^ 2 := by
      field_simp [hm]
    have hright (b : ℝ) : m ^ 2 * (m⁻¹ * b) = m * b := by
      field_simp [hm]
    rw [hleft, hright] at hmul
    exact hmul

def convolutionEnvelope (a b : E → ℝ) (x : E) : ℝ :=
  ∫ y, a y * b (x - y)

theorem convolutionEnvelope_nonneg {a b : E → ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) (x : E) :
    0 ≤ convolutionEnvelope a b x :=
  integral_nonneg (fun y => mul_nonneg (ha0 y) (hb0 (x - y)))

theorem continuous_convolutionEnvelope {a b : E → ℝ}
    (ha : Integrable a volume) (hb : Continuous b)
    (hbdd : BddAbove (range (fun x => ‖b x‖))) :
    Continuous (convolutionEnvelope a b) :=
  BddAbove.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℝ ℝ) hbdd ha hb

theorem integrable_convolutionEnvelope_integrand {a b : E → ℝ}
    (ha : Integrable a volume) (hb : Continuous b)
    (hbdd : BddAbove (range (fun x => ‖b x‖))) (x : E) :
    Integrable (fun y => a y * b (x - y)) volume := by
  rcases hbdd with ⟨C, hC⟩
  apply ha.mul_bdd (hb.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun y => hC (mem_range_self (x - y)))

theorem bddAbove_sq {b : E → ℝ} (hbdd : BddAbove (range (fun x => ‖b x‖))) :
    BddAbove (range (fun x => ‖b x ^ 2‖)) := by
  rcases hbdd with ⟨C, hC⟩
  refine ⟨C ^ 2, ?_⟩
  rintro _ ⟨x, rfl⟩
  change ‖b x ^ 2‖ ≤ C ^ 2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC (mem_range_self x)) 2

theorem convolutionEnvelope_sq_le {a b : E → ℝ}
    (ha : Integrable a volume) (ha0 : ∀ x, 0 ≤ a x)
    (hb : Continuous b) (hbdd : BddAbove (range (fun x => ‖b x‖))) (x : E) :
    convolutionEnvelope a b x ^ 2 ≤
      (∫ y, a y) * ∫ y, a y * b (x - y) ^ 2 :=
  weighted_integral_sq_le_mass ha
    (integrable_convolutionEnvelope_integrand ha hb hbdd x)
    (integrable_convolutionEnvelope_integrand ha (hb.pow 2) (bddAbove_sq hbdd) x) ha0

theorem integrable_convolutionEnvelope_sq_integrand {a b : E → ℝ}
    (ha : Integrable a volume) (hb2 : Integrable (fun x => b x ^ 2) volume) :
    Integrable (fun p : E × E => a p.2 * b (p.1 - p.2) ^ 2)
      (volume.prod volume) :=
  ha.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hb2

theorem integrable_convolutionEnvelope_sq {a b : E → ℝ}
    (ha : Integrable a volume) (ha0 : ∀ x, 0 ≤ a x)
    (hb : Continuous b) (hbdd : BddAbove (range (fun x => ‖b x‖)))
    (hb2 : Integrable (fun x => b x ^ 2) volume) :
    Integrable (fun x => convolutionEnvelope a b x ^ 2) volume := by
  apply ((integrable_convolutionEnvelope_sq_integrand ha hb2).integral_prod_left.const_mul
    (∫ y, a y)).mono' ((continuous_convolutionEnvelope ha hb hbdd).pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact convolutionEnvelope_sq_le ha ha0 hb hbdd x

theorem integral_convolutionEnvelope_sq_le {a b : E → ℝ}
    (ha : Integrable a volume) (ha0 : ∀ x, 0 ≤ a x)
    (hb : Continuous b) (hbdd : BddAbove (range (fun x => ‖b x‖)))
    (hb2 : Integrable (fun x => b x ^ 2) volume) :
    (∫ x, convolutionEnvelope a b x ^ 2) ≤ (∫ y, a y) ^ 2 * ∫ x, b x ^ 2 := by
  have hp := integrable_convolutionEnvelope_sq_integrand ha hb2
  calc
    _ ≤ ∫ x, (∫ y, a y) * ∫ y, a y * b (x - y) ^ 2 :=
      integral_mono (integrable_convolutionEnvelope_sq ha ha0 hb hbdd hb2)
        (hp.integral_prod_left.const_mul _) (convolutionEnvelope_sq_le ha ha0 hb hbdd)
    _ = (∫ y, a y) * ∫ y, ∫ x, a y * b (x - y) ^ 2 := by
      rw [integral_const_mul, integral_integral_swap hp]
    _ = (∫ y, a y) ^ 2 * ∫ x, b x ^ 2 := by
      simp_rw [integral_const_mul, integral_sub_right_eq_self (fun x => b x ^ 2)]
      rw [integral_mul_const]
      ring

theorem memLp_convolutionEnvelope {a b : E → ℝ}
    (ha : Integrable a volume) (ha0 : ∀ x, 0 ≤ a x)
    (hb : Continuous b) (hbdd : BddAbove (range (fun x => ‖b x‖)))
    (hb2 : MemLp b 2 volume) : MemLp (convolutionEnvelope a b) 2 volume :=
  (memLp_two_iff_integrable_sq
    (continuous_convolutionEnvelope ha hb hbdd).aestronglyMeasurable).mpr
    (integrable_convolutionEnvelope_sq ha ha0 hb hbdd hb2.integrable_sq)

theorem norm_convolutionEnvelope_le {a b : E → ℝ}
    (ha : Integrable a volume) (ha0 : ∀ x, 0 ≤ a x)
    (hb : Continuous b) (hbdd : BddAbove (range (fun x => ‖b x‖)))
    (hb2 : MemLp b 2 volume) :
    ‖(memLp_convolutionEnvelope ha ha0 hb hbdd hb2).toLp (convolutionEnvelope a b)‖ ≤
      (∫ y, a y) * ‖hb2.toLp b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (integral_nonneg ha0) (norm_nonneg _))).mp
  rw [mul_pow, EuclideanTranslationNative.scalar_toLp_norm_sq,
    EuclideanTranslationNative.scalar_toLp_norm_sq]
  exact integral_convolutionEnvelope_sq_le ha ha0 hb hbdd hb2.integrable_sq

section NativeProducts

open TensorProbeNative

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type*} [Fintype iota]

def splitDirectionalWord : List iota → List (List iota × List iota)
  | [] => [([], [])]
  | i :: w =>
      (splitDirectionalWord w).map (fun p => (i :: p.1, p.2)) ++
        (splitDirectionalWord w).map (fun p => (p.1, i :: p.2))

theorem splitDirectionalWord_length (w : List iota) :
    (splitDirectionalWord w).length = 2 ^ w.length := by
  induction w with
  | nil => simp [splitDirectionalWord]
  | cons i w ih => simp [splitDirectionalWord, ih, pow_succ, Nat.mul_two]

theorem splitDirectionalWord_order (w : List iota) (p : List iota × List iota)
    (hp : p ∈ splitDirectionalWord w) : p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil =>
    simp only [splitDirectionalWord, List.mem_singleton] at hp
    subst p
    rfl
  | cons i w ih =>
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have h := ih q hq
      simp only [List.length_cons]
      omega
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have h := ih q hq
      simp only [List.length_cons]
      omega

private theorem contMDiff_list_sum {jota : Type*} (l : List jota) (f : jota → M → ℝ)
    (hf : ∀ j ∈ l, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => (l.map (fun j => f j x)).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using (contMDiff_const (c := (0 : ℝ)))
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf j (List.mem_cons_self)).add (ih (fun k hk => hf k (List.mem_cons_of_mem j hk)))

private theorem scalarDirectional_list_sum {jota : Type*} (l : List jota)
    (V : SmoothField (n := n) (M := M)) (f : jota → M → ℝ)
    (hf : ∀ j ∈ l, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j)) (x : M) :
    scalarDirectional V (fun y => (l.map (fun j => f j y)).sum) x =
      (l.map (fun j => scalarDirectional V (f j) x)).sum := by
  induction l with
  | nil =>
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x (V x) = 0
    rw [mfderiv_const, ContinuousLinearMap.zero_apply]
  | cons j l ih =>
    have hj := (hf j List.mem_cons_self).mdifferentiable (by simp) x
    have htail := contMDiff_list_sum l f (fun k hk => hf k (List.mem_cons_of_mem j hk))
    have hd := congrArg (fun A : TangentSpace (𝓡 n) x →L[ℝ] ℝ => A (V x))
      (mfderiv_add hj (htail.mdifferentiable (by simp) x))
    simp only [List.map_cons, List.sum_cons]
    change scalarDirectional V (fun y => f j y + (l.map (fun k => f k y)).sum) x = _
    change scalarDirectional V (fun y => f j y + (l.map (fun k => f k y)).sum) x =
      scalarDirectional V (f j) x + scalarDirectional V
        (fun y => (l.map (fun k => f k y)).sum) x at hd
    rw [hd, ih (fun k hk => hf k (List.mem_cons_of_mem j hk))]

theorem directionalWord_mul (F : iota → SmoothField (n := n) (M := M))
    (w : List iota) {f g : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) (x : M) :
    directionalWord F w (fun y => f y * g y) x =
      ((splitDirectionalWord w).map
        (fun p => directionalWord F p.1 f x * directionalWord F p.2 g x)).sum := by
  induction w generalizing x with
  | nil => simp [splitDirectionalWord]
  | cons i w ih =>
    have heq : directionalWord F w (fun y => f y * g y) =
        fun y => ((splitDirectionalWord w).map
          (fun p => directionalWord F p.1 f y * directionalWord F p.2 g y)).sum :=
      funext ih
    rw [directionalWord_cons, heq, scalarDirectional_list_sum]
    · simp only [splitDirectionalWord, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, directionalWord_cons, ← List.sum_map_add]
      congr 1
      apply List.map_congr_left
      intro p _
      rw [scalarDirectional_mul (F i)
        ((directionalWord_contMDiff F p.1 hf).mdifferentiable (by simp) x)
        ((directionalWord_contMDiff F p.2 hg).mdifferentiable (by simp) x)]
      ring
    · intro p _
      exact (directionalWord_contMDiff F p.1 hf).mul (directionalWord_contMDiff F p.2 hg)

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsFiniteMeasure μ]

private theorem memLp_of_continuous {f : M → ℝ} (hf : Continuous f) : MemLp f 2 μ :=
  ContinuousMap.memLp (p := 2) (μ := μ) ℝ (⟨f, hf⟩ : C(M, ℝ))

private theorem lpNorm_mul_le_of_sup {f g : M → ℝ}
    (hf : Continuous f) (hg : Continuous g) {a : ℝ} (ha : 0 ≤ a)
    (hb : ∀ x, ‖f x‖ ≤ a) :
    lpNorm (fun x => f x * g x) 2 μ ≤ a * lpNorm g 2 μ := by
  have hdom : MemLp (fun x => a * ‖g x‖) 2 μ := (memLp_of_continuous μ hg).norm.const_mul a
  calc
    _ ≤ lpNorm (fun x => a * ‖g x‖) 2 μ := by
      apply lpNorm_mono_real hdom
      intro x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
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
    exact (lpNorm_add_le (memLp_of_continuous μ (hf j List.mem_cons_self))
      (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (add_le_add_right (ih (fun k hk => hf k (List.mem_cons_of_mem j hk))) _)

theorem lpNorm_directionalWord_mul_le
    (F : iota → SmoothField (n := n) (M := M)) (k : ℕ) (w : List iota)
    (hw : w.length ≤ k) {f g : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g)
    {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfLow : ∀ v : List iota, v.length ≤ k / 2 → ∀ x, ‖directionalWord F v f x‖ ≤ a)
    (hgLow : ∀ v : List iota, v.length ≤ k / 2 → ∀ x, ‖directionalWord F v g x‖ ≤ b)
    (hfHigh : ∀ v : List iota, v.length ≤ k → lpNorm (directionalWord F v f) 2 μ ≤ A)
    (hgHigh : ∀ v : List iota, v.length ≤ k → lpNorm (directionalWord F v g) 2 μ ≤ B) :
    lpNorm (directionalWord F w (fun x => f x * g x)) 2 μ ≤
      (2 : ℝ) ^ w.length * (a * B + b * A) := by
  have heq : directionalWord F w (fun x => f x * g x) =
      fun x => ((splitDirectionalWord w).map
        (fun p => directionalWord F p.1 f x * directionalWord F p.2 g x)).sum :=
    funext (directionalWord_mul F w hf hg)
  rw [heq]
  apply (lpNorm_list_sum_le μ (splitDirectionalWord w)
    (fun p x => directionalWord F p.1 f x * directionalWord F p.2 g x)
    (fun p _ => (directionalWord_contMDiff F p.1 hf).continuous.mul
      (directionalWord_contMDiff F p.2 hg).continuous)).trans
  have hterm (p : List iota × List iota) (hp : p ∈ splitDirectionalWord w) :
      lpNorm (fun x => directionalWord F p.1 f x * directionalWord F p.2 g x) 2 μ ≤
        a * B + b * A := by
    have hlength := splitDirectionalWord_order w p hp
    by_cases hleft : p.1.length ≤ k / 2
    · apply ((lpNorm_mul_le_of_sup μ (directionalWord_contMDiff F p.1 hf).continuous
        (directionalWord_contMDiff F p.2 hg).continuous ha (hfLow p.1 hleft)).trans
        (mul_le_mul_of_nonneg_left (hgHigh p.2 (by omega)) ha)).trans
      exact le_add_of_nonneg_right (mul_nonneg hb hA)
    · have hright : p.2.length ≤ k / 2 := by omega
      have hcomm : (fun x => directionalWord F p.1 f x * directionalWord F p.2 g x) =
          (fun x => directionalWord F p.2 g x * directionalWord F p.1 f x) := by
        funext x
        ring
      rw [hcomm]
      apply ((lpNorm_mul_le_of_sup μ (directionalWord_contMDiff F p.2 hg).continuous
        (directionalWord_contMDiff F p.1 hf).continuous hb (hgLow p.2 hright)).trans
        (mul_le_mul_of_nonneg_left (hfHigh p.1 (by omega)) hb)).trans
      exact le_add_of_nonneg_left (mul_nonneg ha hB)
  calc
    _ ≤ ((splitDirectionalWord w).map (fun _ => a * B + b * A)).sum :=
      List.sum_le_sum hterm
    _ = (2 : ℝ) ^ w.length * (a * B + b * A) := by
      have hconst (l : List (List iota × List iota)) :
          (l.map (fun _ => a * B + b * A)).sum = (l.length : ℝ) * (a * B + b * A) := by
        induction l with
        | nil => simp
        | cons p l ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
          ring
      rw [hconst, splitDirectionalWord_length, Nat.cast_pow, Nat.cast_ofNat]

end NativeProducts

end PoincareConjecture.DeTurckTameCompositionNative
