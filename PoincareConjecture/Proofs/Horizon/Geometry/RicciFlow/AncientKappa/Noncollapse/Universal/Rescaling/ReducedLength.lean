import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Data.Real.Pointwise
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral Pointwise Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {F G : RicciFlow n M (Iic 0)} {a : ℝ} (ha : 0 < a)
  (hmetric : ∀ t x (v w : TangentSpace (𝓡 n) x),
    (G.metric t).inner x v w = a⁻¹ * (F.metric (a * t)).inner x v w)
  (hscalar : ∀ t x, (G.connection t).scalarCurvature x =
    a * (F.connection (a * t)).scalarCurvature x)

omit [IsManifold (𝓡 n) ∞ M] in
private theorem curveVelocity_comp_mul {γ : ℝ → M} {s : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ (a * s)) :
    curveVelocity (n := n) (fun r => γ (a * r)) s =
      a • curveVelocity (n := n) γ (a * s) := by
  have hd : HasDerivAt (fun r : ℝ => a * r) a s := by
    simpa using (hasDerivAt_id s).const_mul a
  have hlin : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => a * r) s 1 = a := by
    exact (congrArg (fun L : ℝ →L[ℝ] ℝ => L 1)
      (mfderiv_eq_fderiv (f := fun r : ℝ => a * r) (x := s))).trans
      ((congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hd.hasFDerivAt.fderiv).trans
        (ContinuousLinearMap.toSpanSingleton_apply_one ℝ a))
  have hchain := mfderiv_comp_apply s (f := fun r : ℝ => a * r) (g := γ)
    hγ hd.differentiableAt.mdifferentiableAt (1 : TangentSpace 𝓘(ℝ, ℝ) s)
  have hinput : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => a * r) s 1 =
      a • (1 : TangentSpace 𝓘(ℝ, ℝ) s) := by rw [hlin]; simp
  rw [hinput, map_smul] at hchain
  change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ ∘ fun r : ℝ => a * r) s) 1 = _
  simpa only [curveVelocity, Function.comp_apply] using hchain

include ha hmetric hscalar in
private theorem backwardLIntegrand_parabolicRescale {γ : ℝ → M} {s : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ (a * s)) :
    backwardLIntegrand G 0 (fun r => γ (a * r)) s =
      Real.sqrt a * backwardLIntegrand F 0 γ (a * s) := by
  rw [backwardLIntegrand, curveVelocity_comp_mul hγ, hscalar, hmetric]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [backwardLIntegrand, Real.sqrt_mul ha.le]
  rw [show a * (0 - s) = 0 - a * s by ring]
  have hsqrt := Real.sq_sqrt ha.le
  field_simp
  rw [hsqrt]
  ring

namespace BackwardTimePath

include ha hmetric hscalar in
def parabolicRescale {b : ℝ} (hb : 0 < b) (p : BackwardTimePath F 0 0 (a * b)) :
    BackwardTimePath G 0 0 b where
  curve := fun s => p.curve (a * s)
  nonnegative := le_rfl
  ordered := hb
  terminal_mem := by simp
  time_mem := fun s hs => by change 0 - s ≤ 0; linarith [hs.1]
  continuous := p.continuous.comp (continuous_const.mul continuous_id).continuousOn
    (fun s hs => ⟨mul_nonneg ha.le hs.1, mul_le_mul_of_nonneg_left hs.2 ha.le⟩)
  regular := p.regular.comp
    (contMDiff_const.mul contMDiff_id).contMDiffOn
    (fun s hs => ⟨mul_pos ha hs.1, mul_lt_mul_of_pos_left hs.2 ha⟩)
  l_integrable := by
    have h := (p.l_integrable.comp_mul_left (c := a)).const_mul (Real.sqrt a)
    simp only [zero_div, mul_div_cancel_left₀ b ha.ne'] at h
    apply h.congr_uIoo
    intro s hs
    rw [uIoo_of_le hb.le] at hs
    have hs' : a * s ∈ Ioo (0 : ℝ) (a * b) :=
      ⟨mul_pos ha hs.1, mul_lt_mul_of_pos_left hs.2 ha⟩
    exact (backwardLIntegrand_parabolicRescale ha hmetric hscalar
      ((p.regular.contMDiffAt (isOpen_Ioo.mem_nhds hs')).mdifferentiableAt one_ne_zero)).symm

theorem parabolicRescale_length {b : ℝ} (hb : 0 < b)
    (p : BackwardTimePath F 0 0 (a * b)) :
    backwardLLength G 0 0 b (p.parabolicRescale ha hmetric hscalar hb).curve =
      backwardLLength F 0 0 (a * b) p.curve / Real.sqrt a := by
  change (∫ s in 0..b, backwardLIntegrand G 0 (fun r => p.curve (a * r)) s) = _
  have heq : (∫ s in 0..b, backwardLIntegrand G 0 (fun r => p.curve (a * r)) s) =
      ∫ s in 0..b, Real.sqrt a * backwardLIntegrand F 0 p.curve (a * s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hb.le
    intro s hs
    have hs' : a * s ∈ Ioo (0 : ℝ) (a * b) :=
      ⟨mul_pos ha hs.1, mul_lt_mul_of_pos_left hs.2 ha⟩
    exact backwardLIntegrand_parabolicRescale ha hmetric hscalar
      ((p.regular.contMDiffAt (isOpen_Ioo.mem_nhds hs')).mdifferentiableAt one_ne_zero)
  rw [heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ ha.ne', mul_zero]
  change Real.sqrt a * (a⁻¹ * backwardLLength F 0 0 (a * b) p.curve) = _
  have hsqrt := Real.sq_sqrt ha.le
  have hpos := Real.sqrt_pos.mpr ha
  field_simp
  rw [hsqrt]

end BackwardTimePath

include ha hmetric hscalar in
private theorem action_exists_parabolicRescale {b L : ℝ} (hb : 0 < b) {x y : M}
    (hL : ∃ p : BackwardTimePath F 0 0 (a * b), p.curve 0 = x ∧
      p.curve (a * b) = y ∧ L = backwardLLength F 0 0 (a * b) p.curve) :
    ∃ p : BackwardTimePath G 0 0 b, p.curve 0 = x ∧ p.curve b = y ∧
      L / Real.sqrt a = backwardLLength G 0 0 b p.curve := by
  obtain ⟨p, hp0, hpb, rfl⟩ := hL
  refine ⟨p.parabolicRescale ha hmetric hscalar hb, ?_, hpb, ?_⟩
  · simpa [BackwardTimePath.parabolicRescale] using hp0
  · exact (p.parabolicRescale_length ha hmetric hscalar hb).symm

include ha hmetric hscalar in
theorem reducedLength_parabolicRescale {b : ℝ} (hb : 0 < b) (x y : M) :
    reducedLength G 0 x y b = reducedLength F 0 x y (a * b) := by
  have himetric : ∀ t x (v w : TangentSpace (𝓡 n) x),
      (F.metric t).inner x v w = (a⁻¹)⁻¹ * (G.metric (a⁻¹ * t)).inner x v w := by
    intro t x v w
    rw [hmetric, inv_inv, mul_inv_cancel_left₀ ha.ne']
    field_simp
  have hiscalar : ∀ t x, (F.connection t).scalarCurvature x =
      a⁻¹ * (G.connection (a⁻¹ * t)).scalarCurvature x := by
    intro t x
    rw [hscalar, mul_inv_cancel_left₀ ha.ne', inv_mul_cancel_left₀ ha.ne']
  let S : Set ℝ := {L | ∃ p : BackwardTimePath F 0 0 (a * b),
    p.curve 0 = x ∧ p.curve (a * b) = y ∧ L = backwardLLength F 0 0 (a * b) p.curve}
  let T : Set ℝ := {L | ∃ p : BackwardTimePath G 0 0 b,
    p.curve 0 = x ∧ p.curve b = y ∧ L = backwardLLength G 0 0 b p.curve}
  have hset : T = (Real.sqrt a)⁻¹ • S := by
    ext L
    constructor
    · intro hL
      have hL' : ∃ p : BackwardTimePath G 0 0 (a⁻¹ * (a * b)), p.curve 0 = x ∧
          p.curve (a⁻¹ * (a * b)) = y ∧
          L = backwardLLength G 0 0 (a⁻¹ * (a * b)) p.curve := by
        rw [inv_mul_cancel_left₀ ha.ne']
        exact hL
      have hinv := action_exists_parabolicRescale (inv_pos.mpr ha) himetric hiscalar
        (mul_pos ha hb) hL'
      refine ⟨L / Real.sqrt a⁻¹, hinv, ?_⟩
      simp only [Real.sqrt_inv, div_inv_eq_mul, smul_eq_mul]
      field_simp
    · rintro ⟨L, hL, rfl⟩
      simpa only [T, Set.mem_ofPred_eq, smul_eq_mul, div_eq_mul_inv, mul_comm] using
        action_exists_parabolicRescale ha hmetric hscalar hb hL
  rw [reducedLength, dif_pos hb, reducedLength, dif_pos (mul_pos ha hb)]
  change sInf T / (2 * Real.sqrt b) = sInf S / (2 * Real.sqrt (a * b))
  rw [hset, Real.sInf_smul_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg a)),
    smul_eq_mul, Real.sqrt_mul ha.le]
  ring

end PoincareConjecture
