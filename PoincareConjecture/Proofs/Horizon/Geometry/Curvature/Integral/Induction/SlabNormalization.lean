import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

private theorem isProperMap_restrictPreimage_const_mul
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} {a b c : ℝ}
    (hc : 0 < c) (hf : IsProperMap ((Ioo a b).restrictPreimage f)) :
    IsProperMap ((Ioo (c * a) (c * b)).restrictPreimage (fun x => c * f x)) := by
  let target : Ioo a b ≃ₜ Ioo (c * a) (c * b) :=
    (Homeomorph.mulLeft₀ c hc.ne').subtype (fun x => by
      change x ∈ Ioo a b ↔ c * x ∈ Ioo (c * a) (c * b)
      simp only [mem_Ioo, mul_lt_mul_iff_right₀ hc])
  let source : ((fun x => c * f x) ⁻¹' Ioo (c * a) (c * b)) ≃ₜ
      (f ⁻¹' Ioo a b) :=
    (Homeomorph.refl X).subtype (fun x => by
      change c * f x ∈ Ioo (c * a) (c * b) ↔ f x ∈ Ioo a b
      simp only [mem_Ioo, mul_lt_mul_iff_right₀ hc])
  exact (target.isProperMap.comp hf).comp source.isProperMap

namespace LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem gradient_const_mul (D : LeviCivitaData g)
    (c : ℝ) (f : M → ℝ) (x : M) :
    D.gradient (fun y => c * f y) x = c • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  rw [D.inner_gradient, mvfderiv_const_mul]
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]

private theorem tangentNorm_gradient_const_mul (D : LeviCivitaData g)
    {c : ℝ} (hc : 0 ≤ c) (f : M → ℝ) (x : M) :
    g.tangentNorm x (D.gradient (fun y => c * f y) x) =
      c * g.tangentNorm x (D.gradient f x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [gradient_const_mul]
  change ‖c • D.gradient f x‖ = c * ‖D.gradient f x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

theorem normalized_wide_regular_slab (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {r ε H : ℝ} (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r / 128) (hH : 0 < H)
    (p : M)
    (hproper : IsProperMap ((Ioo (9 * r / 8) (15 * r / 8)).restrictPreimage f))
    (hband : ∀ x : M, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
      r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r)
    (hbounds : ∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
      |f x - (g.edist p x).toReal| ≤ ε ∧
      (1 : ℝ) / 4 ≤ g.tangentNorm x (D.gradient f x) ∧
      g.tangentNorm x (D.gradient f x) ≤ 2 ∧
      ∀ v : TangentSpace (𝓡 n) x, D.hessian f x v v ≤ H * g.inner x v v) :
    let τ := 1 / (2 * max r 1)
    let F := fun x => τ * f x
    0 < τ ∧ τ ≤ 1 / 2 ∧ 0 < τ * r ∧ τ * r ≤ 1 / 2 ∧
      0 < τ * ε ∧ τ * ε < τ * r / 128 ∧ 0 < τ * H ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F ∧
      IsProperMap ((Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))).restrictPreimage F) ∧
      (∀ x : M, F x ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) →
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ) F x ≠ 0) ∧
      (∀ x : M, F x ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8)) →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      ∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |F x - τ * (g.edist p x).toReal| ≤ τ * ε ∧
        τ / 4 ≤ g.tangentNorm x (D.gradient F x) ∧
        g.tangentNorm x (D.gradient F x) ≤ 1 ∧
        ∀ v : TangentSpace (𝓡 n) x, D.hessian F x v v ≤ τ * H * g.inner x v v := by
  let τ := 1 / (2 * max r 1)
  let F := fun x => τ * f x
  have hmax : 0 < max r 1 := zero_lt_one.trans_le (le_max_right r 1)
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτhalf : τ ≤ 1 / 2 := by
    dsimp only [τ]
    apply (div_le_iff₀ (mul_pos (by norm_num) hmax)).2
    linarith [le_max_right r 1]
  have hτrhalf : τ * r ≤ 1 / 2 := by
    have hmul : τ * r ≤ τ * max r 1 :=
      mul_le_mul_of_nonneg_left (le_max_left r 1) hτ.le
    have heq : τ * max r 1 = 1 / 2 := by
      dsimp only [τ]
      field_simp
    exact hmul.trans_eq heq
  have hεsmall : τ * ε < τ * r / 128 := by
    simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left hεr hτ
  have hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F := contMDiff_const.mul hf
  have hbandF (x : M)
      (hx : F x ∈ Ioo (τ * (9 * r / 8)) (τ * (15 * r / 8))) :
      r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r := by
    apply hband x
    simpa only [F, mem_Ioo, mul_lt_mul_iff_right₀ hτ] using hx
  have hboundsF (x : M) (hx : r < (g.edist p x).toReal)
      (hx' : (g.edist p x).toReal < 2 * r) :
      |F x - τ * (g.edist p x).toReal| ≤ τ * ε ∧
      τ / 4 ≤ g.tangentNorm x (D.gradient F x) ∧
      g.tangentNorm x (D.gradient F x) ≤ 1 ∧
      ∀ v : TangentSpace (𝓡 n) x, D.hessian F x v v ≤ τ * H * g.inner x v v := by
    obtain ⟨hvalue, hlower, hupper, hhessian⟩ := hbounds x hx hx'
    have hnorm : g.tangentNorm x (D.gradient F x) =
        τ * g.tangentNorm x (D.gradient f x) :=
      tangentNorm_gradient_const_mul D hτ.le f x
    refine ⟨?_, ?_, ?_, ?_⟩
    · change |τ * f x - τ * (g.edist p x).toReal| ≤ τ * ε
      rw [← mul_sub, abs_mul, abs_of_pos hτ]
      exact mul_le_mul_of_nonneg_left hvalue hτ.le
    · rw [hnorm]
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlower hτ.le
    · rw [hnorm]
      exact (mul_le_mul_of_nonneg_left hupper hτ.le).trans (by linarith only [hτhalf])
    · intro v
      change D.hessian (fun y => τ * f y) x v v ≤ τ * H * g.inner x v v
      rw [D.hessian_const_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hhessian v) hτ.le
  refine ⟨hτ, hτhalf, mul_pos hτ hr, hτrhalf, mul_pos hτ hε, hεsmall,
    mul_pos hτ hH, hF, isProperMap_restrictPreimage_const_mul hτ hproper, ?_, hbandF,
    hboundsF⟩
  intro x hx
  apply (g.tangentNorm_gradient_pos_iff F x).mp
  have hlower := (hboundsF x (hbandF x hx).1 (hbandF x hx).2).2.1
  exact (div_pos hτ (by norm_num)).trans_le hlower

end LeviCivitaData

end PoincareConjecture
