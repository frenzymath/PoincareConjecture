import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.LieTestCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem integral_compact_first_order_test
    {a b c f : V → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (hcc : HasCompactSupport c)
    (u v : V) :
    (∫ x, c x * f x + a x * fderiv ℝ f x u + b x * fderiv ℝ f x v) =
      ∫ x, (c x - fderiv ℝ a x u - fderiv ℝ b x v) * f x := by
  have hcf : Integrable (fun x => c x * f x) :=
    (hc.continuous.mul hf.continuous).integrable_of_hasCompactSupport hcc.mul_right
  have had : Integrable (fun x => a x * fderiv ℝ f x u) :=
    (ha.continuous.mul ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport hca.mul_right
  have hbd : Integrable (fun x => b x * fderiv ℝ f x v) :=
    (hb.continuous.mul ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport hcb.mul_right
  have hdaf : Integrable (fun x => fderiv ℝ a x u * f x) :=
    (((ha.continuous_fderiv (by simp)).clm_apply continuous_const).mul hf.continuous
      ).integrable_of_hasCompactSupport (hca.fderiv_apply ℝ u).mul_right
  have hdbf : Integrable (fun x => fderiv ℝ b x v * f x) :=
    (((hb.continuous_fderiv (by simp)).clm_apply continuous_const).mul hf.continuous
      ).integrable_of_hasCompactSupport (hcb.fderiv_apply ℝ v).mul_right
  have hsum := integral_add (hcf.add had) hbd
  have hsum' := integral_add hcf had
  have hsub := integral_sub (hcf.sub hdaf) hdbf
  have hsub' := integral_sub hcf hdaf
  simp only [Pi.add_apply] at hsum hsum'
  simp only [Pi.sub_apply] at hsub hsub'
  simp only [sub_mul]
  rw [hsum, hsum', hsub, hsub', integral_compact_mul_fderiv ha hf hca u,
    integral_compact_mul_fderiv hb hf hcb v]
  ring

theorem integral_metricLieDerivative_eq_tests
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X : V → V} (hX : ContDiff ℝ ∞ X)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (u v : V) :
    (∫ x, φ x * DeTurckNative.metricLieDerivative D X x u v) =
      ∑ k, ∫ x, lieTestCoefficient D φ u v k x * X x k := by
  let A : Fin n → V → ℝ := fun k x => φ x * g.inner x (e k) v
  let B : Fin n → V → ℝ := fun k x => φ x * g.inner x u (e k)
  let C : Fin n → V → ℝ := fun k x => φ x *
    (g.inner x (rawConnectionCoefficient D x u (e k)) v +
      g.inner x u (rawConnectionCoefficient D x v (e k)))
  have hg := contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hA (k : Fin n) : ContDiff ℝ ∞ (A k) :=
    hφ.mul ((hg.clm_apply contDiff_const).clm_apply contDiff_const)
  have hB (k : Fin n) : ContDiff ℝ ∞ (B k) :=
    hφ.mul ((hg.clm_apply contDiff_const).clm_apply contDiff_const)
  have hΓ (w : V) (k : Fin n) :
      ContDiff ℝ ∞ (fun x => rawConnectionCoefficient D x w (e k)) :=
    ((rawConnectionCoefficient_contDiff D).clm_apply contDiff_const).clm_apply contDiff_const
  have hC (k : Fin n) : ContDiff ℝ ∞ (C k) :=
    hφ.mul (((hg.clm_apply (hΓ u k)).clm_apply contDiff_const).add
      ((hg.clm_apply contDiff_const).clm_apply (hΓ v k)))
  have hXk (k : Fin n) : ContDiff ℝ ∞ (fun x => X x k) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hX
  let L : Fin n → V → ℝ := fun k x => C k x * X x k +
    A k x * fderiv ℝ (fun y => X y k) x u + B k x * fderiv ℝ (fun y => X y k) x v
  have hL (k : Fin n) : Integrable (L k) := by
    have h₀ : Integrable (fun x => C k x * X x k) :=
      ((hC k).continuous.mul (hXk k).continuous
      ).integrable_of_hasCompactSupport hc.mul_right.mul_right
    have h₁ : Integrable (fun x => A k x * fderiv ℝ (fun y => X y k) x u) :=
      ((hA k).continuous.mul
      (((hXk k).continuous_fderiv (by simp)).clm_apply continuous_const)
        ).integrable_of_hasCompactSupport hc.mul_right.mul_right
    have h₂ : Integrable (fun x => B k x * fderiv ℝ (fun y => X y k) x v) :=
      ((hB k).continuous.mul
      (((hXk k).continuous_fderiv (by simp)).clm_apply continuous_const)
        ).integrable_of_hasCompactSupport hc.mul_right.mul_right
    exact (h₀.add h₁).add h₂
  have he (x : V) : φ x * DeTurckNative.metricLieDerivative D X x u v = ∑ k, L k x := by
    rw [metricLieDerivative_fixed_coordinates D (hX.differentiable (by simp) x),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [L, A, B, C]
    ring
  simp only [he]
  rw [integral_finsetSum _ (fun k _ => hL k)]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_compact_first_order_test (hA k) (hB k) (hC k) (hXk k)
    hc.mul_right hc.mul_right hc.mul_right u v

end PoincareConjecture.M35.Uniqueness.Heat
