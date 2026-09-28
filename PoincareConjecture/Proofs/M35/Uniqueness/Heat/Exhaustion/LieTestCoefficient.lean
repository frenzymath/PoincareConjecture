import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.CovariantTest









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

def lieTestCoefficient {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (φ : V → ℝ) (u v : V) (k : Fin n) (x : V) : ℝ :=
  φ x * (g.inner x (rawConnectionCoefficient D x u (e k)) v +
    g.inner x u (rawConnectionCoefficient D x v (e k))) -
    fderiv ℝ (fun y => φ y * g.inner y (e k) v) x u -
    fderiv ℝ (fun y => φ y * g.inner y u (e k)) x v

theorem lieTestCoefficient_contDiff {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (u v : V) (k : Fin n) :
    ContDiff ℝ ∞ (lieTestCoefficient D φ u v k) := by
  have hg := contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hΓ (w : V) : ContDiff ℝ ∞ (fun x => rawConnectionCoefficient D x w (e k)) :=
    ((rawConnectionCoefficient_contDiff D).clm_apply contDiff_const).clm_apply contDiff_const
  have h₀ : ContDiff ℝ ∞ (fun x => φ x *
      (g.inner x (rawConnectionCoefficient D x u (e k)) v +
        g.inner x u (rawConnectionCoefficient D x v (e k)))) :=
    hφ.mul (((hg.clm_apply (hΓ u)).clm_apply contDiff_const).add
      ((hg.clm_apply contDiff_const).clm_apply (hΓ v)))
  have hA : ContDiff ℝ ∞ (fun x => φ x * g.inner x (e k) v) :=
    hφ.mul ((hg.clm_apply contDiff_const).clm_apply contDiff_const)
  have hB : ContDiff ℝ ∞ (fun x => φ x * g.inner x u (e k)) :=
    hφ.mul ((hg.clm_apply contDiff_const).clm_apply contDiff_const)
  have h₁ := (hA.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := u))
  have h₂ := (hB.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := v))
  exact (h₀.sub h₁).sub h₂

theorem lieTestCoefficient_tsupport_subset {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (φ : V → ℝ) (u v : V) (k : Fin n) :
    tsupport (lieTestCoefficient D φ u v k) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra hn
  have h₁ : fderiv ℝ (fun y => φ y * g.inner y (e k) v) x = 0 := by
    apply fderiv_of_notMem_tsupport
    exact fun hh => hn (tsupport_mul_subset_left hh)
  have h₂ : fderiv ℝ (fun y => φ y * g.inner y u (e k)) x = 0 := by
    apply fderiv_of_notMem_tsupport
    exact fun hh => hn (tsupport_mul_subset_left hh)
  apply hx
  simp only [lieTestCoefficient, image_eq_zero_of_notMem_tsupport hn,
    zero_mul, h₁, h₂, zero_apply, sub_zero]

theorem lieTestCoefficient_hasCompactSupport {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {φ : V → ℝ} (hc : HasCompactSupport φ)
    (u v : V) (k : Fin n) : HasCompactSupport (lieTestCoefficient D φ u v k) :=
  hc.of_isClosed_subset (isClosed_tsupport _)
    (lieTestCoefficient_tsupport_subset D φ u v k)

theorem linear_form_sum_components (L : V →L[ℝ] ℝ) (z : V) :
    L z = ∑ k, z k * L (e k) := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr z)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr] using h.symm

theorem vector_component_fderiv {X : V → V} {x : V} (hX : DifferentiableAt ℝ X x)
    (u : V) (k : Fin n) :
    fderiv ℝ (fun y => X y k) x u = (fderiv ℝ X x u) k := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp x hX.hasFDerivAt
  change HasFDerivAt (fun y => X y k) _ x at h
  rw [h.fderiv]
  rfl

theorem metricLieDerivative_fixed_coordinates
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X : V → V} {x : V} (hX : DifferentiableAt ℝ X x) (u v : V) :
    DeTurckNative.metricLieDerivative D X x u v =
      ∑ k, (X x k * (g.inner x (rawConnectionCoefficient D x u (e k)) v +
          g.inner x u (rawConnectionCoefficient D x v (e k))) +
        fderiv ℝ (fun y => X y k) x u * g.inner x (e k) v +
        fderiv ℝ (fun y => X y k) x v * g.inner x u (e k)) := by
  let q : V →L[ℝ] V →L[ℝ] ℝ := g.euclideanCoefficients x
  have h₀ := linear_form_sum_components (q.flip v) (fderiv ℝ X x u)
  have h₁ := linear_form_sum_components
    ((q.flip v).comp (rawConnectionCoefficient D x u)) (X x)
  have h₂ := linear_form_sum_components (q u) (fderiv ℝ X x v)
  have h₃ := linear_form_sum_components
    ((q u).comp (rawConnectionCoefficient D x v)) (X x)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply] at h₀ h₁ h₂ h₃
  rw [DeTurckNative.metricLieDerivative_apply, raw_connection_expansion D hX,
    raw_connection_expansion D hX]
  simp only [map_add, add_apply]
  change q (fderiv ℝ X x u) v + q (rawConnectionCoefficient D x u (X x)) v +
    (q u (fderiv ℝ X x v) + q u (rawConnectionCoefficient D x v (X x))) =
    ∑ k, (X x k * (q (rawConnectionCoefficient D x u (e k)) v +
      q u (rawConnectionCoefficient D x v (e k))) +
      fderiv ℝ (fun y => X y k) x u * q (e k) v +
      fderiv ℝ (fun y => X y k) x v * q u (e k))
  rw [h₀, h₁, h₂, h₃]
  simp only [vector_component_fderiv hX, mul_add, Finset.sum_add_distrib]
  ring

theorem integral_compact_mul_fderiv {a b : V → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport a) (u : V) :
    (∫ x, a x * fderiv ℝ b x u) = -(∫ x, fderiv ℝ a x u * b x) := by
  have hleft : Integrable (fun x => a x * fderiv ℝ b x u) :=
    (ha.continuous.mul ((hb.continuous_fderiv (by simp)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport hc.mul_right
  have hright : Integrable (fun x => fderiv ℝ a x u * b x) :=
    (((ha.continuous_fderiv (by simp)).clm_apply continuous_const).mul hb.continuous
      ).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ u).mul_right
  have hprod : Integrable (fun x => a x * b x) :=
    (ha.continuous.mul hb.continuous).integrable_of_hasCompactSupport hc.mul_right
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hright hleft hprod
    (fun x _ => ha.differentiable (by simp) x) (fun x _ => hb.differentiable (by simp) x)

end PoincareConjecture.M35.Uniqueness.Heat
