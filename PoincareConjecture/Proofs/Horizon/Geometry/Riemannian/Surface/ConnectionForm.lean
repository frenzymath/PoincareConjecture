import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ManifoldCurvatureSmooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Frame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}

noncomputable def surfaceConnectionForm (D : LeviCivitaData g)
    (e₁ e₂ Z : (x : S) → TangentSpace (𝓡 2) x) (x : S) : ℝ :=
  g.inner x (D.covariantDerivativeOnFields Z e₁ x) (e₂ x)

lemma inner_covariantDerivative_unit_eq_zero (D : LeviCivitaData g)
    (X : (x : S) → TangentSpace (𝓡 2) x)
    {e : (x : S) → TangentSpace (𝓡 2) x} {x : S}
    (he : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e) x)
    (hunit : ∀ᶠ y in 𝓝 x, g.inner y (e y) (e y) = 1) :
    g.inner x (e x) (D.covariantDerivativeOnFields X e x) = 0 := by
  have h := D.horizon_mvfderiv_inner X (he.mdifferentiableAt (by simp))
    (he.mdifferentiableAt (by simp))
  rw [Poincare.mvfderiv_eq_of_eventuallyEq hunit, mvfderiv_const] at h
  simp only [zero_apply] at h
  rw [g.symm x (D.covariantDerivativeOnFields X e x) (e x)] at h
  linarith

private lemma inner_covariantDerivatives_frame_eq_zero (D : LeviCivitaData g)
    (X Y : (x : S) → TangentSpace (𝓡 2) x)
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x} {x : S}
    (he₁ : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) x)
    (he₂ : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) x)
    (hunit₁ : ∀ᶠ y in 𝓝 x, g.inner y (e₁ y) (e₁ y) = 1)
    (hunit₂ : ∀ᶠ y in 𝓝 x, g.inner y (e₂ y) (e₂ y) = 1)
    (horth : g.inner x (e₁ x) (e₂ x) = 0) :
    g.inner x (D.covariantDerivativeOnFields X e₁ x)
      (D.covariantDerivativeOnFields Y e₂ x) = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Fact (Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hne₁ : e₁ x ≠ 0 := by
    intro hzero
    have h := hunit₁.self_of_nhds
    simp [hzero] at h
  have hne₂ : e₂ x ≠ 0 := by
    intro hzero
    have h := hunit₂.self_of_nhds
    simp [hzero] at h
  have hspan : D.covariantDerivativeOnFields X e₁ x ∈ ℝ ∙ (e₂ x) :=
    Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hne₁ hne₂
      (D.inner_covariantDerivative_unit_eq_zero X he₁ hunit₁) horth
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
  rw [← ha]
  simp only [map_smul, smul_apply, smul_eq_mul,
    D.inner_covariantDerivative_unit_eq_zero Y he₂ hunit₂, mul_zero]

theorem curvatureTensor_eq_exteriorDerivative_surfaceConnectionForm
    (D : LeviCivitaData g) {U : Set S} (hU : IsOpen U) {x : S} (hx : x ∈ U)
    {e₁ e₂ X Y : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hunit₁ : ∀ y ∈ U, g.inner y (e₁ y) (e₁ y) = 1)
    (hunit₂ : ∀ y ∈ U, g.inner y (e₂ y) (e₂ y) = 1)
    (horth : ∀ y ∈ U, g.inner y (e₁ y) (e₂ y) = 0)
    (hX : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% Y) x) :
    D.curvatureTensor x (X x) (Y x) (e₂ x) (e₁ x) =
      mvfderiv (𝓡 2) (D.surfaceConnectionForm e₁ e₂ Y) x (X x) -
        mvfderiv (𝓡 2) (D.surfaceConnectionForm e₁ e₂ X) x (Y x) -
        D.surfaceConnectionForm e₁ e₂ (mlieBracket (𝓡 2) X Y) x := by
  have he₁x := he₁.contMDiffAt (hU.mem_nhds hx)
  have he₂x := he₂.contMDiffAt (hU.mem_nhds hx)
  have hu₁ : ∀ᶠ y in 𝓝 x, g.inner y (e₁ y) (e₁ y) = 1 := by
    filter_upwards [hU.mem_nhds hx] with y hy using hunit₁ y hy
  have hu₂ : ∀ᶠ y in 𝓝 x, g.inner y (e₂ y) (e₂ y) = 1 := by
    filter_upwards [hU.mem_nhds hx] with y hy using hunit₂ y hy
  have hXY := D.inner_covariantDerivatives_frame_eq_zero X Y he₁x he₂x hu₁ hu₂
    (horth x hx)
  have hYX := D.inner_covariantDerivatives_frame_eq_zero Y X he₁x he₂x hu₁ hu₂
    (horth x hx)
  have h₁ := D.horizon_mvfderiv_inner X
    ((D.contMDiffAt_covariantDerivativeOnFields hY he₁x).mdifferentiableAt (by simp))
    (he₂x.mdifferentiableAt (by simp))
  have h₂ := D.horizon_mvfderiv_inner Y
    ((D.contMDiffAt_covariantDerivativeOnFields hX he₁x).mdifferentiableAt (by simp))
    (he₂x.mdifferentiableAt (by simp))
  rw [hYX, add_zero] at h₁
  rw [hXY, add_zero] at h₂
  unfold surfaceConnectionForm
  rw [h₁, h₂, curvatureTensor,
    ← D.curvatureOnFields_eq_curvature_manifold hX hY he₁x]
  simp only [curvatureOnFields, covariantDerivativeOnFields, map_sub, sub_apply]
  rfl

theorem exists_local_scalarCurvature_connectionForm (D : LeviCivitaData g) (p : S) :
    ∃ (U : Set S) (e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x),
      IsOpen U ∧ p ∈ U ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U ∧
      (∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0) ∧
      ∀ x ∈ U, D.scalarCurvature x = -2 *
        (mvfderiv (𝓡 2) (D.surfaceConnectionForm e₁ e₂ e₂) x (e₁ x) -
          mvfderiv (𝓡 2) (D.surfaceConnectionForm e₁ e₂ e₁) x (e₂ x) -
          D.surfaceConnectionForm e₁ e₂ (mlieBracket (𝓡 2) e₁ e₂) x) := by
  obtain ⟨U, e₁, e₂, hU, hp, he₁, he₂, hunit₁, hunit₂, horth⟩ :=
    g.exists_local_orthonormal_frame p
  refine ⟨U, e₁, e₂, hU, hp, he₁, he₂, hunit₁, hunit₂, horth, ?_⟩
  intro x hx
  have h := D.curvatureTensor_eq_exteriorDerivative_surfaceConnectionForm hU hx
    he₁ he₂ hunit₁ hunit₂ horth
    (he₁.contMDiffAt (hU.mem_nhds hx)) (he₂.contMDiffAt (hU.mem_nhds hx))
  rw [D.curvatureTensor_eq_half_scalarCurvature] at h
  have horth' : g.inner x (e₂ x) (e₁ x) = 0 := by
    rw [g.symm]
    exact horth x hx
  simp only [horth x hx, horth', hunit₁ x hx, hunit₂ x hx,
    zero_mul, mul_one, zero_sub, mul_neg_one] at h
  linarith

end PoincareConjecture.LeviCivitaData
