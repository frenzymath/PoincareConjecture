import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.ConnectionForm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Density










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology Matrix

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}



theorem scalarCurvature_mul_frameDet_eq_neg_two_curvatureTensor
    (D : LeviCivitaData g) (x : S)
    {e₁ e₂ : TangentSpace (𝓡 2) x}
    (u v : TangentSpace (𝓡 2) x) :
    D.scalarCurvature x *
        (g.inner x u e₁ * g.inner x v e₂ -
          g.inner x u e₂ * g.inner x v e₁) =
      -2 * D.curvatureTensor x u v e₂ e₁ := by
  have h := D.curvatureTensor_eq_half_scalarCurvature x u v e₂ e₁
  nlinarith [h]



theorem gramDet_eq_frameDet_sq
    (g : RiemannianMetric 2 S) (x : S)
    {e₁ e₂ : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (he₂ : g.inner x e₂ e₂ = 1)
    (horth : g.inner x e₁ e₂ = 0)
    (u v : TangentSpace (𝓡 2) x) :
    g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 =
      (g.inner x u e₁ * g.inner x v e₂ -
        g.inner x u e₂ * g.inner x v e₁) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  let : Fact (Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2) :=
    ⟨hdim⟩
  have hne₁ : e₁ ≠ 0 := by
    intro hzero
    simp [hzero] at he₁
  have hne₂ : e₂ ≠ 0 := by
    intro hzero
    simp [hzero] at he₂
  have horth' : g.inner x e₂ e₁ = 0 := by rw [g.symm]; exact horth
  have hdecomp (z : TangentSpace (𝓡 2) x) :
      z = g.inner x e₁ z • e₁ + g.inner x e₂ z • e₂ := by
    let r := z - g.inner x e₁ z • e₁
    have hr : g.inner x e₁ r = 0 := by
      simp only [r, map_sub, map_smul, smul_eq_mul, he₁, mul_one, sub_self]
    have hs : r ∈ ℝ ∙ e₂ :=
      Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hne₁ hne₂ hr horth
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
    have hcc := congrArg (fun w => g.inner x e₂ w) hc
    have hcz : c = g.inner x e₂ z := by
      simp only [r, map_sub, map_smul, smul_eq_mul, horth', he₂, mul_one] at hcc
      linarith
    have hc' := hc.symm
    rw [sub_eq_iff_eq_add] at hc'
    exact hc'.trans ((add_comm _ _).trans (by rw [hcz]))
  have hinner (a b : TangentSpace (𝓡 2) x) :
      g.inner x a b = g.inner x e₁ a * g.inner x e₁ b +
        g.inner x e₂ a * g.inner x e₂ b := by
    change inner ℝ a b = inner ℝ e₁ a * inner ℝ e₁ b +
      inner ℝ e₂ a * inner ℝ e₂ b
    have ha := congrArg (fun z => g.inner x z b) (hdecomp a)
    change inner ℝ a b = inner ℝ
      (g.inner x e₁ a • e₁ + g.inner x e₂ a • e₂) b at ha
    simp only [inner_add_left, real_inner_smul_left] at ha
    convert ha using 1
    rfl
  rw [hinner u u, hinner v v, hinner u v]
  have hu₁ : g.inner x u e₁ = g.inner x e₁ u := by rw [g.symm]
  have hu₂ : g.inner x u e₂ = g.inner x e₂ u := by rw [g.symm]
  have hv₁ : g.inner x v e₁ = g.inner x e₁ v := by rw [g.symm]
  have hv₂ : g.inner x v e₂ = g.inner x e₂ v := by rw [g.symm]
  rw [hu₁, hu₂, hv₁, hv₂]
  ring_nf



theorem pullbackVolumeDensity_eq_abs_frameDet
    (g : RiemannianMetric 2 S)
    {f : EuclideanSpace ℝ (Fin 2) → S} {x : EuclideanSpace ℝ (Fin 2)}
    (e₁ e₂ : TangentSpace (𝓡 2) (f x))
    (he₁ : g.inner (f x) e₁ e₁ = 1) (he₂ : g.inner (f x) e₂ e₂ = 1)
    (horth : g.inner (f x) e₁ e₂ = 0) :
    g.pullbackVolumeDensity f x =
      |g.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) e₁ *
        g.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)) e₂ -
        g.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) e₂ *
        g.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)) e₁| := by
  let u := mfderiv (𝓡 2) (𝓡 2) f x (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let v := mfderiv (𝓡 2) (𝓡 2) f x (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have hgram := gramDet_eq_frameDet_sq g (f x) he₁ he₂ horth u v
  unfold RiemannianMetric.pullbackVolumeDensity
  change Real.sqrt (Matrix.det (Matrix.of (fun i j : Fin 2 =>
    g.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x
      (EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderiv (𝓡 2) (𝓡 2) f x
        (EuclideanSpace.basisFun (Fin 2) ℝ j))))) = _
  rw [show Matrix.det (Matrix.of (fun i j : Fin 2 =>
      g.inner (f x) (mfderiv (𝓡 2) (𝓡 2) f x
        (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 2) f x
          (EuclideanSpace.basisFun (Fin 2) ℝ j)))) =
      g.inner (f x) u u * g.inner (f x) v v -
        (g.inner (f x) u v) ^ 2 by
    simp [Matrix.det_fin_two, u, v, g.symm]
    ring]
  rw [hgram, Real.sqrt_sq_eq_abs]



theorem scalarCurvature_mul_frameDet_eq_connectionForm
    (D : LeviCivitaData g) {U : Set S} (hU : IsOpen U) {x : S} (hx : x ∈ U)
    {e₁ e₂ X Y : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hunit₁ : ∀ y ∈ U, g.inner y (e₁ y) (e₁ y) = 1)
    (hunit₂ : ∀ y ∈ U, g.inner y (e₂ y) (e₂ y) = 1)
    (horth : ∀ y ∈ U, g.inner y (e₁ y) (e₂ y) = 0)
    (hX : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% Y) x) :
    D.scalarCurvature x *
        (g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x)) =
      -2 * (mvfderiv (𝓡 2) (D.surfaceConnectionForm e₁ e₂ Y) x (X x) -
        mvfderiv (𝓡 2) (D.surfaceConnectionForm e₁ e₂ X) x (Y x) -
        D.surfaceConnectionForm e₁ e₂ (mlieBracket (𝓡 2) X Y) x) := by
  have hcurv := D.curvatureTensor_eq_exteriorDerivative_surfaceConnectionForm hU hx
    he₁ he₂ hunit₁ hunit₂ horth hX hY
  have hscalar := D.scalarCurvature_mul_frameDet_eq_neg_two_curvatureTensor x
    (e₁ := e₁ x) (e₂ := e₂ x) (X x) (Y x)
  rw [hcurv] at hscalar
  exact hscalar

end PoincareConjecture.LeviCivitaData
