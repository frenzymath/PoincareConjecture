import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.FrameChange
import Mathlib.Topology.Algebra.Field

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

noncomputable def frameOrientation (g : RiemannianMetric 2 S) (x : S)
    (e₁ e₂ f₁ f₂ : TangentSpace (𝓡 2) x) : ℝ :=
  g.inner x f₁ e₁ * g.inner x f₂ e₂ - g.inner x f₁ e₂ * g.inner x f₂ e₁

theorem frameOrientation_change (g : RiemannianMetric 2 S) (x : S)
    (e₁ e₂ : TangentSpace (𝓡 2) x) {f₁ f₂ : TangentSpace (𝓡 2) x}
    (hf₁ : g.inner x f₁ f₁ = 1) (hf₂ : g.inner x f₂ f₂ = 1)
    (hf : g.inner x f₁ f₂ = 0) (v w : TangentSpace (𝓡 2) x) :
    g.frameOrientation x e₁ e₂ v w =
      g.frameOrientation x f₁ f₂ v w * g.frameOrientation x e₁ e₂ f₁ f₂ := by
  conv_lhs =>
    rw [g.eq_frameCoordinates_smul x hf₁ hf₂ hf v,
      g.eq_frameCoordinates_smul x hf₁ hf₂ hf w]
  simp only [frameOrientation, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

theorem frameOrientation_smul (g : RiemannianMetric 2 S) (x : S)
    (e₁ e₂ v w : TangentSpace (𝓡 2) x) (a b : ℝ) :
    g.frameOrientation x e₁ e₂ (a • v) (b • w) =
      (a * b) * g.frameOrientation x e₁ e₂ v w := by
  simp only [frameOrientation, map_smul, smul_apply, smul_eq_mul]
  ring

theorem frameOrientation_sq (g : RiemannianMetric 2 S) (x : S)
    {e₁ e₂ f₁ f₂ : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (he₂ : g.inner x e₂ e₂ = 1)
    (he : g.inner x e₁ e₂ = 0)
    (hf₁ : g.inner x f₁ f₁ = 1) (hf₂ : g.inner x f₂ f₂ = 1)
    (hf : g.inner x f₁ f₂ = 0) :
    g.frameOrientation x e₁ e₂ f₁ f₂ ^ 2 = 1 := by
  have h := LeviCivitaData.gramDet_eq_frameDet_sq g x he₁ he₂ he f₁ f₂
  simpa [frameOrientation, hf₁, hf₂, hf] using h.symm

theorem continuousOn_frameOrientation (g : RiemannianMetric 2 S) {U : Set S}
    {e₁ e₂ f₁ f₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hf₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% f₁) U)
    (hf₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% f₂) U) :
    ContinuousOn (fun x => g.frameOrientation x (e₁ x) (e₂ x) (f₁ x) (f₂ x)) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : S → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  intro x hx
  exact ((((hf₁ x hx).inner_bundle (he₁ x hx)).mul
    ((hf₂ x hx).inner_bundle (he₂ x hx))).sub
    (((hf₁ x hx).inner_bundle (he₂ x hx)).mul
      ((hf₂ x hx).inner_bundle (he₁ x hx)))).continuousWithinAt

theorem exists_frameOrientation_sign_on_curve
    (g : RiemannianMetric 2 S) {U : Set S}
    {e₁ e₂ f₁ f₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) U)
    (hf₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% f₁) U)
    (hf₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% f₂) U)
    (heu₁ : ∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1)
    (heu₂ : ∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1)
    (heo : ∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0)
    (hfu₁ : ∀ x ∈ U, g.inner x (f₁ x) (f₁ x) = 1)
    (hfu₂ : ∀ x ∈ U, g.inner x (f₂ x) (f₂ x) = 1)
    (hfo : ∀ x ∈ U, g.inner x (f₁ x) (f₂ x) = 0)
    {A : Type*} [TopologicalSpace A] {K : Set A} (hK : IsPreconnected K)
    {γ : A → S} (hγ : ContinuousOn γ K) (hγU : MapsTo γ K U) :
    ∃ δ : ℝ, (δ = 1 ∨ δ = -1) ∧
      ∀ t ∈ K, g.frameOrientation (γ t)
        (e₁ (γ t)) (e₂ (γ t)) (f₁ (γ t)) (f₂ (γ t)) = δ := by
  have hc := (g.continuousOn_frameOrientation he₁ he₂ hf₁ hf₂).comp hγ hγU
  have hs : EqOn
      ((fun t => g.frameOrientation (γ t)
        (e₁ (γ t)) (e₂ (γ t)) (f₁ (γ t)) (f₂ (γ t))) ^ 2) 1 K := by
    intro t ht
    exact g.frameOrientation_sq (γ t) (heu₁ _ (hγU ht)) (heu₂ _ (hγU ht))
      (heo _ (hγU ht)) (hfu₁ _ (hγU ht)) (hfu₂ _ (hγU ht)) (hfo _ (hγU ht))
  rcases hK.eq_one_or_eq_neg_one_of_sq_eq hc hs with h | h
  · exact ⟨1, Or.inl rfl, h⟩
  · exact ⟨-1, Or.inr rfl, h⟩

end PoincareConjecture.RiemannianMetric
