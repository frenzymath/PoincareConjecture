import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.FrameCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Angle







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]


theorem unitField_eq_cos_sin_arccos
    (g : RiemannianMetric 2 S) (x : S) {e₁ e₂ T : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (he₂ : g.inner x e₂ e₂ = 1)
    (horth : g.inner x e₁ e₂ = 0) (hT : g.inner x T T = 1)
    (hpos : 0 < g.inner x T e₂) :
    Real.arccos (g.inner x T e₁) ∈ Ioo 0 Real.pi ∧
      T = Real.cos (Real.arccos (g.inner x T e₁)) • e₁ +
        Real.sin (Real.arccos (g.inner x T e₁)) • e₂ := by
  have hunit := (g.inner_self_eq_frameCoordinates_sq x he₁ he₂ horth T).symm.trans hT
  obtain ⟨hrange, hc, hs⟩ := Surface.arccos_unit_upper hunit hpos
  exact ⟨hrange, by rw [hc, hs]; exact g.eq_frameCoordinates_smul x he₁ he₂ horth T⟩


theorem contMDiffOn_arccos_frameCoordinate
    (g : RiemannianMetric 2 S) {U : Set S}
    {e₁ e₂ T : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) U)
    (hT : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% T) U)
    (hunit₁ : ∀ x ∈ U, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ U, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ U, g.inner x (e₁ x) (e₂ x) = 0)
    (hunitT : ∀ x ∈ U, g.inner x (T x) (T x) = 1)
    (hpos : ∀ x ∈ U, 0 < g.inner x (T x) (e₂ x)) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => Real.arccos (g.inner x (T x) (e₁ x))) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2) : S → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
  intro x hx
  have hunit := (g.inner_self_eq_frameCoordinates_sq x (hunit₁ x hx) (hunit₂ x hx)
    (horth x hx) (T x)).symm.trans (hunitT x hx)
  have hp := sq_pos_of_pos (hpos x hx)
  have hn₁ : g.inner x (T x) (e₁ x) ≠ -1 := by nlinarith
  have hn₂ : g.inner x (T x) (e₁ x) ≠ 1 := by nlinarith
  exact (Real.contDiffAt_arccos hn₁ hn₂).comp_contMDiffWithinAt
    (f := fun y => g.inner y (T y) (e₁ y))
    ((hT x hx).inner_bundle (he₁ x hx))


theorem arccos_inner_of_angle_sub
    (g : RiemannianMetric 2 S) (x : S) {e₁ e₂ v w : TangentSpace (𝓡 2) x}
    (he₁ : g.inner x e₁ e₁ = 1) (he₂ : g.inner x e₂ e₂ = 1)
    (horth : g.inner x e₁ e₂ = 0) {α β : ℝ}
    (hv : v = Real.cos α • e₁ + Real.sin α • e₂)
    (hw : w = Real.cos β • e₁ + Real.sin β • e₂)
    (hangle : β - α ∈ Icc 0 Real.pi) :
    Real.arccos (g.inner x v w) = β - α := by
  have horth' : g.inner x e₂ e₁ = 0 := by rw [g.symm]; exact horth
  have hinner : g.inner x v w = Real.cos (β - α) := by
    rw [hv, hw, Real.cos_sub]
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      he₁, he₂, horth, horth', mul_one, mul_zero, zero_add, add_zero]
  rw [hinner, Real.arccos_cos hangle.1 hangle.2]

end PoincareConjecture.RiemannianMetric
