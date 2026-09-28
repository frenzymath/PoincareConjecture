import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.BoundedFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}


theorem restrictComponent_ricci (F : RicciFlow n M J) (p : M) (t : ℝ)
    (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p)
    (v w : TangentSpace (𝓡 n) x) :
    ((F.restrictComponent p).connection t).ricci x v w =
      (F.connection t).ricci x
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x v)
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x w) := by
  apply ((F.restrictComponent p).connection t).ricci_eq_of_local_isometry
    (F.connection t) isOpen_univ contMDiff_subtype_val.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)


theorem restrictComponent_scalarCurvature_mvfderiv
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (p : M) (t : ℝ)
    (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y => ((F.restrictComponent p).connection t).scalarCurvature y)
        x v =
      mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y) x
        (mfderiv (𝓡 n) (𝓡 n) Subtype.val x v) := by
  have hscalar : (fun y => ((F.restrictComponent p).connection t).scalarCurvature y) =
      (F.connection t).scalarCurvature ∘ Subtype.val := by
    funext y
    exact F.restrictComponent_scalarCurvature p t y
  rw [hscalar]
  have hs := (hC.tensor_calculus n M (F.metric t) (F.connection t)).contMDiff_scalarCurvature
  exact mvfderiv_comp_apply x (hs.mdifferentiable (by simp) x)
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) x) v

end PoincareConjecture.RicciFlow

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem finite_differential_of_component_curvature_slab_bounds
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁))
    (hcomplete : ∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t))
    (hcurv : ∀ t ∈ Ioo T₀ T₁, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∀ p : M, ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo T₀ T₁ →
      ∃ K : ℝ, ∀ s ∈ Icc a b, ∀ x ∈ connectedComponent p,
        (F.connection s).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) dR
          (Ioo T₀ T₁) t ∧
        0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
          2 * mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y) x v +
          2 * (F.connection t).ricci x v v := by
  intro t ht x v
  let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) x
  let x' : U := ⟨x, mem_connectedComponent⟩
  let G := F.restrictComponent x
  obtain ⟨w, hw⟩ := ((G.metric t).mfderiv_bijective_of_pullback_eq
    (F.metric t) (f := Subtype.val) x' (fun _ _ => rfl)).surjective v
  have hcompleteG : ∀ s ∈ Ioo T₀ T₁, MetricComplete (G.metric s) :=
    fun s hs => F.restrictComponent_metricComplete x s (hcomplete s hs)
  have hcurvG : ∀ s ∈ Ioo T₀ T₁, ∀ y,
      (G.connection s).NonnegativeCurvatureOperator y :=
    fun s hs y => (F.restrictComponent_nonnegativeCurvatureOperator_iff x s y).mpr
      (hcurv s hs y)
  have hboundG : ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo T₀ T₁ →
      ∃ K : ℝ, ∀ s ∈ Icc a b, ∀ y, (G.connection s).curvatureTensorNorm y ≤ K := by
    intro a b hab hJ
    obtain ⟨K, hK⟩ := hbound x a b hab hJ
    refine ⟨K, fun s hs y => ?_⟩
    rw [F.restrictComponent_curvatureTensorNorm]
    exact hK s hs y y.property
  obtain ⟨dR, hdR, hineq⟩ := finite_differential_of_curvature_slab_bounds hC G
    hcompleteG hcurvG hboundG t ht x' w
  refine ⟨dR, ?_, ?_⟩
  · simpa only [G, F.restrictComponent_scalarCurvature] using hdR
  · dsimp only [G] at hineq
    rw [F.restrictComponent_scalarCurvature_mvfderiv hC] at hineq
    simpa only [F.restrictComponent_scalarCurvature, F.restrictComponent_ricci, hw]
      using hineq

end Poincare.RicciFlow.Harnack
