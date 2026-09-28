import PoincareConjecture.Proofs.M35.Thm12_28.ScalarEvolutionConvergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Locality









set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
  {g : RiemannianMetric 3 E} {h : RiemannianMetric 3 M}
  (D : LeviCivitaData g) (D' : LeviCivitaData h)
  {f : E → M} {p : E}

omit [T2Space M] in


theorem scalarGradientNorm_eq_pullback_of_scalar_germ
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f p)
    (hi : (mfderiv (𝓡 3) (𝓡 3) f p).IsInvertible)
    (hm : ∀ u v : E, g.inner p u v =
      h.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p u) (mfderiv (𝓡 3) (𝓡 3) f p v))
    (hR : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ D'.scalarCurvature (f p))
    (hscalar : D.scalarCurvature =ᶠ[𝓝 p] D'.scalarCurvature ∘ f) :
    scalarGradientNorm g D p = scalarGradientNorm h D' (f p) := by
  have hgrad : D.gradient D.scalarCurvature p = D.gradient (D'.scalarCurvature ∘ f) p :=
    congrArg (g.inner p).inverse (Poincare.mvfderiv_eq_of_eventuallyEq hscalar)
  have himage : mfderiv (𝓡 3) (𝓡 3) f p (D.gradient D.scalarCurvature p) =
      D'.gradient D'.scalarCurvature (f p) := by
    rw [hgrad, D.gradient_comp_eq_mpullback D' (hf.mdifferentiableAt (by simp))
      (hR.mdifferentiableAt (by simp)) hi hm]
    simp only [VectorField.mpullback, hi.self_apply_inverse]
  rw [scalarGradientNorm_eq_gradient_norm, scalarGradientNorm_eq_gradient_norm]
  change Real.sqrt (g.inner p _ _) = Real.sqrt (h.inner (f p) _ _)
  exact congrArg Real.sqrt ((hm (D.gradient D.scalarCurvature p)
    (D.gradient D.scalarCurvature p)).trans
      (congrArg₂ (fun u v => h.inner (f p) u v) himage himage))



theorem ricciNormSq_eq_pullback_euclidean
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f p)
    (hi : ∀ᶠ y in 𝓝 p, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hm : ∀ᶠ y in 𝓝 p, ∀ u v : E, g.inner y u v =
      h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y u) (mfderiv (𝓡 3) (𝓡 3) f y v)) :
    D.ricciNormSq p = D'.ricciNormSq (f p) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f p)) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 3) : M → Type _) (f p)
  obtain ⟨e, he⟩ := hi.self_of_nhds
  let e' : TangentSpace (𝓡 3) p ≃ₗᵢ[ℝ] TangentSpace (𝓡 3) (f p) :=
    e.toLinearEquiv.isometryOfInner (fun u v => by
      change h.inner (f p) (e u) (e v) = g.inner p u v
      exact (congrArg₂ (fun a b => h.inner (f p) a b)
        (congrArg (fun A => A u) he) (congrArg (fun A => A v) he)).trans
          (hm.self_of_nhds u v).symm)
  have he' (v : E) : e' v = mfderiv (𝓡 3) (𝓡 3) f p v :=
    congrArg (fun A => A v) he
  let b := g.orthonormalBasis p
  symm
  calc
    D'.ricciNormSq (f p) = ∑ i, ∑ j, (D'.ricci (f p) (e' (b i)) (e' (b j))) ^ 2 :=
      M13.sum_sq_bilinear_basis_eq (M13.ricciLinear D' (f p))
        (h.orthonormalBasis (f p)) (b.map e')
    _ = D.ricciNormSq p := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun a : ℝ => a ^ 2)
        ((congrArg₂ (D'.ricci (f p)) (he' (b i)) (he' (b j))).trans
          (D.ricci_eq_pullback_euclidean D' hf hi hm (b i) (b j)).symm)



theorem scalar_evolution_eq_pullback_of_scalar_germ
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f p)
    (hi : ∀ᶠ y in 𝓝 p, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hm : ∀ᶠ y in 𝓝 p, ∀ u v : E, g.inner y u v =
      h.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y u) (mfderiv (𝓡 3) (𝓡 3) f y v))
    (hR : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ D'.scalarCurvature (f p))
    (hscalar : D.scalarCurvature =ᶠ[𝓝 p] D'.scalarCurvature ∘ f) :
    D.laplacian D.scalarCurvature p + 2 * D.ricciNormSq p =
      D'.laplacian D'.scalarCurvature (f p) + 2 * D'.ricciNormSq (f p) :=
  congrArg₂ (fun a b : ℝ => a + 2 * b)
    ((D.laplacian_eq_of_eventuallyEq hscalar).trans
      (D.laplacian_comp_of_metric_pullback D' hf hi hm hR))
    (ricciNormSq_eq_pullback_euclidean D D' hf hi hm)

end PoincareConjecture.M35
