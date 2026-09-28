import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletCompactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem supportedTests_tsupport_subset {K : Set V} (hK : IsClosed K)
    (f : supportedTests K) : tsupport (f : V → ℝ) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (f.property x hn)

def testPartial {K : Set V} (hK : IsClosed K) (i : Fin n) :
    supportedTests K →ₗ[ℝ] supportedTests K :=
  (((LineDeriv.lineDerivOpCLM ℝ 𝓢(V, ℝ) (EuclideanSpace.single i (1 : ℝ))).toLinearMap.comp
    (supportedTests K).subtype)).codRestrict (supportedTests K) (fun f => by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hx ((SchwartzMap.tsupport_lineDerivOp_subset
        (EuclideanSpace.single i 1) (f : 𝓢(V, ℝ))).trans (supportedTests_tsupport_subset hK f) h))

def testLaplacian {K : Set V} (hK : IsClosed K) : supportedTests K →ₗ[ℝ] supportedTests K :=
  ∑ i : Fin n, (testPartial hK i).comp (testPartial hK i)

theorem testLaplacian_apply {K : Set V} (hK : IsClosed K)
    (f : supportedTests K) (x : V) :
    (testLaplacian hK f : 𝓢(V, ℝ)) x = ∑ i : Fin n,
      fderiv ℝ (fun y => fderiv ℝ (f : V → ℝ) y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  simp only [testLaplacian, LinearMap.sum_apply, Submodule.coe_sum,
    sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (∂_{EuclideanSpace.single i (1 : ℝ)}
    (∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ)))) x = _
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  congr 2

theorem testGradient_pairing_laplacian {K : Set V} (hK : IsClosed K)
    (φ f : supportedTests K) :
    inner ℝ (testGradient K φ) (testGradient K f) =
      -inner ℝ (intoDirichletValue K φ) (intoDirichletValue K (testLaplacian hK f)) := by
  rw [PiLp.inner_apply]
  change (∑ i : Fin n, inner ℝ
    ((∂_{EuclideanSpace.single i (1 : ℝ)} (φ : 𝓢(V, ℝ))).toLp 2 volume)
    ((∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ))).toLp 2 volume)) =
    -inner ℝ (testValue K φ) (testValue K (testLaplacian hK f))
  simp only [testLaplacian, LinearMap.sum_apply, map_sum, inner_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := EuclideanDerivativeNative.inner_schwartzLineDeriv
    (φ : 𝓢(V, ℝ)) (∂_{EuclideanSpace.single i (1 : ℝ)} (f : 𝓢(V, ℝ)))
    (EuclideanSpace.single i 1)
  simpa only [neg_neg] using! congrArg (fun r : ℝ => -r) h.symm

theorem dirichletForm_pairing_laplacian {K : Set V} (hK : IsClosed K)
    (f : supportedTests K) (z : dirichletForm K) :
    inner ℝ z (intoDirichletForm K f) =
      inner ℝ (dirichletInclusion K z)
        (intoDirichletValue K f - intoDirichletValue K (testLaplacian hK f)) := by
  have he : (fun w : dirichletForm K => inner ℝ w (intoDirichletForm K f)) =
      (fun w => inner ℝ (dirichletInclusion K w)
        (intoDirichletValue K f - intoDirichletValue K (testLaplacian hK f))) := by
    apply (intoDirichletForm_denseRange K).equalizer
      (continuous_id.inner continuous_const)
      ((dirichletInclusion K).continuous.inner continuous_const)
    funext φ
    simp only [Function.comp_apply, dirichletInclusion_into, inner_sub_right]
    change inner ℝ (dirichletImage K φ) (dirichletImage K f) = _
    rw [WithLp.prod_inner_apply]
    change inner ℝ (intoDirichletValue K φ) (intoDirichletValue K f) +
      inner ℝ (testGradient K φ) (testGradient K f) = _
    rw [testGradient_pairing_laplacian hK]
    ring
  exact congrFun he z

theorem dirichletGenerator_laplacian {K : Set V} (hK : IsClosed K)
    (f : supportedTests K) :
    HilbertResolventNative.InGeneratorGraph («V» := dirichletForm K) (dirichletInclusion K)
      (intoDirichletValue K f) (-intoDirichletValue K (testLaplacian hK f)) := by
  apply (HilbertResolventNative.inGeneratorGraph_iff_variational
    («V» := dirichletForm K) (H := dirichletValue K) _ _ _).mpr
  refine ⟨intoDirichletForm K f, rfl, ?_⟩
  intro z
  simpa only [sub_eq_add_neg] using dirichletForm_pairing_laplacian hK f z

end PoincareConjecture.M35.Uniqueness.Heat
