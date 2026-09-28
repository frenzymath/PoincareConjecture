import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.LevelSet

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow.Splitting

open RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {r : M → ℝ} (hr : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ r)
  (hreg : ∀ x, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) r x ≠ 0)
  (τ : M ≃ₘ⟮𝓡 (n + 1), 𝓡 (n + 1)⟯ M)
  (hτ : Function.Involutive τ) (hreverse : ∀ x, r (τ x) = -r x)

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def zeroLevelInvolution :
    letI := openLevelSetChartedSpace hr (⊤ : Opens M) (fun x _ => hreg x) n 0
    zeroLevelSet r ≃ₘ⟮𝓡 n, 𝓡 n⟯ zeroLevelSet r := by
  letI := openLevelSetChartedSpace hr (⊤ : Opens M) (fun x _ => hreg x) n 0
  let s : zeroLevelSet r → zeroLevelSet r := fun x =>
    ⟨⟨τ (zeroLevelIncl r x), mem_univ _⟩, by
      change r (τ (zeroLevelIncl r x)) = 0
      have hx : r (zeroLevelIncl r x) = 0 := x.2
      rw [hreverse, hx, neg_zero]⟩
  have hss : Function.Involutive s := by
    intro x
    apply Subtype.ext
    exact Subtype.ext (hτ (zeroLevelIncl r x))
  have hs : ContMDiff (𝓡 n) (𝓡 n) ∞ s := by
    intro x
    apply (contMDiffAt_into_openLevelSet_iff hr n 0 (⊤ : Opens M)
      (fun x _ => hreg x) s x).mpr
    exact τ.contMDiffAt.comp x (contMDiff_openLevelIncl hr (⊤ : Opens M)
      (fun x _ => hreg x) n 0 x)
  exact {
    toFun := s
    invFun := s
    left_inv := hss
    right_inv := hss
    contMDiff_toFun := hs
    contMDiff_invFun := hs }

@[simp] theorem zeroLevelInvolution_incl :
    letI := openLevelSetChartedSpace hr (⊤ : Opens M) (fun x _ => hreg x) n 0
    ∀ x, zeroLevelIncl r (zeroLevelInvolution hr hreg τ hτ hreverse x) =
      τ (zeroLevelIncl r x) := by
  intros
  rfl

theorem zeroLevelInvolution_involutive :
    letI := openLevelSetChartedSpace hr (⊤ : Opens M) (fun x _ => hreg x) n 0
    Function.Involutive (zeroLevelInvolution hr hreg τ hτ hreverse) := by
  letI := openLevelSetChartedSpace hr (⊤ : Opens M) (fun x _ => hreg x) n 0
  intro x
  apply Subtype.ext
  exact Subtype.ext (hτ (zeroLevelIncl r x))

theorem zeroLevelInvolution_free (hfree : ∀ x, τ x ≠ x) :
    letI := openLevelSetChartedSpace hr (⊤ : Opens M) (fun x _ => hreg x) n 0
    ∀ x, zeroLevelInvolution hr hreg τ hτ hreverse x ≠ x := by
  letI := openLevelSetChartedSpace hr (⊤ : Opens M) (fun x _ => hreg x) n 0
  intro x hx
  exact hfree (zeroLevelIncl r x) (congrArg (zeroLevelIncl r) hx)

theorem zeroLevelInvolution_preserves_metric (g : RiemannianMetric (n + 1) M)
    (hmetric : ∀ (x : M) (u v : TangentSpace (𝓡 (n + 1)) x),
      g.inner (τ x) (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) τ x u)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) τ x v) = g.inner x u v) :
    letI := openLevelSetChartedSpace hr (⊤ : Opens M) (fun x _ => hreg x) n 0
    letI := isManifold_openLevelSet hr (⊤ : Opens M) (fun x _ => hreg x) n 0
    let s := zeroLevelInvolution hr hreg τ hτ hreverse
    let h := regularLevelMetric hr (⊤ : Opens M) (fun x _ => hreg x) 0 g
    ∀ (x : zeroLevelSet r) (u v : TangentSpace (𝓡 n) x),
      h.inner (s x) (mfderiv (𝓡 n) (𝓡 n) s x u)
        (mfderiv (𝓡 n) (𝓡 n) s x v) = h.inner x u v := by
  letI := openLevelSetChartedSpace hr (⊤ : Opens M) (fun x _ => hreg x) n 0
  letI := isManifold_openLevelSet hr (⊤ : Opens M) (fun x _ => hreg x) n 0
  let s := zeroLevelInvolution hr hreg τ hτ hreverse
  let incl := zeroLevelIncl r
  have hi : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ incl :=
    contMDiff_openLevelIncl hr (⊤ : Opens M) (fun x _ => hreg x) n 0
  dsimp only
  intro x u v
  have hd : (mfderiv (𝓡 n) (𝓡 (n + 1)) incl (s x)).comp
        (mfderiv (𝓡 n) (𝓡 n) s x) =
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) τ (incl x)).comp
        (mfderiv (𝓡 n) (𝓡 (n + 1)) incl x) := by
    rw [← mfderiv_comp x (hi.mdifferentiable (by simp) _)
        (s.contMDiff.mdifferentiable (by simp) x),
      ← mfderiv_comp x (τ.contMDiff.mdifferentiable (by simp) _)
        (hi.mdifferentiable (by simp) x)]
    rfl
  change g.inner (τ (incl x))
    (mfderiv (𝓡 n) (𝓡 (n + 1)) incl (s x) (mfderiv (𝓡 n) (𝓡 n) s x u))
    (mfderiv (𝓡 n) (𝓡 (n + 1)) incl (s x) (mfderiv (𝓡 n) (𝓡 n) s x v)) = _
  rw [← ContinuousLinearMap.comp_apply, hd, ← ContinuousLinearMap.comp_apply, hd]
  exact hmetric (incl x) (mfderiv (𝓡 n) (𝓡 (n + 1)) incl x u)
    (mfderiv (𝓡 n) (𝓡 (n + 1)) incl x v)

end PoincareConjecture.RicciFlow.Splitting
