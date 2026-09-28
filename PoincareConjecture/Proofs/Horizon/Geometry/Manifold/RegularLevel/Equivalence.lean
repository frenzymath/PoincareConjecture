import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.RegularLevel

variable {M : Type*} [TopologicalSpace M]
  {f h : M → ℝ} {U V : Opens M} {c d : ℝ}

def openLevelEquivOfEq
    (he : ∀ x, (x ∈ U ∧ f x = c) ↔ (x ∈ V ∧ h x = d)) :
    openLevelSet f U c ≃ openLevelSet h V d where
  toFun x := ⟨⟨x.1.1, (he x.1.1).mp ⟨x.1.2, x.2⟩ |>.1⟩,
    (he x.1.1).mp ⟨x.1.2, x.2⟩ |>.2⟩
  invFun x := ⟨⟨x.1.1, (he x.1.1).mpr ⟨x.1.2, x.2⟩ |>.1⟩,
    (he x.1.1).mpr ⟨x.1.2, x.2⟩ |>.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem openLevelIncl_openLevelEquivOfEq
    (he : ∀ x, (x ∈ U ∧ f x = c) ↔ (x ∈ V ∧ h x = d))
    (x : openLevelSet f U c) :
    openLevelIncl h V d (openLevelEquivOfEq he x) = openLevelIncl f U c x := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]
  (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
  (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
  (hregf : ∀ x ∈ U, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
  (hregh : ∀ x ∈ V, mfderiv I 𝓘(ℝ, ℝ) h x ≠ 0)

def openLevelDiffeomorphOfEq
    (he : ∀ x, (x ∈ U ∧ f x = c) ↔ (x ∈ V ∧ h x = d)) :
    letI := openLevelSetChartedSpace hf U hregf n c
    letI := openLevelSetChartedSpace hh V hregh n d
    openLevelSet f U c ≃ₘ⟮𝓡 n, 𝓡 n⟯ openLevelSet h V d := by
  letI := openLevelSetChartedSpace hf U hregf n c
  letI := openLevelSetChartedSpace hh V hregh n d
  refine { openLevelEquivOfEq he with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    apply (contMDiffAt_into_openLevelSet_iff hh n d V hregh
      (openLevelEquivOfEq he) x).mpr
    exact contMDiff_openLevelIncl hf U hregf n c x
  · intro x
    apply (contMDiffAt_into_openLevelSet_iff hf n c U hregf
      (openLevelEquivOfEq he).symm x).mpr
    exact contMDiff_openLevelIncl hh V hregh n d x

end Poincare.Geometry.Manifold.RegularLevel
