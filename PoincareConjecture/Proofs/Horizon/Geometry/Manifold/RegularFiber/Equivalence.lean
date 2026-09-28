import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.UniversalProperty
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology
namespace Poincare.Geometry.Manifold.RegularFiber

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  {f h : M → Fin k → ℝ} {U V : Opens M} {c d : Fin k → ℝ}

def openFiberEquivOfEq
    (he : ∀ x, (x ∈ U ∧ f x = c) ↔ (x ∈ V ∧ h x = d)) :
    openFiber f U c ≃ openFiber h V d where
  toFun x := ⟨⟨x.1.1, (he x.1.1).mp ⟨x.1.2, x.2⟩ |>.1⟩,
    (he x.1.1).mp ⟨x.1.2, x.2⟩ |>.2⟩
  invFun x := ⟨⟨x.1.1, (he x.1.1).mpr ⟨x.1.2, x.2⟩ |>.1⟩,
    (he x.1.1).mpr ⟨x.1.2, x.2⟩ |>.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem openFiberIncl_openFiberEquivOfEq
    (he : ∀ x, (x ∈ U ∧ f x = c) ↔ (x ∈ V ∧ h x = d))
    (x : openFiber f U c) :
    openFiberIncl h V d (openFiberEquivOfEq he x) = openFiberIncl f U c x := rfl

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = m+k)]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,Fin k → ℝ) ∞ f)
  (hh : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,Fin k → ℝ) ∞ h)
  (hregf : ∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Fin k → ℝ) f x))
  (hregh : ∀ x ∈ V, Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,Fin k → ℝ) h x))

def openFiberDiffeomorphOfEq
    (he : ∀ x, (x ∈ U ∧ f x = c) ↔ (x ∈ V ∧ h x = d)) :
    letI := openFiberChartedSpace (m := m) hf U hregf c
    letI := openFiberChartedSpace (m := m) hh V hregh d
    openFiber f U c ≃ₘ⟮𝓡 m, 𝓡 m⟯ openFiber h V d := by
  letI := openFiberChartedSpace (m := m) hf U hregf c
  letI := openFiberChartedSpace (m := m) hh V hregh d
  refine { openFiberEquivOfEq he with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    apply (contMDiffAt_into_openFiber_iff (m := m) hh d V hregh
      (openFiberEquivOfEq he) x).mpr
    exact contMDiff_openFiberIncl (m := m) hf U hregf c x
  · intro x
    apply (contMDiffAt_into_openFiber_iff (m := m) hf c U hregf
      (openFiberEquivOfEq he).symm x).mpr
    exact contMDiff_openFiberIncl (m := m) hh V hregh d x

end Poincare.Geometry.Manifold.RegularFiber
