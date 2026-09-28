import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace PoincareConjecture.M10

variable {S X Y : Type*} [TopologicalSpace S]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem eventually_bijective_of_continuousAt {D : S → X →L[ℝ] Y} {s₀ : S}
    (hD : ContinuousAt D s₀) (h₀ : Function.Bijective (D s₀)) :
    ∀ᶠ s in 𝓝 s₀, Function.Bijective (D s) := by
  have hi : (D s₀).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (D s₀).toLinearMap h₀).toContinuousLinearEquiv, rfl⟩
  have hopen : IsOpen {A : X →L[ℝ] Y | A.IsInvertible} :=
    ContinuousLinearEquiv.isOpen
  filter_upwards [hD (hopen.mem_nhds hi)] with s hs
  obtain ⟨e, he⟩ := hs
  rw [← he]
  exact e.bijective

end PoincareConjecture.M10
