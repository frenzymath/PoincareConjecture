import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Persistence of a noncritical differential

Finite-dimensional bijectivity produces an actual continuous linear
equivalence. Openness of the range of such equivalences gives persistence
for a continuous family, with no determinant or varying basis.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace PoincareMT.ReducedVolume

variable {S X Y : Type*} [TopologicalSpace S]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A continuous family near a finite-dimensional bijective linear map remains bijective. -/
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

end PoincareMT.ReducedVolume
