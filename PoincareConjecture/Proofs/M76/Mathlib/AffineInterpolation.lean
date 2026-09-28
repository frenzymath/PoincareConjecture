import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.ContinuousAffineMap

set_option autoImplicit false

open Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem AffineIndependent.exists_continuousAffineMap_eqOn {s : Set E}
    (hs : AffineIndependent 𝕜 ((↑) : s → E)) (f : E → F) :
    ∃ a : E →ᴬ[𝕜] F, EqOn a f s := by
  classical
  obtain ⟨t, hst, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t 𝕜 E := ⟨Subtype.val, ht, by simpa using hspan⟩
  let : Finite t := b.finite
  let : Fintype t := Fintype.ofFinite t
  let a : E →ᵃ[𝕜] F :=
    (Fintype.linearCombination 𝕜 (fun i : t => f i)).toAffineMap.comp b.coords
  refine ⟨⟨a, a.continuous_of_finiteDimensional⟩, ?_⟩
  intro x hx
  have hbx : b ⟨x, hst hx⟩ = x := rfl
  change (Fintype.linearCombination 𝕜 (fun i : t => f i)) (b.coords x) = f x
  rw [← hbx, Fintype.linearCombination_apply]
  simp [AffineBasis.coords_apply, AffineBasis.coord_apply]
  rfl
