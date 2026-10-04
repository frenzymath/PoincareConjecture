import PoincareLib.Topology.Manifold.Smoothing.Triangulation.General.AlexanderRecursiveInitial
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.FinitePositiveHeightGap

/-!
# Both initial half-slabs at the actual marked vertex

Center the original separating height at the nonisolated
vertex and apply the single-vertex construction in both
orientations. Both widths may be arbitrarily small.
See Alexander 1924, pp. 6--8 and M76 derivation 273.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A nonisolated original vertex with separating heights
has actual positive and negative radial half-slabs at the
same marked point, with arbitrarily small widths. The height
is centered at its literal original value. See Alexander
pp. 6--8 and M76 derivation 273. -/
theorem exists_small_generic_vertex_halfSlabs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices)
    {q : E} (hq : q ∈ K.vertices)
    (hacc : q ∈ closure ((K.space ∩ {x | A x = A q}) \ {q}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, β ∈ Ioo 0 ε ∧ ∃ γ : ℝ, γ ∈ Ioo 0 ε ∧
      Nonempty (AlexanderHalfSlab K.space (A - AffineMap.const ℝ E (A q)) q β) ∧
      Nonempty (AlexanderHalfSlab K.space (-(A - AffineMap.const ℝ E (A q))) q γ) := by
  let B : E →ᵃ[ℝ] ℝ := A - AffineMap.const ℝ E (A q)
  have hB (x : E) : B x = A x - A q := rfl
  have hBq : B q = 0 := sub_self _
  have hzero : ∀ v ∈ K.vertices, B v = 0 → v = q := by
    intro v hv hvB
    exact hA hv hq (sub_eq_zero.mp hvB)
  have hzeroNeg : ∀ v ∈ K.vertices, (-B) v = 0 → v = q := by
    intro v hv hvB
    exact hzero v hv (neg_eq_zero.mp hvB)
  have haccB : q ∈ closure ((K.space ∩ {x | B x = 0}) \ {q}) := by
    simpa only [hB, sub_eq_zero] using hacc
  have haccNeg : q ∈ closure ((K.space ∩ {x | (-B) x = 0}) \ {q}) := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using haccB
  obtain ⟨β, hβ, hreg⟩ := K.exists_singleVertex_slab_width hK B hzero hε
  obtain ⟨γ, hγ, hregNeg⟩ := K.exists_singleVertex_slab_width hK (-B) hzeroNeg hε
  exact ⟨β, hβ, γ, hγ,
    K.nonempty_alexanderHalfSlab_of_singleVertex hK hpure B hq hBq haccB hβ.1 hreg,
    K.nonempty_alexanderHalfSlab_of_singleVertex hK hpure (-B) hq
      (by change -B q = 0; rw [hBq, neg_zero]) haccNeg hγ.1 hregNeg⟩

end Geometry.SimplicialComplex
