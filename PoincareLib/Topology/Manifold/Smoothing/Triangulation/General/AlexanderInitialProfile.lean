import PoincareLib.Topology.Manifold.Smoothing.Triangulation.General.AlexanderComplexityInitial
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderRecursiveInduction

/-!
# The initial complete profile of the actual generic surface

The existing complete geometric section families directly supply the
initial profile record. Its support remains inside the original vertex
heights; successor records require no genericity. See Alexander 1924,
pp. 6--8 and M76 derivations 246 and 269.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite pure surface complex with two triangular cofaces at each
edge and distinct original vertex heights has an actual complete profile.
The record retains its literal carrier, affine height and finite support
bound. See Alexander pp. 6--8 and M76 derivations 246 and 269. -/
theorem exists_initial_alexanderSectionProfile
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite)
    (hA : InjOn A K.vertices)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    ∃ P : AlexanderSectionProfile E,
      P.carrier = K.space ∧ P.height = A ∧
        Function.support P.charge ⊆ A '' K.vertices := by
  obtain ⟨m, n, Q, r, hQ, hr, _, hcover, hpair, _, hsupp, hfinite⟩ :=
    K.exists_finite_support_level_curve_families A hK hA hpure hcofaces
  let P : AlexanderSectionProfile E := {
    carrier := K.space
    height := A
    charge := fun c => alexanderCurveCount (fun i => (Q c i).boundary ℝ)
    presentation := fun c => ⟨m c, n c, Q c, r c, hQ c, hr c, hcover c, hpair c, rfl⟩
    finite_support := hfinite }
  exact ⟨P, rfl, rfl, hsupp⟩

end Geometry.SimplicialComplex
