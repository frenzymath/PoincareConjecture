import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.OriginalMarkedPLApproximation
import PoincareLib.Topology.Manifold.Smoothing.RelativeApproximation.General.InteriorSourceModel

/-!
# Marked approximation from the unchanged original PL domain

The original chart cover supplies local compactness. A finite source
carrier then consumes the actual original-atlas pair construction,
without adding a geometric producer to the domain's hypotheses.
See Hatcher, Theorem 3.1, p. 45, and Dehn derivation 023, section 4.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

variable {U X ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [TopologicalSpace X] [T2Space X]

/-- The unchanged PL domain produces marked approximation on any
given finite source polyhedron. Local compactness and every target
model are constructed internally. See Dehn derivation 023, section 4. -/
theorem PLDomain.exists_marked_PL_approximation
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    (D : Set U) (hD : ∃ S : SimplicialComplex ℝ U, S.faces.Finite ∧ S.space = D)
    (v₀ : D) (f : C(D, R)) (B : Set D) (hB : IsCompact B)
    (F : Set X) (hF : F ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    (hBF : MapsTo (fun x : D => (f x : X)) B F) :
    ∃ (g : U → X) (a : C(D, R)), PolyhedralPLInCharts e g D ∧
      (∀ x : D, g x = (a x : X)) ∧
      ∃ H : f.Homotopy a,
        ∀ (t : unitInterval) (x : D), x ∈ B → (H (t, x) : X) ∈ F := by
  obtain ⟨S, hS, rfl⟩ := hD
  let : LocallyCompactSpace X := he.locallyCompactSpace
  exact OpenPartialHomeomorph.exists_original_marked_PL_approximation
    e he.compatible he.cover he.closed he.halfspace S hS v₀ f B hB F hF hFopen hBF

end PoincareMT.M76
