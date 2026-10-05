import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.PolyhedralPLInCharts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.PLSurfaceCount

/-!
# Genus comparison for two models of the same original component

Compose the first original-atlas model map with the second graph coordinate
map. Its finite PL formulas, injectivity and exact image follow from the
retained charts and inverse equations. Euler-count invariance then identifies
the genus labels of the same physical component. See Wall019, lines 133--143.
-/

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- The literal transition between two original models of the same carrier
preserves its surface Euler count. The finite PL transition is constructed
from the original atlas formulas and the second graph coordinates. -/
theorem original_component_surfaceEulerCount_eq
    {E₁ E₂ X ι : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    (J₁ : SimplicialComplex ℝ E₁) (J₂ : SimplicialComplex ℝ E₂)
    (hJ₁ : J₁.faces.Finite) (hJ₂ : J₂.faces.Finite)
    (hdim₁ : ∀ t ∈ J₁.faces, t.card ≤ 3)
    (hdim₂ : ∀ t ∈ J₂.faces, t.card ≤ 3)
    {S : Set X} (g₁ : E₁ → X) (g₂ : E₂ → X) (phi₂ : X → E₂)
    (hg₁ : PolyhedralPLInCharts e g₁ J₁.space) (hgi₁ : InjOn g₁ J₁.space)
    (himage₁ : g₁ '' J₁.space = S) (himage₂ : g₂ '' J₂.space = S)
    (hphi₂ : ∀ i, LocallyPiecewiseAffineOn (phi₂ ∘ (e i).symm) (e i).target)
    (hphi₂i : InjOn phi₂ S)
    (hinverse₂ : ∀ z ∈ J₂.space, phi₂ (g₂ z) = z) :
    J₁.surfaceEulerCount = J₂.surfaceEulerCount := by
  have htransition : FinitePiecewiseAffineOn (phi₂ ∘ g₁) J₁.space :=
    hg₁.finitePiecewiseAffineOn_comp J₁ hJ₁ hphi₂
  have hinj : InjOn (phi₂ ∘ g₁) J₁.space := by
    intro x hx y hy hxy
    exact hgi₁ hx hy (hphi₂i
      (himage₁.subset (mem_image_of_mem g₁ hx))
      (himage₁.subset (mem_image_of_mem g₁ hy)) hxy)
  have himage : (phi₂ ∘ g₁) '' J₁.space = J₂.space := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxS : g₁ x ∈ S := himage₁.subset (mem_image_of_mem g₁ hx)
      obtain ⟨y, hy, hyx⟩ := himage₂.symm.subset hxS
      change phi₂ (g₁ x) ∈ J₂.space
      rw [← hyx, hinverse₂ y hy]
      exact hy
    · intro hz
      have hzS : g₂ z ∈ S := himage₂.subset (mem_image_of_mem g₂ hz)
      obtain ⟨x, hx, hxz⟩ := himage₁.symm.subset hzS
      exact ⟨x, hx, (congrArg phi₂ hxz).trans (hinverse₂ z hz)⟩
  exact htransition.surfaceEulerCount_eq_of_injOn hJ₁ hJ₂ hdim₁ hdim₂ hinj himage

/-- The computed genus is unchanged when the same actual component is
represented by a second original-atlas finite model. -/
theorem original_component_genus_eq
    {E₁ E₂ X ι : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    (J₁ : SimplicialComplex ℝ E₁) (J₂ : SimplicialComplex ℝ E₂)
    (hJ₁ : J₁.faces.Finite) (hJ₂ : J₂.faces.Finite)
    (hdim₁ : ∀ t ∈ J₁.faces, t.card ≤ 3)
    (hdim₂ : ∀ t ∈ J₂.faces, t.card ≤ 3)
    {S : Set X} (g₁ : E₁ → X) (g₂ : E₂ → X) (phi₂ : X → E₂)
    (hg₁ : PolyhedralPLInCharts e g₁ J₁.space) (hgi₁ : InjOn g₁ J₁.space)
    (himage₁ : g₁ '' J₁.space = S) (himage₂ : g₂ '' J₂.space = S)
    (hphi₂ : ∀ i, LocallyPiecewiseAffineOn (phi₂ ∘ (e i).symm) (e i).target)
    (hphi₂i : InjOn phi₂ S)
    (hinverse₂ : ∀ z ∈ J₂.space, phi₂ (g₂ z) = z)
    (genus₁ genus₂ : ℕ)
    (hcount₁ : Nat.card J₁.vertices +
      Nat.card (Triangle J₁.vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      2 * genus₁ =
      Nat.card (Edge J₁.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2)
    (hcount₂ : Nat.card J₂.vertices +
      Nat.card (Triangle J₂.vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      2 * genus₂ =
      Nat.card (Edge J₂.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    genus₁ = genus₂ := by
  have hEuler := original_component_surfaceEulerCount_eq J₁ J₂ hJ₁ hJ₂ hdim₁ hdim₂
    g₁ g₂ phi₂ hg₁ hgi₁ himage₁ himage₂ hphi₂ hphi₂i hinverse₂
  have h₁ := J₁.surfaceEulerCount_eq_two_sub_residual hcount₁
  have h₂ := J₂.surfaceEulerCount_eq_two_sub_residual hcount₂
  omega

end PoincareMT.M76
