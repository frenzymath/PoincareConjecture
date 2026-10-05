import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionPLTransport

/-!
# Finite composition of ambient finite PL maps

Universal finite-polyhedron regularity is closed under
composition. The intermediate domain is the actual finite
embedded image, so no common global triangulation is assumed.
See Hudson 1969, pp. 15--19 and M76 derivation 248.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Composing two ambient homeomorphisms finite PL on every
finite polyhedron preserves that same property. This controls
finite chains of local collar extensions. See derivation 248. -/
theorem finitePiecewiseAffineOn_trans_of_forall_finite_polyhedron (G H : E ≃ₜ E)
    (hG : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (G : E → E) K.space)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) :
    FinitePiecewiseAffineOn (G.trans H : E → E) L.space := by
  obtain ⟨K, hK, hKL, hfaces⟩ := hG L hL
  let M := hfaces.embeddedImage G.injective.injOn
  have hM : M.faces.Finite := hfaces.embeddedImage_finite _ hK
  have hMspace : M.space = G '' K.space := hfaces.embeddedImage_space _
  have hHimage : FinitePiecewiseAffineOn (H : E → E) (G '' L.space) := by
    rw [← hKL, ← hMspace]
    exact hH M hM
  exact hHimage.comp ⟨K, hK, hKL, hfaces⟩ (mapsTo_image _ _)

end Homeomorph
