import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Triangle.RadialGraph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Triangle.Affine
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Graph.Radial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

private instance : Fact (Module.finrank ℝ ℂ = 2) := ⟨by simp⟩
private instance : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩

theorem exists_ambient_diffeomorph_rounded_triangle
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {p : Polygon (EuclideanSpace ℝ (Fin 2)) 3} (hp : IsSimplePolygon p)
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 2 / 9)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ)
    (hρ : ContDiff ℝ ∞ ρ) (hder : ∀ t, |deriv ρ t| ≤ 1) :
    ∃ F : (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
      F '' sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =
        range (roundedPolygonParameter ρ p) := by
  obtain ⟨R, hR, hRbounds, hRrange⟩ :=
    exists_smooth_radial_graph_roundedEquilateral hδ hδsmall htail hbound hρ hder
  obtain ⟨G, _, hG⟩ := exists_ambient_diffeomorph_of_positive_radial_graph
    (LinearIsometryEquiv.refl ℝ ℂ) Complex.orientation R hR
    (fun q => lt_of_lt_of_le (by norm_num) (hRbounds q).1)
  obtain ⟨A, hA⟩ := exists_affine_diffeomorph_rounded_triangle e p hp.planeDet_triangle_ne_zero
  let E := e.symm.toContinuousLinearEquiv.toDiffeomorph
  refine ⟨(E.trans G).trans A, ?_⟩
  have hEsphere : E '' sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = sphere (0 : ℂ) 1 := by
    change e.symm '' sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = _
    simpa only [map_zero] using e.symm.image_sphere 0 1
  change (fun x => A (G (E x))) '' sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = _
  rw [← image_image A (fun x => G (E x)), ← image_image G E,
    hEsphere, hG, ← hRrange, ← range_comp]
  congr 1
  exact funext (hA ρ)

end Poincare.Manifold.Schoenflies.Plane
