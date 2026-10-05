import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.Stationarity
import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.HarmonicCurvatureInequality
import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.ScalarMinimum
import PoincareLib.Geometry.RicciFlow.Area.FixedMap.CompactSlab
import PoincareLib.Geometry.Riemannian.Normalization.Connection.Existence
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.Normalization

/-!
# The branched minimal sphere area-variation bound

Morgan-Tian Claim 18.12, printed pp. 426-427, and Hamilton (1999),
printed p. 718. Energy stationarity supplies the actual harmonic equation.
The regularized curvature argument gives the Ricci integral bound, and
the fixed-map formula gives the area derivative on the closed time slab.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Every sphere satisfying the frozen branched-minimal predicate has the
required actual Ricci integral lower bound. Source: MT Claim 18.12,
pp. 426-427; Hamilton p. 718. -/
theorem m60SphereRicciTrace_integral_lower_bound {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (f : UnitTwoSphere → M) (hf : M60BranchedMinimalSphere g f)
    (ρ : ℝ) (hρ : ∀ p, ρ ≤ D.scalarCurvature (f p)) :
    4 * Real.pi + (ρ / 2) * m60SphereArea g f ≤
      ∫ z : LoopPlane, m60SphereRicciTraceDensity D f z := by
  obtain ⟨S⟩ := m01_exists_leviCivitaData m60RoundSphereMetric
  exact m60SphereRicciTrace_integral_lower_bound_of_harmonic D hD S f hf
    (m60EnergyStationary_chartHarmonic g f hf.smooth hf.energy_stationary) ρ hρ

/-- The complete minimal-sphere variation supplier on a compact closed
Ricci-flow slab, with every scalar lower bound and the attained minimum.
Source: MT Claim 18.12, pp. 426-427; Hamilton p. 718. -/
theorem m60MinimalSphereVariationProperties_of_compact {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (htensor : ∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus)
    (hscalar : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (Icc a b ×ˢ univ))
    (f : UnitTwoSphere → M) (t : ℝ) (ht : t ∈ Icc a b)
    (hf : M60BranchedMinimalSphere (F.metric t) f) :
    M60MinimalSphereVariationProperties F f t := by
  have hmin := m60ScalarMinimum_isLeast_of_flow F hcompact f hscalar ht
  have hvar := (m60SphereArea_variation_on_compact hab F hcompact htensor f
    (hf.smooth.of_le (by simp)) t ht).2
  have hbound (ρ : ℝ) (hρ : ∀ x : M, ρ ≤ (F.connection t).scalarCurvature x) :
      -(∫ z : LoopPlane, m60SphereRicciTraceDensity (F.connection t) f z) ≤
        -4 * Real.pi - (ρ / 2) * m60SphereArea (F.metric t) f := by
    have h := m60SphereRicciTrace_integral_lower_bound (F.connection t) (htensor t ht)
      f hf ρ (fun p => hρ (f p))
    linarith
  exact ⟨hmin, ⟨_, hvar, hbound, hbound _ (fun x => hmin.2 ⟨x, rfl⟩)⟩⟩

end PoincareMT
