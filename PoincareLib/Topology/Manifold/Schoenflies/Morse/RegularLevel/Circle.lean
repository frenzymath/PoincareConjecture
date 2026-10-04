import PoincareLib.Geometry.Manifold.Circle.UnitSphere
import PoincareLib.Geometry.Manifold.OneDimensional.Classification
import PoincareLib.Geometry.Riemannian.Metric.Induced.RegularLevelComponent

/-!
# Circle parametrizations of regular sphere-level components

A component of a full regular level is a compact connected one-manifold
with its induced round-sphere metric. Classification by a periodic geodesic,
followed by the standard circle exponential, gives a diffeomorphism from the
actual Euclidean unit circle.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold.RegularLevel
open Poincare.Geometry.Manifold.OneDimensional
open Poincare.Geometry.Riemannian.SpaceForm
open PoincareMT.RiemannianMetric

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩

/-- Compactness of an isolated regular level suffices for its components to
admit smooth parametrizations by the standard Euclidean unit circle. -/
theorem nonempty_unitCircle_diffeomorph_regularLevelComponent_of_isCompact
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (U : Opens S2) (hreg : ∀ x ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0)
    (c : Real) (hcompact : IsCompact ((U : Set S2) ∩ h ⁻¹' {c}))
    (p : openLevelSet h U c) :
    letI := openLevelSetChartedSpace hh U hreg 1 c
    Nonempty (Diffeomorph (𝓡 1) (𝓡 1) S1
      (Poincare.connectedComponentOpens E1 p) ∞) := by
  let := openLevelSetChartedSpace hh U hreg 1 c
  let := isManifold_openLevelSet hh U hreg 1 c
  let C := Poincare.connectedComponentOpens E1 p
  let gC := (regularLevelMetric hh U hreg c (roundSphereMetric 2)).connectedComponentMetric p
  let : CompactSpace C := compactSpace_regularLevelComponent hh U hreg c hcompact p
  obtain ⟨T, hT, A, hA, hquotient, ⟨e⟩⟩ :=
    exists_addCircle_diffeomorph_of_compact_connected gC
  let := A
  let := hA
  exact ⟨(AddCircle.unitSphereDiffeomorph hT hquotient).symm.trans e⟩

/-- Every component of a full regular level of a smooth sphere height admits
a smooth parametrization by the standard Euclidean unit circle. -/
theorem nonempty_unitCircle_diffeomorph_regularLevelComponent
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (U : Opens S2) (hreg : ∀ x ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0)
    (c : Real) (hfull : h ⁻¹' {c} ⊆ (U : Set S2))
    (p : openLevelSet h U c) :
    letI := openLevelSetChartedSpace hh U hreg 1 c
    Nonempty (Diffeomorph (𝓡 1) (𝓡 1) S1
      (Poincare.connectedComponentOpens E1 p) ∞) := by
  apply nonempty_unitCircle_diffeomorph_regularLevelComponent_of_isCompact hh U hreg c ?_ p
  rw [inter_eq_right.mpr hfull]
  exact (isClosed_singleton.preimage hh.continuous).isCompact

end Poincare.Manifold.Schoenflies
