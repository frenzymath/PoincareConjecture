import PoincareConjecture.Proofs.M38.SchoenfliesPort.Geometry.Manifold.Circle.UnitSphere
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Geometry.Manifold.OneDimensional.Classification
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevelComponent







open _root_.AddCircle
open _root_.Poincare
open _root_.PoincareConjecture

namespace M38Schoenflies










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold.RegularLevel
open Poincare.Geometry.Manifold.OneDimensional
open Poincare.Geometry.Riemannian.SpaceForm
open PoincareConjecture.RiemannianMetric

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩



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

end

end M38Schoenflies
