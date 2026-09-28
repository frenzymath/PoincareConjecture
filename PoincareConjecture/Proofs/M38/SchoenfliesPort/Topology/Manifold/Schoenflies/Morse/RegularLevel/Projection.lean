import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.Hyperplane
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenSubset
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.Circle

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold.RegularLevel
open _root_.Poincare.Geometry.Manifold

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := Metric.sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := Metric.sphere (0 : E3) 1
private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩

theorem regularLevel_projection_geometry
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (U : Opens S2) (hreg : ∀ p ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (c : Real) :
    letI := openLevelSetChartedSpace hh U hreg 1 c
    let q := fun p : openLevelSet h U c =>
      (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (openLevelIncl h U c p))
    ContMDiff (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞ q ∧ Injective q ∧
      ∀ p, Injective (mfderiv (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) q p) := by
  let := openLevelSetChartedSpace hh U hreg 1 c
  let j := openLevelIncl h U c
  have hj : ContMDiff (𝓡 1) (𝓡 2) ∞ j := contMDiff_openLevelIncl hh U hreg 1 c
  have hg : ContMDiff (𝓡 1) (𝓡 3) ∞ (f ∘ j) := hf.contMDiff.comp hj
  have hgc (p : openLevelSet h U c) : inner Real v ((f ∘ j) p) = c :=
    (hheight (j p)).trans p.property
  have hginj : Injective (f ∘ j) := hf.isEmbedding.injective.comp
    (isEmbedding_openLevelIncl h U c).injective
  have hgder (p : openLevelSet h U c) :
      Injective (mfderiv (𝓡 1) (𝓡 3) (f ∘ j) p) := by
    rw [mfderiv_comp p ((hf.contMDiff (j p)).mdifferentiableAt (by simp))
      ((hj p).mdifferentiableAt (by simp))]
    exact (injective_mfderiv_sphere_embedding hf (j p)).comp
      (injective_mfderiv_openLevelIncl hh U hreg 1 c p)
  exact ⟨(Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp hg,
    injective_projection_of_height_eq hv hgc hginj,
    injective_mfderiv_projection_of_height_eq hv hg hgc hgder⟩

theorem exists_smoothEmbedding_unitCircle_projection_regularLevelComponent
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (U : Opens S2) (hreg : ∀ p ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (c : Real) (hfull : h ⁻¹' {c} ⊆ (U : Set S2)) (p : openLevelSet h U c) :
    ∃ γ : S1 -> (Real ∙ v)ᗮ,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞ γ ∧
      range γ = (fun q : openLevelSet h U c =>
        (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (openLevelIncl h U c q))) ''
          connectedComponent p := by
  let := openLevelSetChartedSpace hh U hreg 1 c
  let := isManifold_openLevelSet hh U hreg 1 c
  let C := Poincare.connectedComponentOpens E1 p
  obtain ⟨e⟩ := nonempty_unitCircle_diffeomorph_regularLevelComponent hh U hreg c hfull p
  let j : S1 -> openLevelSet h U c := fun x => (e x : openLevelSet h U c)
  have hjlocal : IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞ j := by
    intro x
    exact (e.isLocalDiffeomorph x).comp (𝓡 1) (openLevelSet h U c)
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 1) C (e x))
  have hj : ContMDiff (𝓡 1) (𝓡 1) ∞ j := hjlocal.contMDiff
  have hjinj : Injective j := Subtype.val_injective.comp e.injective
  let q : openLevelSet h U c -> (Real ∙ v)ᗮ := fun x =>
    (Real ∙ v)ᗮ.orthogonalProjectionOnto (f (openLevelIncl h U c x))
  obtain ⟨hq, hqinj, hqder⟩ := regularLevel_projection_geometry hf hh hv hheight U hreg c
  let γ : S1 -> (Real ∙ v)ᗮ := q ∘ j
  have hγ : ContMDiff (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞ γ := hq.comp hj
  have hγder (x : S1) : Injective (mfderiv (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) γ x) := by
    rw [show γ = q ∘ j from rfl, mfderiv_comp x
      ((hq (j x)).mdifferentiableAt (by simp)) ((hj x).mdifferentiableAt (by simp))]
    exact (hqder (j x)).comp
      ((hjlocal x).mfderivToContinuousLinearEquiv (by simp)).injective
  refine ⟨γ, isSmoothEmbedding_of_injective_mfderiv hγ (hqinj.comp hjinj) hγder, ?_⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨j x, (e x).property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
    refine ⟨x, ?_⟩
    exact congrArg (fun w : C => q w) hx

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
