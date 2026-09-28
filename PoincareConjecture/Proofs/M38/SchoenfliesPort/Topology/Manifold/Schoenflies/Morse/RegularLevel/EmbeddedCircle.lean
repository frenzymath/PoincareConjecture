import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.Tube
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Manifold.RegularLevel
open _root_.M38Schoenflies.Poincare.Geometry.Manifold

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
private instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 2)) = 1 + 1) :=
  ⟨by simp⟩

theorem exists_smooth_circle_regularLevelComponent
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (c : Real) (hc : ∀ p, h p = c → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = c) :
    ∃ γ : S1 → S2, ContMDiff (𝓡 1) (𝓡 2) ∞ γ ∧ Function.Injective γ ∧
      (∀ x, Function.Injective (mfderiv (𝓡 1) (𝓡 2) γ x)) ∧
      range γ = connectedComponentIn (h ⁻¹' {c}) p := by
  let U : Opens S2 := ⟨{q | mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0},
    (Poincare.Geometry.Manifold.isClosed_setOf_mfderiv_eq_zero
      (hh.of_le (by simp))).isOpen_compl⟩
  have hreg : ∀ q ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 := fun _ hq => hq
  have hfull : h ⁻¹' {c} ⊆ (U : Set S2) := fun q hq => hc q hq
  let := openLevelSetChartedSpace hh U hreg 1 c
  let := isManifold_openLevelSet hh U hreg 1 c
  let pL : openLevelSet h U c := ⟨⟨p, hc p hp⟩, hp⟩
  let C := Poincare.connectedComponentOpens E1 pL
  obtain ⟨e⟩ := nonempty_unitCircle_diffeomorph_regularLevelComponent hh U hreg c hfull pL
  let j : S1 → openLevelSet h U c := fun x => (e x : openLevelSet h U c)
  have hjlocal : IsLocalDiffeomorph (𝓡 1) (𝓡 1) ∞ j := by
    intro x
    exact (e.isLocalDiffeomorph x).comp (𝓡 1) (openLevelSet h U c)
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 1) C (e x))
  have hj := hjlocal.contMDiff
  let γ : S1 → S2 := openLevelIncl h U c ∘ j
  have hγ : ContMDiff (𝓡 1) (𝓡 2) ∞ γ :=
    (contMDiff_openLevelIncl hh U hreg 1 c).comp hj
  have hinj : Function.Injective γ :=
    (isEmbedding_openLevelIncl h U c).injective.comp
      (Subtype.val_injective.comp e.injective)
  have hder (x : S1) : Function.Injective (mfderiv (𝓡 1) (𝓡 2) γ x) := by
    rw [show γ = openLevelIncl h U c ∘ j from rfl,
      mfderiv_comp x
        ((contMDiff_openLevelIncl hh U hreg 1 c (j x)).mdifferentiableAt (by simp))
        ((hj x).mdifferentiableAt (by simp))]
    exact (injective_mfderiv_openLevelIncl hh U hreg 1 c (j x)).comp
      ((hjlocal x).mfderivToContinuousLinearEquiv (by simp)).injective
  refine ⟨γ, hγ, hinj, hder, ?_⟩
  change range γ = connectedComponentIn (h ⁻¹' {c}) (openLevelIncl h U c pL)
  rw [← image_openLevel_component U c hfull pL]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨j x, (e x).property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
    exact ⟨x, congrArg (fun w : C => openLevelIncl h U c w) hx⟩

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
