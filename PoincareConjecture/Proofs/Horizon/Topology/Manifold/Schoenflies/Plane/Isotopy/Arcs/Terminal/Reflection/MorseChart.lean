import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.CoreCaps

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal.Reflection
open Poincare.Geometry.Euclidean
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def swapPlanarCoordinates : E2 ≃L[Real] E2 :=
  let C : E2 ≃L[Real] Real × Real := (EuclideanSpace.equiv (Fin 2) Real).trans
    (LinearEquiv.finTwoArrow Real Real).toContinuousLinearEquiv
  (C.trans (ContinuousLinearEquiv.prodComm Real Real Real)).trans C.symm

@[simp] theorem swapPlanarCoordinates_zero (x : E2) : swapPlanarCoordinates x 0 = x 1 := rfl
@[simp] theorem swapPlanarCoordinates_one (x : E2) : swapPlanarCoordinates x 1 = x 0 := rfl

def reflectedMorseChart (e : OpenPartialHomeomorph E2 S2) : OpenPartialHomeomorph E2 S2 :=
  swapPlanarCoordinates.toHomeomorph.toOpenPartialHomeomorph.trans e

@[simp] theorem reflectedMorseChart_target (e : OpenPartialHomeomorph E2 S2) :
    (reflectedMorseChart e).target = e.target := by
  ext q
  change (q ∈ e.target ∧ e.symm q ∈ univ) ↔ q ∈ e.target
  simp only [mem_univ, and_true]

theorem reflectedMorseChart_smooth (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (reflectedMorseChart e) (reflectedMorseChart e).source ∧
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (reflectedMorseChart e).symm (reflectedMorseChart e).target := by
  exact ⟨he.comp swapPlanarCoordinates.contDiff.contMDiff.contMDiffOn (fun x hx => hx.2),
    swapPlanarCoordinates.symm.contDiff.contMDiff.comp_contMDiffOn
      (hei.mono (fun x hx => hx.1))⟩

theorem reflectedMorseChart_center (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) :
    0 ∈ (reflectedMorseChart e).source ∧ reflectedMorseChart e 0 = e 0 := by
  refine ⟨⟨mem_univ _, ?_⟩, ?_⟩
  · change swapPlanarCoordinates 0 ∈ e.source
    simpa only [map_zero] using he0
  · change e (swapPlanarCoordinates 0) = e 0
    rw [map_zero]

theorem reflectedMorseChart_height {v : E3} (hv : ‖v‖ = 1) {g : S2 → E3} {p : S2}
    (e : OpenPartialHomeomorph E2 S2)
    (hform : ∀ x ∈ e.source, inner Real v (g (e x)) =
      inner Real v (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∀ x ∈ (reflectedMorseChart e).source,
      inner Real v (heightReflection hv (g (reflectedMorseChart e x))) =
        inner Real v (heightReflection hv (g p)) - x 0 ^ 2 + x 1 ^ 2 := by
  intro x hx
  change inner Real v (heightReflection hv (g (e (swapPlanarCoordinates x)))) = _
  rw [inner_heightReflection, inner_heightReflection, hform (swapPlanarCoordinates x) hx.2,
    swapPlanarCoordinates_zero, swapPlanarCoordinates_one]
  ring

theorem reflected_height_critical_iff {v : E3} (hv : ‖v‖ = 1) (g : S2 → E3) (p : S2) :
    mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real v (heightReflection hv (g q))) p = 0 ↔
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p = 0 := by
  have hh : (fun q : S2 => inner Real v (heightReflection hv (g q))) =
      -(fun q : S2 => inner Real v (g q)) := by
    funext q
    exact inner_heightReflection hv _
  rw [hh, mfderiv_neg, neg_eq_zero]

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal.Reflection
