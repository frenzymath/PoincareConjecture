import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.MorseChart

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
open Poincare.Geometry.Euclidean
open PlaneArcs.Terminal.Reflection

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

@[simp] theorem swapPlanarCoordinates_involutive (x : E2) :
    swapPlanarCoordinates (swapPlanarCoordinates x) = x := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem swapPlanarCoordinates_norm (x : E2) :
    ‖swapPlanarCoordinates x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    swapPlanarCoordinates_zero, swapPlanarCoordinates_one]
  ring

@[simp] theorem swapPlanarCoordinates_mem_closedBall (x : E2) (r : Real) :
    swapPlanarCoordinates x ∈ closedBall 0 r ↔ x ∈ closedBall 0 r := by
  simp only [mem_closedBall, dist_zero_right, swapPlanarCoordinates_norm]

@[simp] theorem swapPlanarCoordinates_mem_closedSquare (x : E2) (r : Real) :
    swapPlanarCoordinates x ∈ closedSquare r ↔ x ∈ closedSquare r := by
  change (|x 1| ≤ r ∧ |x 0| ≤ r) ↔ (|x 0| ≤ r ∧ |x 1| ≤ r)
  exact and_comm

@[simp] theorem swapPlanarCoordinates_mem_openSquare (x : E2) (r : Real) :
    swapPlanarCoordinates x ∈ openSquare r ↔ x ∈ openSquare r := by
  change (|x 1| < r ∧ |x 0| < r) ↔ (|x 0| < r ∧ |x 1| < r)
  exact and_comm

theorem reflectedMorseChart_image_openSquare
    (e : OpenPartialHomeomorph E2 S2) (r : Real) :
    reflectedMorseChart e '' openSquare r = e '' openSquare r := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨swapPlanarCoordinates x, (swapPlanarCoordinates_mem_openSquare x r).mpr hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨swapPlanarCoordinates x, (swapPlanarCoordinates_mem_openSquare x r).mpr hx, ?_⟩
    change e (swapPlanarCoordinates (swapPlanarCoordinates x)) = e x
    rw [swapPlanarCoordinates_involutive]

theorem square_source_reflection (e : OpenPartialHomeomorph E2 S2) (r : Real)
    (h : closedSquare r ⊆ (reflectedMorseChart e).source) :
    closedSquare r ⊆ e.source := by
  intro x hx
  have h' := h ((swapPlanarCoordinates_mem_closedSquare x r).mpr hx)
  have h'' := h'.2
  change swapPlanarCoordinates (swapPlanarCoordinates x) ∈ e.source at h''
  simpa only [swapPlanarCoordinates_involutive] using h''

theorem heightReflection_add_axis {v : E3} (hv : ‖v‖ = 1) (y : E3) (t : Real) :
    heightReflection hv (heightReflection hv y + (-t) • v) = y + t • v := by
  apply (heightCoordinates hv).symm.injective
  apply Prod.ext
  · change inner Real v (heightReflection hv _) = inner Real v _
    simp only [inner_heightReflection, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hv]
    ring
  · change (Real ∙ v)ᗮ.orthogonalProjectionOnto (heightReflection hv _) =
      (Real ∙ v)ᗮ.orthogonalProjectionOnto _
    simp only [projection_heightReflection, map_add, map_smul,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
      smul_zero, add_zero]

theorem flattened_levels_reflection
    {v : E3} (hv : ‖v‖ = 1) (g : S2 → E3) (p : S2)
    (e : OpenPartialHomeomorph E2 S2)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (r delta : Real) (strips : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b : Fin 2 → Real) (leftContact rightContact : Fin 2 → Real → Real)
    (hflat : ∀ t ∈ Icc (-delta) delta,
      (∀ i, ContinuousAt (leftContact i) t ∧ ContinuousAt (rightContact i) t ∧
        a i < leftContact i t ∧ leftContact i t < rightContact i t ∧ rightContact i t < b i) ∧
      (D ∘ heightReflection hv ∘ g) ''
        {q | inner Real v (heightReflection hv (g q)) =
          inner Real v (heightReflection hv (g p)) + t} =
        (D ∘ heightReflection hv ∘ g ∘ reflectedMorseChart e) ''
          (closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t}) ∪
        (⋃ i, (fun s => heightReflection hv (g (strips i (s, 0))) + t • v) ''
          Icc (a i) (b i)) ∧
      (D ∘ heightReflection hv ∘ g) ''
        ({q | inner Real v (heightReflection hv (g q)) =
          inner Real v (heightReflection hv (g p)) + t} \
          reflectedMorseChart e '' openSquare r) =
        ⋃ i, (fun s => heightReflection hv (g (strips i (s, 0))) + t • v) ''
          Icc (leftContact i t) (rightContact i t)) :
    ∀ t ∈ Icc (-delta) delta,
      (∀ i, ContinuousAt (fun z => leftContact i (-z)) t ∧
        ContinuousAt (fun z => rightContact i (-z)) t ∧
        a i < leftContact i (-t) ∧ leftContact i (-t) < rightContact i (-t) ∧
        rightContact i (-t) < b i) ∧
      (((heightReflection hv).trans D).trans (heightReflection hv) ∘ g) ''
        {q | inner Real v (g q) = inner Real v (g p) + t} =
        (((heightReflection hv).trans D).trans (heightReflection hv) ∘ g ∘ e) ''
          (closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t}) ∪
        (⋃ i, (fun s => g (strips i (s, 0)) + t • v) '' Icc (a i) (b i)) ∧
      (((heightReflection hv).trans D).trans (heightReflection hv) ∘ g) ''
        ({q | inner Real v (g q) = inner Real v (g p) + t} \ e '' openSquare r) =
        ⋃ i, (fun s => g (strips i (s, 0)) + t • v) ''
          Icc (leftContact i (-t)) (rightContact i (-t)) := by
  intro t ht
  obtain ⟨hc, hlevel, hout⟩ := hflat (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hset : {q | inner Real v (heightReflection hv (g q)) =
      inner Real v (heightReflection hv (g p)) + -t} =
      {q | inner Real v (g q) = inner Real v (g p) + t} := by
    ext q
    simp only [mem_ofPred_eq, inner_heightReflection]
    constructor <;> intro h <;> linarith
  rw [hset] at hlevel hout
  rw [reflectedMorseChart_image_openSquare] at hout
  have hsquare :
      (heightReflection hv) '' ((D ∘ heightReflection hv ∘ g ∘ reflectedMorseChart e) ''
        (closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = -t})) =
      (((heightReflection hv).trans D).trans (heightReflection hv) ∘ g ∘ e) ''
        (closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t}) := by
    rw [image_image]
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hq⟩, rfl⟩
      refine ⟨swapPlanarCoordinates x, ⟨(swapPlanarCoordinates_mem_closedSquare x r).mpr hx, ?_⟩, rfl⟩
      change -(x 1)^2 + (x 0)^2 = t
      change -(x 0)^2 + (x 1)^2 = -t at hq
      linarith
    · rintro ⟨x, ⟨hx, hq⟩, rfl⟩
      refine ⟨swapPlanarCoordinates x, ⟨(swapPlanarCoordinates_mem_closedSquare x r).mpr hx, ?_⟩, ?_⟩
      · change -(x 1)^2 + (x 0)^2 = -t
        change -(x 0)^2 + (x 1)^2 = t at hq
        linarith
      · change heightReflection hv (D (heightReflection hv
          (g (e (swapPlanarCoordinates (swapPlanarCoordinates x)))))) = _
        rw [swapPlanarCoordinates_involutive]
        rfl
  have hstrips (l u : Fin 2 → Real) :
      (heightReflection hv) '' (⋃ i,
        (fun s => heightReflection hv (g (strips i (s, 0))) + (-t) • v) '' Icc (l i) (u i)) =
        ⋃ i, (fun s => g (strips i (s, 0)) + t • v) '' Icc (l i) (u i) := by
    simp only [image_iUnion, image_image]
    congr 1
    funext i
    apply image_congr
    intro s _
    exact heightReflection_add_axis hv _ t
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨(hc i).1.comp continuousAt_id.neg,
      (hc i).2.1.comp continuousAt_id.neg, (hc i).2.2⟩
  · have h := congrArg (fun S => heightReflection hv '' S) hlevel
    rw [image_union, hsquare, hstrips] at h
    simpa only [image_image, Diffeomorph.coe_trans, Function.comp_def] using h
  · have h := congrArg (fun S => heightReflection hv '' S) hout
    rw [hstrips] at h
    simpa only [image_image, Diffeomorph.coe_trans, Function.comp_def] using h

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
