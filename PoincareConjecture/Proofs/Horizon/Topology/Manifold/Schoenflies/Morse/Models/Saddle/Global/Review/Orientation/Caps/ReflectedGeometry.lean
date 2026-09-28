import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Data
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Ends
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Caps.Adapter



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Caps
open Poincare.Geometry.Euclidean PlaneArcs.Terminal.Reflection
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem reflectedMorseChart_twice (e : OpenPartialHomeomorph E2 S2) :
    reflectedMorseChart (reflectedMorseChart e) = e := by
  apply OpenPartialHomeomorph.ext
  · intro x
    exact congrArg e (swapPlanarCoordinates_involutive x)
  · intro q
    change swapPlanarCoordinates.symm (swapPlanarCoordinates.symm (e.symm q)) = e.symm q
    apply swapPlanarCoordinates.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact swapPlanarCoordinates.injective (by
      simp only [ContinuousLinearEquiv.apply_symm_apply, swapPlanarCoordinates_involutive])
  · ext x
    change (x ∈ univ ∧ swapPlanarCoordinates x ∈ univ ∧
      swapPlanarCoordinates (swapPlanarCoordinates x) ∈ e.source) ↔ x ∈ e.source
    simp only [mem_univ, true_and, swapPlanarCoordinates_involutive]

variable {f : S2 → E3} (M : SphereMorseReduction f) {g : S2 → E3}
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (p : S2) (e : OpenPartialHomeomorph E2 S2)
    (d : OrientationReview.TerminalSaddleGeometry M P p e)
    (R : SphereMorseReduction M.reflectedOriginal) (hv : R.v = M.v)
    (Q : SphereSurgeryPath (R.v : E3) (fun q => R.D (M.reflectedOriginal q))
      (heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) ∘ g))
    (A : SphereSurgeryCoreCap.AnnularEndFamily (R.v : E3)
      (heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) ∘ g)
      ((fun q => inner Real (R.v : E3) (R.D (M.reflectedOriginal q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (R.v : E3) (R.D (M.reflectedOriginal y))) q = 0}) Q.core)
    (hl : A.lowerCut = -d.ends.upperCut) (hu : A.upperCut = -d.ends.lowerCut)
    (L : d.ends.EndIndex ≃ A.EndIndex)

def reflectedGeometry :
    OrientationReview.TerminalSaddleGeometry R Q p (reflectedMorseChart e) := by
  let J := heightReflection (mem_sphere_zero_iff_norm.mp M.v.property)
  have hball (x : E2) (hx : x ∈ closedBall 0 d.matchingRadius) :
      swapPlanarCoordinates x ∈ closedBall 0 d.matchingRadius := by simpa using hx
  refine {
    D := (J.trans d.D).trans J
    frame := (J.trans d.frame).trans Rz
    frame_height := ?_
    frame_isometry := Rz_isometry.comp (d.frame_isometry.comp (heightReflection_isometry _))
    frame_zero := ?_
    r := d.r
    delta := d.delta
    r_pos := d.r_pos
    square_source := ?_
    delta_pos := d.delta_pos
    delta_lt := d.delta_lt
    D_height := ?_
    strips := d.strips
    a := d.a
    b := d.b
    leftContact := fun i t => d.leftContact i (-t)
    rightContact := fun i t => d.rightContact i (-t)
    flattened_levels := ?_
    model := d.model.trans Rz
    model_kind := ?_
    transport := (Rz.trans d.transport).trans J
    scale := d.scale
    scale_pos := d.scale_pos
    modelChart := reflectedMorseChart d.modelChart
    modelChart_zero := (reflectedMorseChart_center _ d.modelChart_zero).1
    modelChart_smooth := (reflectedMorseChart_smooth _ d.modelChart_smooth d.modelChart_symm_smooth).1
    modelChart_symm_smooth := (reflectedMorseChart_smooth _ d.modelChart_smooth d.modelChart_symm_smooth).2
    matchingRadius := d.matchingRadius
    matchingRadius_pos := d.matchingRadius_pos
    matching_source := fun x hx => ⟨mem_univ _, d.matching_source (hball x hx)⟩
    matching_actual_source := ?_
    transport_height := ?_
    matching := ?_
    ends := A
    eta := d.eta
    eta_pos := d.eta_pos
    eta_lt := d.eta_lt
    lowerCut_eq := ?_
    upperCut_eq := ?_
    labels := d.labels.trans L
    modelSeed := d.modelSeed
    modelSeed_outside := ?_ }
  · intro y
    change -(d.frame (J y) 2) = _
    rw [d.frame_height, hv]
    simp [J]
  · change Rz (d.frame (J 0)) = 0
    rw [show J 0 = 0 from heightReflection_zero _, d.frame_zero]
    ext i
    fin_cases i <;> simp
  · intro x hx
    exact ⟨mem_univ _, d.square_source ((swapPlanarCoordinates_mem_closedSquare x d.r).mpr hx)⟩
  · intro y
    change inner Real (R.v : E3) (J (d.D (J y))) = _
    rw [hv, inner_heightReflection, d.D_height, inner_heightReflection, neg_neg]
  · simp only [hv]
    apply flattened_levels_reflection (mem_sphere_zero_iff_norm.mp M.v.property)
      (J ∘ g) p (reflectedMorseChart e) d.D d.r d.delta d.strips d.a d.b
      d.leftContact d.rightContact
    simpa only [J, reflectedMorseChart_twice, comp_apply, comp_def,
      heightReflection_heightReflection] using d.flattened_levels
  · rcases d.model_kind with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (congrArg (fun F => F.trans Rz) h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg (fun F => F.trans Rz) h)))
    · left
      rw [h]
      ext x i
      exact congrArg (fun y : E3 => y i) (Rz_involutive _)
    · right; left
      rw [h]
      ext x i
      exact congrArg (fun y : E3 => y i) (Rz_involutive _)
  · intro x hx
    refine ⟨mem_univ _, ?_⟩
    change swapPlanarCoordinates (Real.sqrt d.scale • x) ∈ e.source
    rw [map_smul]
    exact d.matching_actual_source _ (hball x hx)
  · intro y
    change inner Real (R.v : E3) (J (d.transport (Rz y))) =
      inner Real (R.v : E3) (J (g p)) + d.scale *
        (y 2 - Rz (d.model (reflectedMorseChart d.modelChart 0)) 2)
    rw [hv, inner_heightReflection, inner_heightReflection, d.transport_height]
    rw [(reflectedMorseChart_center _ d.modelChart_zero).2]
    simp only [Rz_two]
    ring
  · intro x hx
    change J (d.transport (Rz (Rz (d.model (d.modelChart (swapPlanarCoordinates x)))))) = _
    rw [Rz_involutive, d.matching _ (hball x hx)]
    change J (g (e (Real.sqrt d.scale • swapPlanarCoordinates x))) =
      J (g (e (swapPlanarCoordinates (Real.sqrt d.scale • x))))
    rw [map_smul]
  · rw [hl, d.upperCut_eq, hv]
    change _ = inner Real (M.v : E3) (J (g p)) - _
    rw [inner_heightReflection]
    ring
  · rw [hu, d.lowerCut_eq, hv]
    change _ = inner Real (M.v : E3) (J (g p)) + _
    rw [inner_heightReflection]
    ring
  · intro i hmem
    apply d.modelSeed_outside i
    change inner Real (R.v : E3) (J (d.transport (Rz (Rz (d.model (d.modelSeed i)))))) ∈
      Icc A.lowerCut A.upperCut at hmem
    rw [Rz_involutive, hl, hu] at hmem
    simp only [hv, J, inner_heightReflection, mem_Icc] at hmem
    exact ⟨neg_le_neg_iff.mp hmem.2, neg_le_neg_iff.mp hmem.1⟩

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Caps
