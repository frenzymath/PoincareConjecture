import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Flattening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.TerminalInputs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
open Poincare.Geometry.Euclidean PlaneArcs.Terminal.Reflection
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def reflectGeometry {f : S2 → E3} {p : S2}
    (s : TerminalInputData f p)
    (s' : TerminalInputData s.reduction.reflectedOriginal p)
    (hv : s'.reduction.v = s.reduction.v)
    (hg : s'.leaf = heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property) ∘ s.leaf)
    (he : s'.chart = reflectedMorseChart s.chart)
    (d : SaddleLevel.TerminalSaddleGeometry s'.reduction s'.path p s'.chart)
    (A : SphereSurgeryCoreCap.AnnularEndFamily (s.reduction.v : E3) s.leaf
      ((fun q => inner Real (s.reduction.v : E3) (s.reduction.D (f q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (s.reduction.v : E3) (s.reduction.D (f y))) q = 0}) s.path.core)
    (hl : A.lowerCut = -d.ends.upperCut) (hu : A.upperCut = -d.ends.lowerCut)
    (L : d.ends.EndIndex ≃ A.EndIndex) :
    TerminalSaddleGeometry s.reduction s.path p s.chart := by
  let J := heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property)
  have hh (q : S2) : inner Real (s'.reduction.v : E3) (s'.leaf q) =
      -inner Real (s.reduction.v : E3) (s.leaf q) := by
    rw [hv, hg]
    exact inner_heightReflection _ _
  have hnorm (x : E2) : ‖swapPlanarCoordinates x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  have hball (x : E2) (hx : x ∈ closedBall 0 d.matchingRadius) :
      swapPlanarCoordinates x ∈ closedBall 0 d.matchingRadius := by
    simpa only [mem_closedBall, dist_zero_right, hnorm] using hx
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
  · apply square_source_reflection
    rw [← he]
    exact d.square_source
  · intro y
    change inner Real (s.reduction.v : E3) (J (d.D (J y))) = _
    rw [inner_heightReflection, ← hv, d.D_height, hv, inner_heightReflection, neg_neg]
  · apply flattened_levels_reflection
    simpa only [hv, hg, he, comp_assoc, comp_apply] using d.flattened_levels
  · rcases d.model_kind with h | h
    · exact Or.inr (Or.inr (Or.inl (congrArg (fun F => F.trans Rz) h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg (fun F => F.trans Rz) h)))
  · intro x hx
    have hs := d.matching_actual_source _ (hball x hx)
    have hs' := (show Real.sqrt d.scale • swapPlanarCoordinates x ∈
      (reflectedMorseChart s.chart).source from by simpa only [he] using hs).2
    change swapPlanarCoordinates (Real.sqrt d.scale • swapPlanarCoordinates x) ∈ s.chart.source at hs'
    simpa only [map_smul, swapPlanarCoordinates_involutive] using hs'
  · intro y
    change inner Real (s.reduction.v : E3) (J (d.transport (Rz y))) =
      inner Real (s.reduction.v : E3) (s.leaf p) + d.scale *
        (y 2 - Rz (d.model (reflectedMorseChart d.modelChart 0)) 2)
    have hT := d.transport_height (Rz y)
    rw [hh] at hT
    have hT' : inner Real (s.reduction.v : E3) (d.transport (Rz y)) =
        -inner Real (s.reduction.v : E3) (s.leaf p) +
          d.scale * (Rz y 2 - d.model (d.modelChart 0) 2) := by
      simpa only [hv] using hT
    rw [inner_heightReflection, hT']
    rw [(reflectedMorseChart_center _ d.modelChart_zero).2]
    simp only [Rz_two]
    ring
  · intro x hx
    change J (d.transport (Rz (Rz (d.model (d.modelChart (swapPlanarCoordinates x)))))) = _
    rw [Rz_involutive, d.matching _ (hball x hx)]
    simp only [hg, he, comp_apply]
    change J (J (s.leaf (s.chart (swapPlanarCoordinates
      (Real.sqrt d.scale • swapPlanarCoordinates x))))) = _
    simp only [J, heightReflection_heightReflection, map_smul, swapPlanarCoordinates_involutive]
  · rw [hl, d.upperCut_eq, hh]
    ring
  · rw [hu, d.lowerCut_eq, hh]
    ring
  · intro i hmem
    apply d.modelSeed_outside i
    change inner Real (s.reduction.v : E3) (J (d.transport (Rz (Rz (d.model (d.modelSeed i)))))) ∈
      Icc A.lowerCut A.upperCut at hmem
    rw [Rz_involutive, inner_heightReflection, hl, hu] at hmem
    simpa only [hv, mem_Icc] using
      And.intro (neg_le_neg_iff.mp hmem.2) (neg_le_neg_iff.mp hmem.1)

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
