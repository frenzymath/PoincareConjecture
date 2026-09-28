import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Sets







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.SaddleLevel
open _root_.PoincareConjecture

namespace M38Schoenflies



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




def reflectData {f : S2 → E3} {p : S2}
    (s : TerminalInputData f p)
    (s' : TerminalInputData s.reduction.reflectedOriginal p)
    (hv : s'.reduction.v = s.reduction.v)
    (hg : s'.leaf =
      heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property) ∘ s.leaf)
    (he : s'.chart = reflectedMorseChart s.chart)
    (data : SaddleLevel.TerminalSaddleData s'.reduction s'.path p s'.chart)
    (A : SphereSurgeryCoreCap.AnnularEndFamily (s.reduction.v : E3) s.leaf
      ((fun q => inner Real (s.reduction.v : E3) (s.reduction.D (f q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (s.reduction.v : E3) (s.reduction.D (f y))) q = 0}) s.path.core)
    (hl : A.lowerCut = -data.ends.upperCut) (hu : A.upperCut = -data.ends.lowerCut)
    (L : data.ends.EndIndex ≃ A.EndIndex)
    (hcaps : ∀ i, terminalEndCap A (L i) = SaddleLevel.terminalEndCap data.ends i) :
    TerminalSaddleData s.reduction s.path p s.chart := by
  let d := data.toTerminalSaddleGeometry
  let G := reflectGeometry s s' hv hg he d A hl hu L
  have hC := reflectGeometry_C s s' hv hg he d A hl hu L hcaps
  have hmodelCaps := reflectGeometry_modelCaps s s' hv hg he d A hl hu L
  have hactualBand := reflectGeometry_actualBand s s' hv hg he d A hl hu L
  have hmodelBand := reflectGeometry_modelBand s s' hv hg he d A hl hu L
  have hRz : Injective (Rz : E3 → E3) := Rz.injective
  refine {
    toTerminalSaddleGeometry := G
    actualDisk := data.actualDisk
    actualDisk_source := data.actualDisk_source
    actualDisk_smooth := data.actualDisk_smooth
    actualDisk_symm_smooth := data.actualDisk_symm_smooth
    actualDisk_image := ?_
    modelDisk := data.modelDisk
    modelDisk_source := data.modelDisk_source
    modelDisk_smooth := data.modelDisk_smooth
    modelDisk_symm_smooth := data.modelDisk_symm_smooth
    modelDisk_image := ?_
    actual_decomposition := ?_
    model_decomposition := ?_
    actual_boundary := ?_
    model_boundary := ?_
    actual_disjoint := ?_
    model_disjoint := ?_ }
  · intro i
    exact (data.actualDisk_image i).trans (hcaps (d.labels i)).symm
  · intro i
    rw [reflectGeometry_modelDomain]
    exact data.modelDisk_image i
  · change G.flatten '' range s.leaf = G.actualBand ∪ ⋃ i, G.C i
    rw [reflectGeometry_actual_image, data.actual_decomposition,
      image_union, image_iUnion, hactualBand]
    congr 1
    exact iUnion_congr (fun i => (hC i).symm)
  · change G.flatten '' (G.filledModel '' sphere (0 : E3) 1) =
      G.modelBand ∪ ⋃ i, G.modelCaps i
    rw [reflectGeometry_model_image, data.model_decomposition,
      image_union, image_iUnion, hmodelBand]
    congr 1
    exact iUnion_congr (fun i => (hmodelCaps i).symm)
  · intro i
    change G.C i ∩ G.actualBand =
      (G.flatten ∘ s.leaf ∘ data.actualDisk i) '' sphere (0 : E2) 1
    rw [hC, hactualBand, ← image_inter hRz, data.actual_boundary, image_image]
    apply image_congr
    intro x _
    exact (reflectGeometry_flatten_leaf s s' hv hg he d A hl hu L
      (data.actualDisk i x)).symm
  · intro i
    change G.modelCaps i ∩ G.modelBand =
      (fun x => G.flatten (G.filledModel (data.modelDisk i x))) '' sphere (0 : E2) 1
    rw [hmodelCaps, hmodelBand, ← image_inter hRz, data.model_boundary, image_image]
    apply image_congr
    intro x _
    exact (reflectGeometry_flatten_model s s' hv hg he d A hl hu L
      (data.modelDisk i x)).symm
  · intro i j hij
    rw [hC, hC]
    exact disjoint_image_of_injective Rz.injective (data.actual_disjoint hij)
  · intro i j hij
    rw [hmodelCaps, hmodelCaps]
    exact disjoint_image_of_injective Rz.injective (data.model_disjoint hij)

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview

end

end M38Schoenflies
