import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Caps.ReflectedSets
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

theorem exists_reflectedData
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3}
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    {p : S2} {e : OpenPartialHomeomorph E2 S2}
    (data : OrientationReview.TerminalSaddleData M P p e)
    (hk : data.toTerminalSaddleGeometry.model = Saddle.shear.trans Rz ∨
      data.toTerminalSaddleGeometry.model = (Saddle.Nested.shear (3 / 10)).trans Rz)
    (R : SphereMorseReduction M.reflectedOriginal) (hv : R.v = M.v)
    (Q : SphereSurgeryPath (R.v : E3)
      (fun q => R.D (M.reflectedOriginal q))
      (heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) ∘ g))
    (hcore : Q.core = P.core)
    (hinit : ∀ q, R.D (M.reflectedOriginal q) =
      heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) (M.D (f q))) :
    ∃ data' : SaddleLevel.TerminalSaddleData R Q p (reflectedMorseChart e),
      (∀ z, z ∈ data'.toTerminalSaddleGeometry.I ↔
        -z ∈ data.toTerminalSaddleGeometry.I) ∧
      (∀ z, data'.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.A (-z)) ∧
      (∀ z, data'.toTerminalSaddleGeometry.B z = data.toTerminalSaddleGeometry.B (-z)) ∧
      (∀ i, data'.toTerminalSaddleGeometry.C i = Rz '' data.toTerminalSaddleGeometry.C i) ∧
      (∀ i, data'.toTerminalSaddleGeometry.modelCaps i =
        Rz '' data.toTerminalSaddleGeometry.modelCaps i) ∧
      data'.toTerminalSaddleGeometry.actualBand = Rz '' data.toTerminalSaddleGeometry.actualBand ∧
      data'.toTerminalSaddleGeometry.modelBand = Rz '' data.toTerminalSaddleGeometry.modelBand := by
  let d := data.toTerminalSaddleGeometry
  let J := heightReflection (mem_sphere_zero_iff_norm.mp M.v.property)
  have hvalues : (fun q => inner Real (R.v : E3) (R.D (M.reflectedOriginal q))) =
      (fun q => inner Real (M.v : E3) (J (M.D (f q)))) := by
    funext q
    rw [hinit, hv]
  have hB : Neg.neg '' ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}) =
      (fun q => inner Real (R.v : E3) (R.D (M.reflectedOriginal q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (R.v : E3) (R.D (M.reflectedOriginal y))) q = 0} := by
    rw [hvalues]
    exact (Planar.reflected_critical_values _ _).symm
  obtain ⟨A, hl, hu, L, hcaps⟩ := Planar.ReflectedEnds.exists_back data.ends
    (mem_sphere_zero_iff_norm.mp M.v.property) (congrArg Subtype.val hv.symm)
    (rfl : J ∘ g = J ∘ g) hB hcore.symm
  let G := reflectedGeometry M P p e d R hv Q A hl hu L
  have hC := reflectedGeometry_C M P p e d R hv Q A hl hu L hcaps
  have hmodelCaps := reflectedGeometry_modelCaps M P p e d R hv Q A hl hu L
  have hactualBand := reflectedGeometry_actualBand M P p e d R hv Q A hl hu L
  have hmodelBand := reflectedGeometry_modelBand M P p e d R hv Q A hl hu L
  have hRz : Injective (Rz : E3 → E3) := Rz.injective
  let dataR : OrientationReview.TerminalSaddleData R Q p (reflectedMorseChart e) := {
    toTerminalSaddleGeometry := G
    actualDisk := data.actualDisk
    actualDisk_source := data.actualDisk_source
    actualDisk_smooth := data.actualDisk_smooth
    actualDisk_symm_smooth := data.actualDisk_symm_smooth
    actualDisk_image := by
      intro i
      exact (data.actualDisk_image i).trans (hcaps (d.labels i)).symm
    modelDisk := data.modelDisk
    modelDisk_source := data.modelDisk_source
    modelDisk_smooth := data.modelDisk_smooth
    modelDisk_symm_smooth := data.modelDisk_symm_smooth
    modelDisk_image := by
      intro i
      rw [reflectedGeometry_modelDomain]
      exact data.modelDisk_image i
    actual_decomposition := by
      change G.flatten '' range (J ∘ g) = G.actualBand ∪ ⋃ i, G.C i
      rw [reflectedGeometry_actual_image, data.actual_decomposition,
        image_union, image_iUnion, hactualBand]
      congr 1
      exact iUnion_congr (fun i => (hC i).symm)
    model_decomposition := by
      change G.flatten '' (G.filledModel '' sphere (0 : E3) 1) =
        G.modelBand ∪ ⋃ i, G.modelCaps i
      rw [reflectedGeometry_model_image, data.model_decomposition,
        image_union, image_iUnion, hmodelBand]
      congr 1
      exact iUnion_congr (fun i => (hmodelCaps i).symm)
    actual_boundary := by
      intro i
      change G.C i ∩ G.actualBand =
        (G.flatten ∘ (J ∘ g) ∘ data.actualDisk i) '' sphere (0 : E2) 1
      rw [hC, hactualBand, ← image_inter hRz, data.actual_boundary, image_image]
      apply image_congr
      intro x _
      exact (reflectedGeometry_flatten_leaf M P p e d R hv Q A hl hu L
        (data.actualDisk i x)).symm
    model_boundary := by
      intro i
      change G.modelCaps i ∩ G.modelBand =
        (fun x => G.flatten (G.filledModel (data.modelDisk i x))) '' sphere (0 : E2) 1
      rw [hmodelCaps, hmodelBand, ← image_inter hRz, data.model_boundary, image_image]
      apply image_congr
      intro x _
      exact (reflectedGeometry_flatten_model M P p e d R hv Q A hl hu L
        (data.modelDisk i x)).symm
    actual_disjoint := by
      intro i j hij
      rw [hC, hC]
      exact disjoint_image_of_injective Rz.injective (data.actual_disjoint hij)
    model_disjoint := by
      intro i j hij
      rw [hmodelCaps, hmodelCaps]
      exact disjoint_image_of_injective Rz.injective (data.model_disjoint hij) }
  have hkR : G.model = Saddle.shear ∨ G.model = Saddle.Nested.shear (3 / 10) := by
    change d.model.trans Rz = Saddle.shear ∨ d.model.trans Rz = Saddle.Nested.shear (3 / 10)
    rcases hk with hk | hk
    · left
      change data.model.trans Rz = _
      rw [hk]
      ext x i
      exact congrArg (fun y : E3 => y i) (Rz_involutive _)
    · right
      change data.model.trans Rz = _
      rw [hk]
      ext x i
      exact congrArg (fun y : E3 => y i) (Rz_involutive _)
  refine ⟨dataR.toAccepted hkR, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact reflectedGeometry_mem_I M P p e d R hv Q A hl hu L
  · exact reflectedGeometry_A M P p e d R hv Q A hl hu L
  · exact reflectedGeometry_B M P p e d R hv Q A hl hu L
  · exact hC
  · exact hmodelCaps
  · exact hactualBand
  · exact hmodelBand

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Caps
