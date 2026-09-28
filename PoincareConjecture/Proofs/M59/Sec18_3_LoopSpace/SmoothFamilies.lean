import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.LoopValueCongruence









set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

noncomputable section

universe u v w

namespace PoincareConjecture

open Proofs.M58

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in


theorem contMDiffOn_m59SmoothFamily (G : E × LoopPlane → M) (a : E)
    (hG : ∀ z : LoopCircle, ContMDiffAt 𝓘(ℝ, E × LoopPlane) (𝓡 3) 1 G (a, z.val)) :
    ContMDiffOn (𝓡 2) (𝓡 3) 1
      (fun w => G (a, radialNormalization w)) loopAnnulus := by
  intro w hw
  have hw0 : w ≠ 0 := by
    intro hzero
    have hp := hw.1
    norm_num [hzero] at hp
  let z : LoopCircle := ⟨radialNormalization w, norm_radialNormalization hw0⟩
  have hinput : ContDiffAt ℝ 1 (fun w : LoopPlane => (a, radialNormalization w)) w :=
    contDiffAt_const.prodMk ((contDiffAt_radialNormalization hw0).of_le (by simp))
  exact ((hG z).comp w hinput.contMDiffAt).contMDiffWithinAt



def m59SmoothFamilyLoop (G : E × LoopPlane → M) (a : E)
    (hG : ∀ z : LoopCircle, ContMDiffAt 𝓘(ℝ, E × LoopPlane) (𝓡 3) 1 G (a, z.val)) :
    C1FreeLoopSpace (M := M) :=
  loopOfExtension (fun w => G (a, radialNormalization w)) (contMDiffOn_m59SmoothFamily G a hG)



theorem m59SmoothFamilyLoop_apply (G : E × LoopPlane → M) (a : E)
    (hG : ∀ z : LoopCircle, ContMDiffAt 𝓘(ℝ, E × LoopPlane) (𝓡 3) 1 G (a, z.val))
    (z : LoopCircle) : m59SmoothFamilyLoop G a hG z = G (a, z.val) := by
  change G (a, radialNormalization z.val) = _
  rw [radialNormalization_of_norm_eq_one z.property]



theorem m59SmoothFamilyLoop_tangent (G : E × LoopPlane → M) (a : E)
    (hG : ∀ z : LoopCircle, ContMDiffAt 𝓘(ℝ, E × LoopPlane) (𝓡 3) 1 G (a, z.val))
    (z : LoopCircle) :
    c1LoopTangent (m59SmoothFamilyLoop G a hG) z =
      tangentMap 𝓘(ℝ, E × LoopPlane) (𝓡 3) G ⟨(a, z.val), (0, loopCircleTangent z)⟩ := by
  apply TotalSpace.ext
  · exact m59SmoothFamilyLoop_apply G a hG z
  · apply heq_of_eq
    have hz0 : z.val ≠ 0 := by
      intro hzero
      simpa only [hzero, norm_zero, zero_ne_one] using z.property
    have hr : DifferentiableAt ℝ (radialNormalization : LoopPlane → LoopPlane) z.val :=
      (contDiffAt_radialNormalization hz0).differentiableAt (by simp)
    have hi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E × LoopPlane)
        (fun w => (a, radialNormalization w)) z.val :=
      ((differentiableAt_const a).prodMk hr).mdifferentiableAt
    have heq : (a, radialNormalization z.val) = (a, z.val) := by
      rw [radialNormalization_of_norm_eq_one z.property]
    have hd : mfderiv (𝓡 2) 𝓘(ℝ, E × LoopPlane)
        (fun w => (a, radialNormalization w)) z.val (loopCircleTangent z) =
        (0, loopCircleTangent z) := by
      have h := (differentiableAt_const a).fderiv_prodMk hr
      have ht := congrArg (fun L => L (loopCircleTangent z)) h
      simpa +instances only [mfderiv_eq_fderiv, fderiv_fun_const, ContinuousLinearMap.prod_apply,
        Pi.zero_apply, zero_apply,
        fderiv_radialNormalization_tangent z.property (inner_loopCircleTangent z)] using! ht
    have h := mfderiv_comp_apply_of_eq z.val ((hG z).mdifferentiableAt one_ne_zero)
      hi heq (loopCircleTangent z)
    rw [hd] at h
    exact h



theorem continuous_m59SmoothFamilyLoop {B : Type w} [TopologicalSpace B]
    (G : E × LoopPlane → M) (a : B → E) (ha : Continuous a)
    (hG : ∀ b (z : LoopCircle), ContMDiffAt 𝓘(ℝ, E × LoopPlane) (𝓡 3) 1 G (a b, z.val)) :
    Continuous (fun b => m59SmoothFamilyLoop G (a b) (hG b)) := by
  have hinput : Continuous (fun p : B × LoopCircle => (a p.1, p.2.val)) :=
    (ha.comp continuous_fst).prodMk continuous_snd.subtype_val
  have hvalues : Continuous (fun p : B × LoopCircle => G (a p.1, p.2.val)) :=
    continuous_iff_continuousAt.mpr fun p => (hG p.1 p.2).continuousAt.comp
      (f := fun q : B × LoopCircle => (a q.1, q.2.val)) hinput.continuousAt
  have htinput : Continuous (fun p : B × LoopCircle =>
      (⟨(a p.1, p.2.val), (0, loopCircleTangent p.2)⟩ :
        TangentBundle 𝓘(ℝ, E × LoopPlane) (E × LoopPlane))) := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E × LoopPlane)).symm.continuous.comp
      (hinput.prodMk (continuous_const.prodMk (continuous_loopCircleTangent.comp continuous_snd)))
  have htangents : Continuous (fun p : B × LoopCircle =>
      tangentMap 𝓘(ℝ, E × LoopPlane) (𝓡 3) G
        ⟨(a p.1, p.2.val), (0, loopCircleTangent p.2)⟩) :=
    continuous_iff_continuousAt.mpr fun p =>
      (continuousAt_tangentMap_of_contMDiffAt (hG p.1 p.2)).comp htinput.continuousAt
  apply (continuous_iff_values_tangents _).mpr
  constructor
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : B × LoopCircle => m59SmoothFamilyLoop G (a p.1) (hG p.1) p.2)
    simpa only [m59SmoothFamilyLoop_apply] using hvalues
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : B × LoopCircle =>
      c1LoopTangent (m59SmoothFamilyLoop G (a p.1) (hG p.1)) p.2)
    simpa only [m59SmoothFamilyLoop_tangent] using htangents

end PoincareConjecture
