import PoincareConjecture.Proofs.M59.Mathlib.RadialDerivative
import PoincareConjecture.Proofs.M59.Mathlib.VectorBundleScalar
import PoincareConjecture.Proofs.M58.Sec18_4_ContractionEndpoints










set_option autoImplicit false

open Bundle Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

noncomputable section

universe u v

namespace PoincareConjecture

open Proofs.M58




theorem m59Plane_tangent_projection (z : LoopCircle) (v : LoopPlane) :
    v - ⟪z.val, v⟫ • z.val = ⟪loopCircleTangent z, v⟫ • loopCircleTangent z := by
  have hsquare : z.val 0 ^ 2 + z.val 1 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq z.val
    rw [z.property] at h
    simpa only [Fin.sum_univ_two, one_pow] using h.symm
  ext i
  fin_cases i
  · simp [loopCircleTangent, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination -(v 0) * hsquare
  · simp [loopCircleTangent, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination -(v 1) * hsquare

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



def m59RadialLoop (gamma : C1FreeLoopSpace (M := M)) : C1FreeLoopSpace (M := M) :=
  loopOfExtension (gamma.extension ∘ radialNormalization) (contMDiffOn_radial_extension gamma)



theorem m59RadialLoop_apply (gamma : C1FreeLoopSpace (M := M)) (z : LoopCircle) :
    m59RadialLoop gamma z = gamma z := by
  change gamma.extension (radialNormalization z.val) = gamma z
  rw [radialNormalization_of_norm_eq_one z.property, gamma.boundary]



theorem m59RadialLoop_tangent (gamma : C1FreeLoopSpace (M := M)) (z : LoopCircle) :
    c1LoopTangent (m59RadialLoop gamma) z = c1LoopTangent gamma z := by
  apply TotalSpace.ext
  · exact m59RadialLoop_apply gamma z
  · apply heq_of_eq
    exact mfderiv_radial_extension gamma z



theorem m59RadialLoop_constant (x : M) :
    m59RadialLoop (constantC1Loop x) = constantC1Loop x :=
  loop_eq_of_fields rfl rfl



theorem continuous_of_loop_firstJet_eq {X : Type v} [TopologicalSpace X]
    {f g : X → C1FreeLoopSpace (M := M)} (hg : Continuous g)
    (hvalues : ∀ x z, f x z = g x z)
    (htangents : ∀ x z, c1LoopTangent (f x) z = c1LoopTangent (g x) z) :
    Continuous f := by
  have h := (continuous_iff_values_tangents g).mp hg
  apply (continuous_iff_values_tangents f).mpr
  have hv : (fun x => loopValues (f x)) = (fun x => loopValues (g x)) :=
    funext fun x => ContinuousMap.ext (hvalues x)
  have ht : (fun x => loopTangents (f x)) = (fun x => loopTangents (g x)) :=
    funext fun x => ContinuousMap.ext (htangents x)
  exact ⟨hv ▸ h.1, ht ▸ h.2⟩



theorem continuous_m59RadialLoop : Continuous (m59RadialLoop (M := M)) :=
  continuous_of_loop_firstJet_eq continuous_id m59RadialLoop_apply m59RadialLoop_tangent



theorem m59RadialLoop_derivative (gamma : C1FreeLoopSpace (M := M))
    (z : LoopCircle) (i : Fin 2) :
    c1LoopDerivative (m59RadialLoop gamma) z i =
      (⟨gamma z, ⟪loopCircleTangent z, EuclideanSpace.basisFun (Fin 2) ℝ i⟫ •
        (c1LoopTangent gamma z).2⟩ : TangentBundle (𝓡 3) M) := by
  apply TotalSpace.ext
  · exact m59RadialLoop_apply gamma z
  · apply heq_of_eq
    change mfderiv (𝓡 2) (𝓡 3) (gamma.extension ∘ radialNormalization) z.val
      (EuclideanSpace.basisFun (Fin 2) ℝ i) = _
    have hz0 : z.val ≠ 0 := by
      intro h
      simpa [h] using z.property
    have hrad : MDifferentiableAt (𝓡 2) (𝓡 2) radialNormalization z.val :=
      (contDiffAt_radialNormalization hz0).contMDiffAt.mdifferentiableAt (by simp)
    have hF : MDifferentiableAt (𝓡 2) (𝓡 3) gamma.extension
        (radialNormalization z.val) := by
      rw [radialNormalization_of_norm_eq_one z.property]
      exact (contMDiffAt_loop_extension gamma.regularity z).mdifferentiableAt one_ne_zero
    have hD (v : LoopPlane) :
        mfderiv (𝓡 2) (𝓡 2) radialNormalization z.val v =
          ⟪loopCircleTangent z, v⟫ • loopCircleTangent z := by
      simpa +instances only [mfderiv_eq_fderiv] using!
        (Proofs.M59.fderiv_radialNormalization_unit z.property v).trans
          (m59Plane_tangent_projection z v)
    erw [mfderiv_comp_apply _ hF hrad, hD,
      radialNormalization_of_norm_eq_one z.property, map_smul]
    rfl



theorem continuous_m59RadialLoop_derivative {X : Type v} [TopologicalSpace X]
    (F : X → C1FreeLoopSpace (M := M)) (hF : Continuous F) (i : Fin 2) :
    Continuous (fun p : X × LoopCircle => c1LoopDerivative (m59RadialLoop (F p.1)) p.2 i) := by
  have hT : Continuous (fun p : X × LoopCircle => c1LoopTangent (F p.1) p.2) :=
    continuous_loop_tangent_eval.comp (hF.prodMap continuous_id)
  have hc : Continuous (fun p : X × LoopCircle =>
      ⟪loopCircleTangent p.2, EuclideanSpace.basisFun (Fin 2) ℝ i⟫) :=
    (continuous_loopCircleTangent.comp continuous_snd).inner continuous_const
  have h := hT.totalSpace_smul hc
  have heq : (fun p : X × LoopCircle => c1LoopDerivative (m59RadialLoop (F p.1)) p.2 i) =
      (fun p : X × LoopCircle =>
        (⟨F p.1 p.2, ⟪loopCircleTangent p.2, EuclideanSpace.basisFun (Fin 2) ℝ i⟫ •
          (c1LoopTangent (F p.1) p.2).2⟩ : TangentBundle (𝓡 3) M)) :=
    funext fun p => m59RadialLoop_derivative (F p.1) p.2 i
  rw [heq]
  exact h

end PoincareConjecture
