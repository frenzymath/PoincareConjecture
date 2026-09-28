import PoincareConjecture.Proofs.M58.Sec18_4_LoopLength
import PoincareConjecture.Proofs.M58.Sec18_4_LoopExtension
import PoincareConjecture.Proofs.M58.Sec18_4_LoopTopology










set_option autoImplicit false

open Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Proofs.M58



theorem m65AngularPoint_hasDerivAt (x : ℝ) :
    HasDerivAt angularPoint (loopCircleTangent ⟨angularPoint x, norm_angularPoint x⟩) x := by
  have h : HasDerivAt (fun r : ℝ => ![Real.cos r, Real.sin r])
      ![-Real.sin x, Real.cos x] x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Real.hasDerivAt_cos x
    · exact Real.hasDerivAt_sin x
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt x h

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem m65PeriodicLoopTangent_eq (gamma : C1FreeLoopSpace (M := M)) (x : ℝ) :
    (⟨periodicFreeLoop gamma x, curveVelocity (periodicFreeLoop gamma) x⟩ :
      TangentBundle (𝓡 3) M) =
        c1LoopTangent gamma ⟨angularPoint x, norm_angularPoint x⟩ := by
  let z : LoopCircle := ⟨angularPoint x, norm_angularPoint x⟩
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) angularPoint x 1 = loopCircleTangent z := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
      (m65AngularPoint_hasDerivAt x).deriv
  have hchain := mfderiv_comp_apply (f := angularPoint) (g := gamma.extension) x
    ((contMDiffAt_loop_extension gamma.regularity z).mdifferentiableAt one_ne_zero)
    (m65AngularPoint_hasDerivAt x).differentiableAt.mdifferentiableAt (1 : ℝ)
  erw [hd] at hchain
  apply TotalSpace.ext
  · exact gamma.boundary z
  · exact heq_of_eq hchain



theorem m65Continuous_periodicLoopTangent :
    Continuous (fun p : C1FreeLoopSpace (M := M) × ℝ =>
      (⟨periodicFreeLoop p.1 p.2, curveVelocity (periodicFreeLoop p.1) p.2⟩ :
        TangentBundle (𝓡 3) M)) := by
  simp_rw [m65PeriodicLoopTangent_eq]
  exact continuous_loop_tangent_eval.comp
    (continuous_fst.prodMk ((contDiff_angularPoint.continuous.comp continuous_snd).subtype_mk _))

end PoincareConjecture
