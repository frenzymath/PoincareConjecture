import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.ContractionAnnulus
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.AngularTangent









set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem m65ContractionAnnulusMap_mfderiv (C : ℝ × (M × M) → M)
    (gamma eta : C1FreeLoopSpace (M := M)) (p v : LoopPlane)
    (hC : ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
      (Real.smoothTransition (p 1), periodicFreeLoop eta (p 0),
        periodicFreeLoop gamma (p 0))) :
    mfderiv (𝓡 2) (𝓡 3) (m65ContractionAnnulusMap C gamma eta) p v =
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        (Real.smoothTransition (p 1), periodicFreeLoop eta (p 0),
          periodicFreeLoop gamma (p 0))
        (deriv Real.smoothTransition (p 1) * v 1,
          v 0 • curveVelocity (periodicFreeLoop eta) (p 0),
          v 0 • curveVelocity (periodicFreeLoop gamma) (p 0)) := by
  have hcoord (i : Fin 2) : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
      (fun q : LoopPlane => q i) p :=
    (show DifferentiableAt ℝ (fun q : LoopPlane => q i) p from
      (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt).mdifferentiableAt
  have hcoordd (i : Fin 2) : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun q : LoopPlane => q i) p v = v i := by
    rw [mfderiv_eq_fderiv]
    exact congrArg (fun d : LoopPlane →L[ℝ] ℝ => d v)
      (EuclideanSpace.proj (𝕜 := ℝ) i).fderiv
  have hsmooth : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hs : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      Real.smoothTransition (p 1) :=
    (hsmooth.differentiable one_ne_zero (p 1)).mdifferentiableAt
  have hsd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition (p 1) (v 1) =
      deriv Real.smoothTransition (p 1) * v 1 := by
    calc
      _ = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition (p 1) ((v 1) • (1 : ℝ)) :=
        by rw [smul_eq_mul, mul_one]
      _ = (v 1) • mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition (p 1) 1 := map_smul _ _ _
      _ = _ := by
        rw [mfderiv_eq_fderiv]
        change v 1 * (fderiv ℝ Real.smoothTransition (p 1)) 1 = _
        rw [fderiv_apply_one_eq_deriv, mul_comm]
  have hg := (contMDiff_periodicFreeLoop gamma).mdifferentiableAt one_ne_zero (x := p 0)
  have he := (contMDiff_periodicFreeLoop eta).mdifferentiableAt one_ne_zero (x := p 0)
  have htime := hs.comp p (hcoord 1)
  have hgamma := hg.comp p (hcoord 0)
  have heta := he.comp p (hcoord 0)
  have hchain := mfderiv_comp_apply (f := fun q : LoopPlane =>
      (Real.smoothTransition (q 1), periodicFreeLoop eta (q 0), periodicFreeLoop gamma (q 0)))
    (g := C) p (hC.mdifferentiableAt one_ne_zero)
    (htime.prodMk (heta.prodMk hgamma)) v
  erw [mfderiv_prodMk htime (heta.prodMk hgamma), mfderiv_prodMk heta hgamma] at hchain
  have hangle (loop : C1FreeLoopSpace (M := M)) :
      mfderiv (𝓡 2) (𝓡 3) (fun q : LoopPlane => periodicFreeLoop loop (q 0)) p v =
        v 0 • curveVelocity (periodicFreeLoop loop) (p 0) := by
    erw [mfderiv_comp_apply p
      ((contMDiff_periodicFreeLoop loop).mdifferentiableAt one_ne_zero) (hcoord 0), hcoordd]
    calc
      _ = mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (periodicFreeLoop loop) (p 0) ((v 0) • (1 : ℝ)) :=
        by rw [smul_eq_mul, mul_one]
      _ = _ := map_smul _ _ _
  have htimev : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun q : LoopPlane => Real.smoothTransition (q 1)) p v =
        deriv Real.smoothTransition (p 1) * v 1 := by
    erw [mfderiv_comp_apply p hs (hcoord 1), hcoordd, hsd]
  change mfderiv (𝓡 2) (𝓡 3) (m65ContractionAnnulusMap C gamma eta) p v =
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (Real.smoothTransition (p 1), periodicFreeLoop eta (p 0), periodicFreeLoop gamma (p 0))
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun q : LoopPlane => Real.smoothTransition (q 1)) p v,
        mfderiv (𝓡 2) (𝓡 3) (fun q : LoopPlane => periodicFreeLoop eta (q 0)) p v,
        mfderiv (𝓡 2) (𝓡 3) (fun q : LoopPlane => periodicFreeLoop gamma (q 0)) p v) at hchain
  erw [htimev, hangle, hangle] at hchain
  exact hchain

end PoincareConjecture
