import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.ContractionDerivative










set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {X : Type v} [TopologicalSpace X]



theorem m65ContractionAnnulusMap_continuous_columns
    (C : ℝ × (M × M) → M) (gamma eta : X → C1FreeLoopSpace (M := M))
    (hgamma : Continuous gamma) (heta : Continuous eta)
    (hC : ∀ q : X × LoopPlane,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (Real.smoothTransition (q.2 1), periodicFreeLoop (eta q.1) (q.2 0),
          periodicFreeLoop (gamma q.1) (q.2 0))) (i : Fin 2) :
    Continuous (fun q : X × LoopPlane =>
      (⟨m65ContractionAnnulusMap C (gamma q.1) (eta q.1) q.2,
        mfderiv (𝓡 2) (𝓡 3) (m65ContractionAnnulusMap C (gamma q.1) (eta q.1)) q.2
          (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ : TangentBundle (𝓡 3) M)) := by
  have hg : Continuous (fun q : X × LoopPlane =>
      (⟨periodicFreeLoop (gamma q.1) (q.2 0),
        curveVelocity (periodicFreeLoop (gamma q.1)) (q.2 0)⟩ : TangentBundle (𝓡 3) M)) :=
    m65Continuous_periodicLoopTangent.comp
      ((hgamma.comp continuous_fst).prodMk (by fun_prop))
  have he : Continuous (fun q : X × LoopPlane =>
      (⟨periodicFreeLoop (eta q.1) (q.2 0),
        curveVelocity (periodicFreeLoop (eta q.1)) (q.2 0)⟩ : TangentBundle (𝓡 3) M)) :=
    m65Continuous_periodicLoopTangent.comp
      ((heta.comp continuous_fst).prodMk (by fun_prop))
  have hgval : Continuous (fun q : X × LoopPlane => periodicFreeLoop (gamma q.1) (q.2 0)) :=
    (FiberBundle.continuous_proj LoopAmbient (TangentSpace (𝓡 3))).comp hg
  have heval : Continuous (fun q : X × LoopPlane => periodicFreeLoop (eta q.1) (q.2 0)) :=
    (FiberBundle.continuous_proj LoopAmbient (TangentSpace (𝓡 3))).comp he
  have hsmooth : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have ht : Continuous (fun q : X × LoopPlane => Real.smoothTransition (q.2 1)) := by
    fun_prop
  have htd : Continuous (fun q : X × LoopPlane => deriv Real.smoothTransition (q.2 1)) :=
    (hsmooth.continuous_deriv le_rfl).comp (by fun_prop)
  fin_cases i
  · have hpair : Continuous (fun q : X × LoopPlane =>
        (⟨(periodicFreeLoop (eta q.1) (q.2 0), periodicFreeLoop (gamma q.1) (q.2 0)),
          (curveVelocity (periodicFreeLoop (eta q.1)) (q.2 0),
            curveVelocity (periodicFreeLoop (gamma q.1)) (q.2 0))⟩ :
          TangentBundle ((𝓡 3).prod (𝓡 3)) (M × M))) :=
      (contMDiff_equivTangentBundleProd_symm (I := 𝓡 3) (I' := 𝓡 3)
        (M := M) (M' := M) (n := 0)).continuous.comp (he.prodMk hg)
    have hreal : Continuous (fun q : X × LoopPlane =>
        (⟨Real.smoothTransition (q.2 1), 0⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (ht.prodMk continuous_const)
    have hinput := (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ))
      (I' := (𝓡 3).prod (𝓡 3)) (M := ℝ) (M' := M × M) (n := 0)).continuous.comp
        (hreal.prodMk hpair)
    have hout : Continuous (fun q : X × LoopPlane =>
        tangentMap (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          ⟨(Real.smoothTransition (q.2 1), periodicFreeLoop (eta q.1) (q.2 0),
              periodicFreeLoop (gamma q.1) (q.2 0)),
            (0, curveVelocity (periodicFreeLoop (eta q.1)) (q.2 0),
              curveVelocity (periodicFreeLoop (gamma q.1)) (q.2 0))⟩) :=
      continuous_iff_continuousAt.mpr fun q =>
        (continuousAt_tangentMap_of_contMDiffAt (hC q)).comp hinput.continuousAt
    convert hout using 1
    funext q
    apply TotalSpace.ext
    · rfl
    · apply heq_of_eq
      simpa +instances [EuclideanSpace.basisFun_apply, EuclideanSpace.single, tangentMap] using!
        m65ContractionAnnulusMap_mfderiv C (gamma q.1) (eta q.1) q.2
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) (hC q)
  · have hpair : Continuous (fun q : X × LoopPlane =>
        (⟨(periodicFreeLoop (eta q.1) (q.2 0), periodicFreeLoop (gamma q.1) (q.2 0)), 0⟩ :
          TangentBundle ((𝓡 3).prod (𝓡 3)) (M × M))) :=
      (Bundle.Trivialization.continuous_zeroSection ℝ).comp (heval.prodMk hgval)
    have hreal : Continuous (fun q : X × LoopPlane =>
        (⟨Real.smoothTransition (q.2 1), deriv Real.smoothTransition (q.2 1)⟩ :
          TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp (ht.prodMk htd)
    have hinput := (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ))
      (I' := (𝓡 3).prod (𝓡 3)) (M := ℝ) (M' := M × M) (n := 0)).continuous.comp
        (hreal.prodMk hpair)
    have hout : Continuous (fun q : X × LoopPlane =>
        tangentMap (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          ⟨(Real.smoothTransition (q.2 1), periodicFreeLoop (eta q.1) (q.2 0),
              periodicFreeLoop (gamma q.1) (q.2 0)),
            (deriv Real.smoothTransition (q.2 1), 0, 0)⟩) :=
      continuous_iff_continuousAt.mpr fun q =>
        (continuousAt_tangentMap_of_contMDiffAt (hC q)).comp hinput.continuousAt
    convert hout using 1
    funext q
    apply TotalSpace.ext
    · rfl
    · apply heq_of_eq
      simpa +instances [EuclideanSpace.basisFun_apply, EuclideanSpace.single, tangentMap] using!
        m65ContractionAnnulusMap_mfderiv C (gamma q.1) (eta q.1) q.2
          (EuclideanSpace.basisFun (Fin 2) ℝ 1) (hC q)



theorem m65ContractionAnnulusMap_continuous_density
    (g : RiemannianMetric 3 M) (C : ℝ × (M × M) → M)
    (gamma eta : X → C1FreeLoopSpace (M := M))
    (hgamma : Continuous gamma) (heta : Continuous eta)
    (hC : ∀ q : X × LoopPlane,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (Real.smoothTransition (q.2 1), periodicFreeLoop (eta q.1) (q.2 0),
          periodicFreeLoop (gamma q.1) (q.2 0))) :
    Continuous (fun q : X × LoopPlane =>
      m60AreaDensity g (m65ContractionAnnulusMap C (gamma q.1) (eta q.1)) q.2) := by
  let : RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hgram : Continuous (fun q : X × LoopPlane =>
      m60AreaGram g (m65ContractionAnnulusMap C (gamma q.1) (eta q.1)) q.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      (m65ContractionAnnulusMap_continuous_columns C gamma eta hgamma heta hC i).inner_bundle
        (m65ContractionAnnulusMap_continuous_columns C gamma eta hgamma heta hC j)
  exact (continuous_const.max hgram.matrix_det).sqrt

end PoincareConjecture
