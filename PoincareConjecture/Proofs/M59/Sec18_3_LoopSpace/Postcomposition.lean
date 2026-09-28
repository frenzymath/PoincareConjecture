import PoincareConjecture.Definitions.M59LoopIdentification
import PoincareConjecture.Proofs.M58.Sec18_4_ContractionEndpoints









set_option autoImplicit false

open Bundle
open scoped Manifold ContDiff Topology

noncomputable section

universe u

namespace PoincareConjecture

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]



theorem m59Loop_jet_eq_tangentMap (gamma : C1FreeLoopSpace (M := M))
    (z : LoopCircle) (v : LoopPlane) :
    (⟨gamma z, mfderiv (𝓡 2) (𝓡 3) gamma.extension z.val v⟩ : TangentBundle (𝓡 3) M) =
      tangentMap (𝓡 2) (𝓡 3) gamma.extension ⟨z.val, v⟩ := by
  apply TotalSpace.ext
  · exact (gamma.boundary z).symm
  · rfl



def m59PostcomposeLoop (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (gamma : C1FreeLoopSpace (M := M)) : C1FreeLoopSpace (M := N) :=
  Proofs.M58.loopOfExtension (f ∘ gamma.extension)
    ((hf.of_le (by simp)).comp_contMDiffOn gamma.regularity)



theorem m59PostcomposeLoop_apply (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (gamma : C1FreeLoopSpace (M := M)) (z : LoopCircle) :
    m59PostcomposeLoop f hf gamma z = f (gamma z) :=
  congrArg f (gamma.boundary z)



theorem m59PostcomposeLoop_jet (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (gamma : C1FreeLoopSpace (M := M)) (z : LoopCircle) (v : LoopPlane) :
    (⟨m59PostcomposeLoop f hf gamma z,
      mfderiv (𝓡 2) (𝓡 3) (m59PostcomposeLoop f hf gamma).extension z.val v⟩ :
        TangentBundle (𝓡 3) N) =
      tangentMap (𝓡 3) (𝓡 3) f
        (⟨gamma z, mfderiv (𝓡 2) (𝓡 3) gamma.extension z.val v⟩ :
          TangentBundle (𝓡 3) M) := by
  rw [m59Loop_jet_eq_tangentMap, m59Loop_jet_eq_tangentMap]
  exact tangentMap_comp_at ⟨z.val, v⟩
    (hf.mdifferentiable (by simp) _)
    ((Proofs.M58.contMDiffAt_loop_extension gamma.regularity z).mdifferentiableAt one_ne_zero)



theorem m59PostcomposeLoop_tangent (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (gamma : C1FreeLoopSpace (M := M)) (z : LoopCircle) :
    c1LoopTangent (m59PostcomposeLoop f hf gamma) z =
      tangentMap (𝓡 3) (𝓡 3) f (c1LoopTangent gamma z) :=
  m59PostcomposeLoop_jet f hf gamma z (loopCircleTangent z)



theorem m59PostcomposeLoop_derivative (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (gamma : C1FreeLoopSpace (M := M)) (z : LoopCircle) (i : Fin 2) :
    c1LoopDerivative (m59PostcomposeLoop f hf gamma) z i =
      tangentMap (𝓡 3) (𝓡 3) f (c1LoopDerivative gamma z i) :=
  m59PostcomposeLoop_jet f hf gamma z (EuclideanSpace.basisFun (Fin 2) ℝ i)



theorem continuous_m59PostcomposeLoop (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f) :
    Continuous (m59PostcomposeLoop f hf) := by
  apply (Proofs.M58.continuous_iff_values_tangents _).mpr
  constructor
  · have heq : (fun gamma => Proofs.M58.loopValues (m59PostcomposeLoop f hf gamma)) =
        (fun gamma => f.comp (Proofs.M58.loopValues gamma)) := by
      funext gamma
      ext z
      exact m59PostcomposeLoop_apply f hf gamma z
    rw [heq]
    exact (ContinuousMap.continuous_postcomp f).comp (Proofs.M58.loopValues (M := M)).continuous
  · let T : C(TangentBundle (𝓡 3) M, TangentBundle (𝓡 3) N) :=
      ⟨tangentMap (𝓡 3) (𝓡 3) f, hf.continuous_tangentMap (by simp)⟩
    have heq : (fun gamma => Proofs.M58.loopTangents (m59PostcomposeLoop f hf gamma)) =
        (fun gamma => T.comp (Proofs.M58.loopTangents gamma)) := by
      funext gamma
      apply ContinuousMap.ext
      intro z
      exact m59PostcomposeLoop_tangent f hf gamma z
    rw [heq]
    exact (ContinuousMap.continuous_postcomp T).comp (Proofs.M58.loopTangents (M := M)).continuous



def m59LoopPostcomposition (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f) :
    M59LoopPostcomposition f where
  map := ⟨m59PostcomposeLoop f hf, continuous_m59PostcomposeLoop f hf⟩
  extension_agreement _ _ := rfl
  maps_constant _ := Proofs.M58.loop_eq_of_fields rfl rfl



theorem m59LoopPostcomposition_apply {f : C(M, N)} (L : M59LoopPostcomposition f)
    (gamma : C1FreeLoopSpace (M := M)) (z : LoopCircle) :
    L.map gamma z = f (gamma z) :=
  ((L.map gamma).boundary z).symm.trans
    ((L.extension_agreement gamma z.val).trans (congrArg f (gamma.boundary z)))



theorem m59LoopPostcomposition_eq {f : C(M, N)} (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (L : M59LoopPostcomposition f) (gamma : C1FreeLoopSpace (M := M)) :
    L.map gamma = m59PostcomposeLoop f hf gamma := by
  apply Proofs.M58.loop_eq_of_fields
  · exact funext fun z =>
      (m59LoopPostcomposition_apply L gamma z).trans (m59PostcomposeLoop_apply f hf gamma z).symm
  · exact funext (L.extension_agreement gamma)

end PoincareConjecture
