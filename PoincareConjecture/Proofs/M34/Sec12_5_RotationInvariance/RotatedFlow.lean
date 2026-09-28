import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.Rotations
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Definitions.Ch12.StandardCap












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34



theorem standardRotation_surjective (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Function.Surjective (standardRotation A) :=
  LinearMap.surjective_of_injective (f := (capRotationIsometry A).toLinearMap)
    (capRotationIsometry A).injective



noncomputable def capRotationEquiv (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    StandardCapSpace ≃ₗᵢ[ℝ] StandardCapSpace :=
  LinearIsometryEquiv.ofSurjective (capRotationIsometry A) (standardRotation_surjective A)



theorem standardRotation_isLocalDiffeomorph
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (standardRotation A) :=
  (capRotationEquiv A).toContinuousLinearEquiv.toDiffeomorph.isLocalDiffeomorph

namespace PartialStandardCapFlow

variable {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
  (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)



noncomputable def rotatedMetric (t : ℝ) : RiemannianMetric 3 StandardCapSpace :=
  (F.flow.metric t).pullbackOfLocalDiffeomorph (standardRotation A)
    (standardRotation_isLocalDiffeomorph A)



theorem rotatedMetric_zero : rotatedMetric F A 0 = g0.metric := by
  have hinner : ∀ x (u v : TangentSpace (𝓡 3) x),
      (rotatedMetric F A 0).inner x u v = g0.metric.inner x u v := by
    intro x u v
    change (F.flow.metric 0).inner (standardRotation A x)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = _
    rw [F.initial_metric]
    exact g0.rotation_invariant A x u v
  cases h₁ : rotatedMetric F A 0
  cases h₂ : g0.metric
  rw [h₁, h₂] at hinner
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  ext u v
  exact hinner x u v




noncomputable def rotatedConnection (t : ℝ) : LeviCivitaData (rotatedMetric F A t) :=
  if ht : t = 0 then
    (by rw [ht, rotatedMetric_zero F A]; exact g0.connection)
  else (rotatedMetric F A t).euclideanLeviCivitaData



theorem rotatedConnection_zero : HEq (rotatedConnection F A 0) g0.connection := by
  simp [rotatedConnection]



noncomputable def rotatedFlow : RicciFlow 3 StandardCapSpace (Ico 0 F.lifetime) :=
  F.flow.pullbackWithConnection (standardRotation A)
    (standardRotation_isLocalDiffeomorph A) (rotatedConnection F A)



theorem rotatedFlow_curvatureTensorNorm (t : ℝ) (x : StandardCapSpace) :
    ((rotatedFlow F A).connection t).curvatureTensorNorm x =
      (F.flow.connection t).curvatureTensorNorm (standardRotation A x) := by
  apply LeviCivitaData.curvatureTensorNorm_eq_of_local_isometry
    ((rotatedFlow F A).connection t) (F.flow.connection t) isOpen_univ
    (standardRotation_isLocalDiffeomorph A).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)




noncomputable def rotatedPartialFlow : PartialStandardCapFlow g0 where
  lifetime := F.lifetime
  lifetime_pos := F.lifetime_pos
  flow := rotatedFlow F A
  initial_metric := rotatedMetric_zero F A
  initial_connection := rotatedConnection_zero F A
  curvature_locally_bounded := by
    intro T hT hTF
    obtain ⟨K, hK, hb⟩ := F.curvature_locally_bounded T hT hTF
    refine ⟨K, hK, ?_⟩
    intro t ht x
    rw [rotatedFlow_curvatureTensorNorm]
    exact hb t ht (standardRotation A x)




theorem rotatedPartialFlow_metric_inner (t : ℝ) (x : StandardCapSpace)
    (u v : TangentSpace (𝓡 3) x) :
    ((rotatedPartialFlow F A).flow.metric t).inner x u v =
      (F.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) := rfl

end PartialStandardCapFlow
end PoincareConjecture.M34
