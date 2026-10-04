import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Rotations
import PoincareLib.Geometry.RicciFlow.Pullback
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry

/-!
# The actual partial flow pulled back by a prescribed standard rotation

The literal SO(3) action is a global smooth linear equivalence. Its
pullback preserves the initial metric, retains the supplied compatible
connection at zero, and transports the actual curvature norm and bounds.
This is the uniqueness reduction in Morgan-Tian Section 12.5,
pp. 309-319; see rotation-invariance.md. No positive-time invariance or
noncompact uniqueness is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- The literal standard rotation is onto the original cap space
(Section 12.5, pp. 309-319). -/
theorem standardRotation_surjective (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Function.Surjective (standardRotation A) :=
  LinearMap.surjective_of_injective (f := (capRotationIsometry A).toLinearMap)
    (capRotationIsometry A).injective

/-- The prescribed rotation as a genuine linear isometric equivalence
(Section 12.5, pp. 309-319). -/
noncomputable def capRotationEquiv (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    StandardCapSpace ≃ₗᵢ[ℝ] StandardCapSpace :=
  LinearIsometryEquiv.ofSurjective (capRotationIsometry A) (standardRotation_surjective A)

/-- The frozen SO(3) action is a smooth local diffeomorphism everywhere
(Section 12.5, pp. 309-319). -/
theorem standardRotation_isLocalDiffeomorph
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (standardRotation A) :=
  (capRotationEquiv A).toContinuousLinearEquiv.toDiffeomorph.isLocalDiffeomorph

namespace PartialStandardCapFlow

variable {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
  (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)

/-- The total metric family obtained by the actual prescribed rotation
(Section 12.5, pp. 309-319). -/
noncomputable def rotatedMetric (t : ℝ) : RiemannianMetric 3 StandardCapSpace :=
  (F.flow.metric t).pullbackOfLocalDiffeomorph (standardRotation A)
    (standardRotation_isLocalDiffeomorph A)

/-- Initial rotation invariance identifies the entire pulled-back
initial metric record with the supplied one (Section 12.5, pp. 309-319). -/
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

/-- A compatible connection family retaining the supplied record at
zero, with the metric equality explicitly transported
(Section 12.5, pp. 309-319). -/
noncomputable def rotatedConnection (t : ℝ) : LeviCivitaData (rotatedMetric F A t) :=
  if ht : t = 0 then
    (by rw [ht, rotatedMetric_zero F A]; exact g0.connection)
  else (rotatedMetric F A t).euclideanLeviCivitaData

/-- The transported initial connection is heterogeneously equal to
the exact supplied record (Section 12.5, pp. 309-319). -/
theorem rotatedConnection_zero : HEq (rotatedConnection F A 0) g0.connection := by
  simp [rotatedConnection]

/-- Pullback by the fixed literal rotation gives an actual Ricci flow
on exactly the old time interval (Section 12.5, pp. 309-319). -/
noncomputable def rotatedFlow : RicciFlow 3 StandardCapSpace (Ico 0 F.lifetime) :=
  F.flow.pullbackWithConnection (standardRotation A)
    (standardRotation_isLocalDiffeomorph A) (rotatedConnection F A)

/-- The full curvature norm of the pulled-back flow is the original
norm at the rotated point (Section 12.5, pp. 309-319). -/
theorem rotatedFlow_curvatureTensorNorm (t : ℝ) (x : StandardCapSpace) :
    ((rotatedFlow F A).connection t).curvatureTensorNorm x =
      (F.flow.connection t).curvatureTensorNorm (standardRotation A x) := by
  apply LeviCivitaData.curvatureTensorNorm_eq_of_local_isometry
    ((rotatedFlow F A).connection t) (F.flow.connection t) isOpen_univ
    (standardRotation_isLocalDiffeomorph A).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)

/-- The rotated flow fills the same frozen partial-cap contract, with
the original lifetime and exactly the original initial records
(Section 12.5, pp. 309-319). -/
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

/-- The rotated partial flow has the exact bilinear pullback required
by the final literal-action invariance statement
(Section 12.5, pp. 309-319). -/
theorem rotatedPartialFlow_metric_inner (t : ℝ) (x : StandardCapSpace)
    (u v : TangentSpace (𝓡 3) x) :
    ((rotatedPartialFlow F A).flow.metric t).inner x u v =
      (F.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) := rfl

end PartialStandardCapFlow
end PoincareMT.M34
