import PoincareConjecture.Definitions.M14GeneralizedLGeometry
import PoincareConjecture.Proofs.M11.BilinearBundleSmooth
import PoincareConjecture.Proofs.M11.PositiveFormBounded
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

noncomputable def auxiliarySpacetimeForm (F : GeneralizedFlowSpacetime n X time I)
    (q : F.Point) : TangentSpace (spacetimeModel n) q →L[ℝ]
      TangentSpace (spacetimeModel n) q →L[ℝ] ℝ := by
  let : Bundle.RiemannianBundle F.Horizontal := ⟨F.horizontalMetric.toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (spacetimeModel n) q) :=
    inferInstanceAs (NormedAddCommGroup (SpacetimeModelVector n))
  let : NormedSpace ℝ (TangentSpace (spacetimeModel n) q) :=
    inferInstanceAs (NormedSpace ℝ (SpacetimeModelVector n))
  let dt : TangentSpace (spacetimeModel n) q →L[ℝ] ℝ :=
    mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction q
  let B : F.Horizontal q →L[ℝ] F.Horizontal q →L[ℝ] ℝ := F.horizontalMetric.inner q
  let L : TangentSpace (spacetimeModel n) q →L[ℝ] F.Horizontal q := F.horizontalProjection q
  exact B.bilinearComp L L + dt.smulRight dt

theorem auxiliarySpacetimeForm_apply (F : GeneralizedFlowSpacetime n X time I)
    (q : F.Point) (v w : TangentSpace (spacetimeModel n) q) :
    auxiliarySpacetimeForm F q v w =
      F.horizontalMetric.inner q (F.horizontalProjection q v) (F.horizontalProjection q w) +
        (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction q v) *
          (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction q w) := rfl

theorem auxiliarySpacetimeForm_pos (F : GeneralizedFlowSpacetime n X time I)
    (q : F.Point) (v : TangentSpace (spacetimeModel n) q) (hv : v ≠ 0) :
    0 < auxiliarySpacetimeForm F q v v := by
  let dt : TangentSpace (spacetimeModel n) q →L[ℝ] ℝ :=
    mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction q
  change 0 < F.horizontalMetric.inner q (F.horizontalProjection q v)
      (F.horizontalProjection q v) + dt v * dt v
  by_cases hV : F.horizontalProjection q v = 0
  · have ht : dt v ≠ 0 := by
      intro ht
      apply hv
      have h := F.tangent_decomposition q v
      change v = dt v • F.timeVector q + (F.horizontalProjection q v).val at h
      simpa only [ht, zero_smul, hV, Submodule.coe_zero, zero_add] using h
    simp only [hV, map_zero, zero_add]
    exact mul_self_pos.mpr ht
  · exact add_pos_of_pos_of_nonneg (F.horizontalMetric.pos q _ hV) (mul_self_nonneg _)

theorem auxiliarySpacetimeForm_contMDiff (F : GeneralizedFlowSpacetime n X time I) :
    ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod
        𝓘(ℝ, SpacetimeModelVector n →L[ℝ] SpacetimeModelVector n →L[ℝ] ℝ)) ∞
      (fun q : F.Point => TotalSpace.mk'
        (SpacetimeModelVector n →L[ℝ] SpacetimeModelVector n →L[ℝ] ℝ)
        (E := fun q : F.Point => TangentSpace (spacetimeModel n) q →L[ℝ]
          TangentSpace (spacetimeModel n) q →L[ℝ] ℝ) q (auxiliarySpacetimeForm F q)) := by
  let : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  have ht : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ F.timeFunction := F.time_smooth
  have hp : ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) F.Point =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := F.Horizontal) v.proj
          (F.horizontalProjection v.proj v.2)) := F.horizontalProjection_smooth
  have hdt : ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n))
      𝓘(ℝ) ∞ (fun v : TangentBundle (spacetimeModel n) F.Point =>
        mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction v.proj v.2) :=
    (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).comp
      (ht.contMDiff_tangentMap (m := ∞) (by simp))
  intro q
  rw [← contMDiffWithinAt_univ]
  apply Proofs.M11.contMDiffWithinAt_bilinear_of_eval
    (IB := spacetimeModel n) (J := spacetimeModel n)
    (F := SpacetimeModelVector n)
    (E := (TangentSpace (spacetimeModel n) : F.Point → Type _))
    (b := id) (g := auxiliarySpacetimeForm F) contMDiffWithinAt_id
  intro v w
  have hv := Proofs.M11.frameVector_contMDiffAt (IB := spacetimeModel n)
    (E := (TangentSpace (spacetimeModel n) : F.Point → Type _)) q v
  have hw := Proofs.M11.frameVector_contMDiffAt (IB := spacetimeModel n)
    (E := (TangentSpace (spacetimeModel n) : F.Point → Type _)) q w
  have hV := hp.contMDiffAt.comp q hv
  have hW := hp.contMDiffAt.comp q hw
  have hpair : ContMDiffAt (spacetimeModel n) ((spacetimeModel n).prod 𝓘(ℝ)) ∞
      (fun z : F.Point => TotalSpace.mk' ℝ (E := Bundle.Trivial F.Point ℝ) z
        (F.horizontalMetric.inner z
          (F.horizontalProjection z
            ((trivializationAt (SpacetimeModelVector n)
              (TangentSpace (spacetimeModel n)) q).symmL ℝ z v))
          (F.horizontalProjection z
            ((trivializationAt (SpacetimeModelVector n)
              (TangentSpace (spacetimeModel n)) q).symmL ℝ z w)))) q :=
    F.horizontalMetric.contMDiff.contMDiffAt.clm_bundle_apply₂
      (F₃ := ℝ) (E₃ := Bundle.Trivial F.Point ℝ) hV hW
  have hmetric := (Bundle.contMDiffAt_totalSpace.mp hpair).2
  have htime := (hdt.contMDiffAt.comp q hv).mul (hdt.contMDiffAt.comp q hw)
  apply (hmetric.add htime).contMDiffWithinAt.congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall (fun _ => rfl)
  · rfl

noncomputable def auxiliarySpacetimeMetric (F : GeneralizedFlowSpacetime n X time I) :
    Bundle.ContMDiffRiemannianMetric (B := F.Point) (spacetimeModel n) ∞
      (SpacetimeModelVector n) (TangentSpace (spacetimeModel n) : F.Point → Type _) where
  inner := auxiliarySpacetimeForm F
  symm q v w := by
    simp only [auxiliarySpacetimeForm_apply]
    rw [F.horizontalMetric.symm q (F.horizontalProjection q v), mul_comm]
  pos := auxiliarySpacetimeForm_pos F
  isVonNBounded q := by
    let : NormedAddCommGroup (TangentSpace (spacetimeModel n) q) :=
      inferInstanceAs (NormedAddCommGroup (SpacetimeModelVector n))
    let : NormedSpace ℝ (TangentSpace (spacetimeModel n) q) :=
      inferInstanceAs (NormedSpace ℝ (SpacetimeModelVector n))
    let : FiniteDimensional ℝ (TangentSpace (spacetimeModel n) q) :=
      inferInstanceAs (FiniteDimensional ℝ (SpacetimeModelVector n))
    exact Proofs.M11.positiveForm_isVonNBounded
      (auxiliarySpacetimeForm F q) (auxiliarySpacetimeForm_pos F q)
  contMDiff := auxiliarySpacetimeForm_contMDiff F

end PoincareConjecture.M14
