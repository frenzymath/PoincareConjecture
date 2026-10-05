import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Retained.RetainedNeckChart
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Charts.SmoothChartInverse
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Bounds.BufferBalls
import PoincareLib.Geometry.Riemannian.Coordinates.Transitions
import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic

/-!
# The actual local-result embedding preserves seed volume

Theorem 13.2, pp. 332-333, in the Uniform Seed argument, pp. 392-393.
The supplied injective metric-preserving map has a smooth inverse on its
image. Its exact local volume identity and global distance inequality
do not require completeness or that its image be a whole component.
See the reviewed event-seed-geometry derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.Proofs.M47

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

/-- The literal local-result embedding decreases ambient path distance,
Theorem 13.2, pp. 332-333. No precompact-ball premise is required. -/
theorem local_result_embedding_edist_le
    (E : SurgeryEventData g0 K P slice metric T) (i : Fin E.cap_count)
    (x y : (E.local_result i).output.carrier) :
    (metric T).edist (E.local_embed i x) (E.local_embed i y) ≤
      (E.local_result i).metric.edist x y :=
  (E.local_result i).metric.edist_comp_le_of_pullback_bound (metric T)
    (E.local_embed_smooth i) (fun z v => (E.local_metric i z v v).le) x y

/-- The actual injective local-result embedding preserves calibrated
volume of every measurable set, including sets of infinite volume.
Theorem 13.2 and the Uniform Seed construction, pp. 332-333, 392-393. -/
theorem local_result_embedding_volume_eq
    (E : SurgeryEventData g0 K P slice metric T) (i : Fin E.cap_count)
    {A : Set (E.local_result i).output.carrier} (hA : MeasurableSet A) :
    calibratedMetricVolume (metric T) (E.local_embed i '' A) =
      calibratedMetricVolume (E.local_result i).metric A := by
  let R := E.local_result i
  let : Nonempty R.output.carrier := ⟨R.tip⟩
  let e := Poincare.partialDiffeomorphOfInjOn (E.local_embed i) univ isOpen_univ
    (E.local_embed_smooth i).contMDiffOn (E.local_embed_injective i).injOn
    (fun x _ => R.metric.mfderiv_bijective_of_pullback_eq (metric T) x (E.local_metric i x))
  have hmap : (e.toOpenPartialHomeomorph : R.output.carrier → (slice T).carrier) =
      E.local_embed i := rfl
  have hnorm (x : R.output.carrier) (v : TangentSpace (𝓡 3) x) :
      (metric T).tangentNorm (E.local_embed i x)
        (mfderiv (𝓡 3) (𝓡 3) (E.local_embed i) x v) = R.metric.tangentNorm x v :=
    congrArg Real.sqrt (E.local_metric i x v v)
  have hf := e.contMDiffOn.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hi := e.contMDiffOn_invFun.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hupper := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le
    R.metric (metric T) e.toOpenPartialHomeomorph hf (C := 1) zero_lt_one
    (fun x _ v => by
      change (metric T).tangentNorm (E.local_embed i x)
        (mfderiv (𝓡 3) (𝓡 3) (E.local_embed i) x v) ≤ 1 * R.metric.tangentNorm x v
      simpa only [one_mul] using (hnorm x v).le) hA (subset_univ A)
  have hlower := M34.calibratedMetricVolume_le_mul_image_of_local_tangentNorm_lower
    R.metric (metric T) e.toOpenPartialHomeomorph hf hi (C := 1) zero_lt_one
    (fun x _ v => by
      change R.metric.tangentNorm x v ≤ 1 * (metric T).tangentNorm (E.local_embed i x)
        (mfderiv (𝓡 3) (𝓡 3) (E.local_embed i) x v)
      simpa only [one_mul] using (hnorm x v).ge) hA (subset_univ A)
  exact le_antisymm
    (by simpa only [hmap, ENNReal.ofReal_one, one_pow, one_mul] using hupper)
    (by simpa only [hmap, ENNReal.ofReal_one, one_pow, one_mul] using hlower)

end PoincareMT.Proofs.M47
