import PoincareConjecture.Proofs.M47.RetainedNeckChart
import PoincareConjecture.Proofs.M44.Mathlib.SmoothChartInverse
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_BufferBalls
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions
import PoincareConjecture.Definitions.Ch15.SurgeryFlow











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}



theorem local_result_embedding_edist_le
    (E : SurgeryEventData g0 K P slice metric T) (i : Fin E.cap_count)
    (x y : (E.local_result i).output.carrier) :
    (metric T).edist (E.local_embed i x) (E.local_embed i y) ≤
      (E.local_result i).metric.edist x y :=
  (E.local_result i).metric.edist_comp_le_of_pullback_bound (metric T)
    (E.local_embed_smooth i) (fun z v => (E.local_metric i z v v).le) x y




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

end PoincareConjecture.Proofs.M47
