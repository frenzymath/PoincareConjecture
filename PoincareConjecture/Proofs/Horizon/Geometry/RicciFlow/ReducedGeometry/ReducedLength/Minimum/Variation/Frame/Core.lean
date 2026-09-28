import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Frame.Transport

set_option autoImplicit false

open Set
open scoped BigOperators NNReal

noncomputable section

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open PoincareConjecture.RicciFlow.Frame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_metric_orthonormal_transport
    {J : Set ℝ} (G : EvolvingMetricData (V := E) J)
    {a c : ℝ} (hac : a < c) (A : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc a c)) {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a c, ‖A t‖₊ ≤ K)
    (hleft : ∀ t ∈ Icc a c, ∀ v w,
      G.metric t (A t v) w = G.ricci t v w)
    (hright : ∀ t ∈ Icc a c, ∀ v w,
      G.metric t v (A t w) = G.ricci t v w)
    (e : Fin (Module.finrank ℝ E) → E)
    (he : ∀ i j, G.metric a (e i) (e j) = if i = j then 1 else 0) :
    ∃ P : Fin (Module.finrank ℝ E) → ℝ → E,
      (∀ i, P i a = e i) ∧
      (∀ i t, t ∈ Icc a c →
        HasDerivWithinAt (P i) (A t (P i t)) (Icc a c) t) ∧
      (∀ t, t ∈ Icc a c → ∀ i j,
        G.metric t (P i t) (P j t) = if i = j then 1 else 0) := by
  let U := transportCurveOn A hac.le hA hK
  refine ⟨fun i t => U t (e i), ?_, ?_, ?_⟩
  · intro i
    change U a (e i) = e i
    rw [show U = transportCurveOn A hac.le hA hK by rfl]
    rw [transportCurveOn_left A hac.le hA hK]
    simp
  · intro i t ht
    simpa [U] using
      (transportCurveOn_hasDerivWithinAt A hac.le hA hK ht).clm_apply
        (hasDerivWithinAt_const t (Icc a c) (e i))
  · intro t ht i j
    rw [transport_isometry_on G A hac hA hK hleft hright ⟨t, ht⟩ (e i) (e j), he]

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
