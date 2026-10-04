/- Adapted from Mapher `PoincareMT/Proofs/M03/Existence/IntegralGaugeFTCNative.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Local.Gauge.Pullback.IntegralGaugeRecovery

/-!
# Integral reconstruction from the actual half-open-interval equation

A within derivative on Ico is an ordinary derivative at every interior
point. Its relative continuity controls the closed integration segment,
including its initial endpoint. The fundamental theorem of calculus then
supplies the exact integral identity used by IntegralGaugeRecovery.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff

universe u

namespace PoincareMT.IntegralGaugeFTCNative

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- FTC on each closed segment inside Ico, with no two-sided initial derivative. -/
theorem integral_eq_sub_of_hasDerivWithinAt_Ico {F f : ℝ → E} {a b t : ℝ}
    (hf : ContinuousOn f (Ico a b))
    (hF : ∀ s ∈ Ico a b, HasDerivWithinAt F (f s) (Ico a b) s)
    (ht : t ∈ Ico a b) :
    (∫ s in a..t, f s) = F t - F a := by
  have hsub : Icc a t ⊆ Ico a b := by
    intro s hs
    exact ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hcont : ContinuousOn F (Icc a t) := by
    intro s hs
    exact (hF s (hsub hs)).continuousWithinAt.mono hsub
  have hderiv : ∀ s ∈ Ioo a t, HasDerivAt F (f s) s := by
    intro s hs
    apply (hF s ⟨hs.1.le, hs.2.trans ht.2⟩).hasDerivAt
    apply mem_of_superset (Ioo_mem_nhds hs.1 (hs.2.trans ht.2))
    intro y hy
    exact ⟨hy.1.le, hy.2⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont hderiv
    ((hf.mono hsub).intervalIntegrable_of_Icc ht.1)

/-- The actual differential equation reconstructs its integral identity at every Ico time. -/
theorem eq_add_integral_of_hasDerivWithinAt_Ico {F f : ℝ → E} {a b t : ℝ}
    (hf : ContinuousOn f (Ico a b))
    (hF : ∀ s ∈ Ico a b, HasDerivWithinAt F (f s) (Ico a b) s)
    (ht : t ∈ Ico a b) :
    F t = F a + ∫ s in a..t, f s := by
  rw [integral_eq_sub_of_hasDerivWithinAt_Ico hf hF ht, add_comm, sub_add_cancel]

end Calculus

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Pairingwise FTC fills the integral-equation field of the existing gauge certificate. -/
theorem metric_inner_eq_add_integral_Ico {g₀ : RiemannianMetric n M}
    {metric : ℝ → RiemannianMetric n M} {T : ℝ}
    {source correction : ∀ (s : ℝ) (x : M),
      TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ}
    (hinitial : metric 0 = g₀)
    (hcont : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      ContinuousOn (fun s => source s x u v - correction s x u v) (Ico 0 T))
    (hderiv : ∀ s ∈ Ico 0 T, ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun r => (metric r).inner x u v)
        (source s x u v - correction s x u v) (Ico 0 T) s)
    (t : ℝ) (ht : t ∈ Ico 0 T) (x : M) (u v : TangentSpace (𝓡 n) x) :
    (metric t).inner x u v = g₀.inner x u v +
      ∫ s in (0 : ℝ)..t, source s x u v - correction s x u v := by
  have h := eq_add_integral_of_hasDerivWithinAt_Ico (hcont x u v)
    (fun s hs => hderiv s hs x u v) ht
  rw [hinitial] at h
  exact h

end PoincareMT.IntegralGaugeFTCNative

namespace PoincareMT.GaugeRecovery.Certificate

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M]

/-- Convert the existing derivative certificate using the proved FTC identity. -/
def toIntegral {g₀ : RiemannianMetric n M} (C : GaugeRecovery.Certificate g₀)
    (hcont : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      ContinuousOn (fun s => C.source s x u v - C.gaugeCorrection s x u v) (Ico 0 C.T)) :
    IntegralGaugeRecovery.Certificate g₀ where
  T := C.T
  hT := C.hT
  metric := C.metric
  connection := C.connection
  smooth := C.smooth
  initial := C.initial
  source := C.source
  gaugeCorrection := C.gaugeCorrection
  source_continuous := hcont
  integral_equation := IntegralGaugeFTCNative.metric_inner_eq_add_integral_Ico
    C.initial hcont C.transportedEquation
  cancellation := C.cancellation

@[simp] theorem toIntegral_metric {g₀ : RiemannianMetric n M} (C : GaugeRecovery.Certificate g₀)
    (hcont : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      ContinuousOn (fun s => C.source s x u v - C.gaugeCorrection s x u v) (Ico 0 C.T)) :
    (C.toIntegral hcont).metric = C.metric := rfl

end PoincareMT.GaugeRecovery.Certificate
