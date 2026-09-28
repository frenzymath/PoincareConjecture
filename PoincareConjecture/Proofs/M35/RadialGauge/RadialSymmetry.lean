import PoincareConjecture.Proofs.M35.RadialGauge.HeatWeight
import PoincareConjecture.Proofs.M35.RadialGauge.WeightedSource
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem heatAverage_comp_linearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : V ≃ₗᵢ[ℝ] V) (f : V → F) (t : ℝ) (x : V) :
    heatAverage t f (L x) = heatAverage t (f ∘ L) x := by
  have hL : MeasurePreserving L (stdGaussian V) (stdGaussian V) :=
    ⟨L.continuous.measurable, stdGaussian_map L⟩
  unfold heatAverage
  rw [← hL.integral_comp L.toHomeomorph.measurableEmbedding
    (fun z => f (L x + Real.sqrt (2 * t) • z))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by simp only [Function.comp_apply, map_add, map_smul])

noncomputable def gaugeSource (b : V → V) (G : V → ℝ → ℝ) (u : V → ℝ) (x : V) : ℝ :=
  semilinearSource (b x) (G x) (u x) (fderiv ℝ u x)

theorem fderiv_of_orthogonal_invariant (L : V ≃ₗᵢ[ℝ] V) {u : V → ℝ}
    (hu : ∀ x, u (L x) = u x) (x : V) :
    (fderiv ℝ u (L x)).comp (L : V →L[ℝ] V) = fderiv ℝ u x := by
  have heq : u ∘ L = u := funext hu
  have h := (L.toContinuousLinearEquiv.comp_right_fderiv (f := u) (x := x)).symm
  change (fderiv ℝ u (L x)).comp (L : V →L[ℝ] V) = fderiv ℝ (u ∘ L) x at h
  rwa [heq] at h

theorem gaugeSource_invariant (L : V ≃ₗᵢ[ℝ] V)
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ}
    (hb : ∀ x, b (L x) = L (b x))
    (hG : ∀ x z, G (L x) z = G x z) (hu : ∀ x, u (L x) = u x) (x : V) :
    gaugeSource b G u (L x) = gaugeSource b G u x := by
  have hd := fderiv_of_orthogonal_invariant L hu x
  have heval := congrArg (fun p : V →L[ℝ] ℝ => p (b x)) hd
  have hnorm := congrArg norm hd
  simp only [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv] at hnorm
  change (fderiv ℝ u (L x)) (L (b x)) = (fderiv ℝ u x) (b x) at heval
  simp only [gaugeSource, semilinearSource, hb, hG, hu, heval, hnorm]

noncomputable def gaugeDuhamel (b : ℝ → V → V) (G : ℝ → V → ℝ → ℝ)
    (u : ℝ → V → ℝ) (t : ℝ) (x : V) : ℝ :=
  ∫ s in (0 : ℝ)..t, heatAverage (t - s) (gaugeSource (b s) (G s) (u s)) x

theorem gaugeDuhamel_invariant (L : V ≃ₗᵢ[ℝ] V)
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ}
    (hb : ∀ t x, b t (L x) = L (b t x))
    (hG : ∀ t x z, G t (L x) z = G t x z)
    (hu : ∀ t x, u t (L x) = u t x) (t : ℝ) (x : V) :
    gaugeDuhamel b G u t (L x) = gaugeDuhamel b G u t x := by
  apply intervalIntegral.integral_congr
  intro s _
  change heatAverage (t - s) (gaugeSource (b s) (G s) (u s)) (L x) =
    heatAverage (t - s) (gaugeSource (b s) (G s) (u s)) x
  rw [heatAverage_comp_linearIsometryEquiv]
  congr 1
  funext y
  exact gaugeSource_invariant L (hb s) (hG s) (hu s) y

noncomputable def gaugePicard (b : ℝ → V → V) (G : ℝ → V → ℝ → ℝ) :
    ℕ → ℝ → V → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => gaugeDuhamel b G (gaugePicard b G k)

theorem gaugePicard_invariant (L : V ≃ₗᵢ[ℝ] V)
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ}
    (hb : ∀ t x, b t (L x) = L (b t x))
    (hG : ∀ t x z, G t (L x) z = G t x z) (k : ℕ) (t : ℝ) (x : V) :
    gaugePicard b G k t (L x) = gaugePicard b G k t x := by
  induction k generalizing t x with
  | zero => rfl
  | succ k ih => exact gaugeDuhamel_invariant L hb hG ih t x

theorem gaugePicard_limit_invariant (L : V ≃ₗᵢ[ℝ] V)
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ}
    (hb : ∀ t x, b t (L x) = L (b t x))
    (hG : ∀ t x z, G t (L x) z = G t x z)
    (hu : ∀ t x, Tendsto (fun k => gaugePicard b G k t x) atTop (𝓝 (u t x)))
    (t : ℝ) (x : V) : u t (L x) = u t x := by
  apply tendsto_nhds_unique (hu t (L x))
  simpa only [gaugePicard_invariant L hb hG] using hu t x

theorem smooth_even_radial_trace {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hinvariant : ∀ (L : V ≃ₗᵢ[ℝ] V) x, u (L x) = u x) (e : V) :
    ContDiff ℝ ∞ (fun r : ℝ => u (r • e)) ∧ Function.Even (fun r : ℝ => u (r • e)) := by
  constructor
  · exact hu.comp (contDiff_id.smul contDiff_const)
  · intro r
    simpa only [LinearIsometryEquiv.coe_neg, neg_smul] using
      hinvariant (LinearIsometryEquiv.neg ℝ) (r • e)

end PoincareConjecture.M35.RadialGauge
