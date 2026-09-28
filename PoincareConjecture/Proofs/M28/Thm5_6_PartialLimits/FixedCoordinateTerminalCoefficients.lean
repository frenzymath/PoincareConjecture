import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.FixedCoordinateFlowLimit
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CoordinateGerms

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture.ChartDistance
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {tau : ℝ} {F : ∀ k, RicciFlow n (M k) (Icc (-tau) 0)}
  {V : Set (EuclideanSpace ℝ (Fin n))} {hV : IsOpen V} [Nonempty V]
  {e : ∀ k, V → M k}

set_option synthInstance.maxHeartbeats 200000 in

theorem FixedCoordinateFlowLimit.compact_pullbackCoefficients
    (L : FixedCoordinateFlowLimit F V hV e)
    (f : ∀ k, EuclideanSpace ℝ (Fin n) → M k)
    (hf : ∀ k (x : V), f k x = e k x)
    {t : ℝ} (ht : t ∈ Icc (-tau) 0)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKV : K ⊆ V) :
    TendstoUniformlyOn
      (fun k x => ((F (L.subsequence k)).metric t).pullbackCoefficients
        (f (L.subsequence k)) x)
      (fun x => L.coefficients (t, x)) atTop K := by
  let param := fun k => chartParametrization (fun _ : Unit => V) (fun _ => hV)
    (i := ()) (e k)
  have hparam (k : ℕ) : EqOn (param k) (f k) V := by
    intro x hx
    exact (chartParametrization_apply (fun _ : Unit => V) (fun _ => hV)
      (e k) ⟨x, hx⟩).trans (hf k ⟨x, hx⟩).symm
  have htest : ({t} ×ˢ K : Set (ℝ × EuclideanSpace ℝ (Fin n))) ⊆
      Icc (-tau) 0 ×ˢ V := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    rcases mem_singleton_iff.mp hs with rfl
    exact ⟨ht, hKV hx⟩
  have hjet := L.jets 0 ({t} ×ˢ K) (isCompact_singleton.prod hK) htest
  have heval := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet
  have hzero : TendstoUniformlyOn
      (fun k z => ((F (L.subsequence k)).metric z.1).pullbackCoefficients
        (param (L.subsequence k)) z.2) L.coefficients atTop ({t} ×ˢ K) := by
    simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using heval
  have hslice : TendstoUniformlyOn
      (fun k x => ((F (L.subsequence k)).metric t).pullbackCoefficients
        (param (L.subsequence k)) x)
      (fun x => L.coefficients (t, x)) atTop K := by
    exact (hzero.comp (fun x => (t, x))).mono
      (fun x hx => ⟨mem_singleton t, hx⟩)
  apply hslice.congr
  refine Eventually.of_forall fun k x hx => ?_
  exact ((F (L.subsequence k)).metric t).pullbackCoefficients_eq_of_eventuallyEq
    (Filter.mem_of_superset (hV.mem_nhds (hKV hx)) (hparam (L.subsequence k)))

theorem FixedCoordinateFlowLimit.compact_coefficient_bounds
    (L : FixedCoordinateFlowLimit F V hV e)
    (f : ∀ k, EuclideanSpace ℝ (Fin n) → M k)
    (hf : ∀ k (x : V), f k x = e k x)
    {t : ℝ} (ht : t ∈ Icc (-tau) 0)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKV : K ⊆ V)
    {alpha beta : ℝ}
    (hbound : ∀ k x, x ∈ K → ∀ v,
      alpha * ‖v‖ ^ 2 ≤ ((F k).metric t).pullbackCoefficients (f k) x v v ∧
        ((F k).metric t).pullbackCoefficients (f k) x v v ≤ beta * ‖v‖ ^ 2) :
    ∀ x ∈ K, ∀ v,
      alpha * ‖v‖ ^ 2 ≤ L.coefficients (t, x) v v ∧
        L.coefficients (t, x) v v ≤ beta * ‖v‖ ^ 2 := by
  intro x hx v
  have hpoint := (L.compact_pullbackCoefficients f hf ht hK hKV).tendsto_at hx
  have hvalue := ((ContinuousLinearMap.apply ℝ ℝ v).continuous.tendsto _).comp
    (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp hpoint)
  exact ⟨ge_of_tendsto hvalue (Eventually.of_forall fun k =>
    (hbound (L.subsequence k) x hx v).1),
    le_of_tendsto hvalue (Eventually.of_forall fun k =>
      (hbound (L.subsequence k) x hx v).2)⟩

end PoincareConjecture.M28
