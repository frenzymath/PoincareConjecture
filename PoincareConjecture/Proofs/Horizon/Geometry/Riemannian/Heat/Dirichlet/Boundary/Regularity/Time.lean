import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.ContinuousOperator
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}
  (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

def heatPowerContinuousTime (k : ℕ) (t : ℝ) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] (M →ᵇ ℝ) :=
  if ht : 0 < t then heatPowerContinuous D S k t ht else 0

theorem heatPowerContinuousTime_of_pos (k : ℕ) {t : ℝ} (ht : 0 < t) :
    heatPowerContinuousTime D S k t = heatPowerContinuous D S k t ht := by
  simp only [heatPowerContinuousTime, dif_pos ht]

private theorem heatSpectralPower_zero_comp (k : ℕ) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) :
    (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure 0 s).comp
      (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure k t) =
    heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k (s + t) := by
  ext f : 1
  apply (eigenbasis D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure).repr.injective
  ext i
  simp only [ContinuousLinearMap.comp_apply,
    heatSpectralPower_repr D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k (add_pos hs ht),
    heatSpectralPower_repr D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k ht,
    heatSpectralPower_repr D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure 0 hs, pow_zero, one_mul, mul_add, Real.exp_add]
  ring

private theorem heatPowerContinuous_zero_comp (k : ℕ) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) :
    (heatPowerContinuous D S 0 s hs).comp
      (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure k t) =
    heatPowerContinuousTime D S k (s + t) := by
  rw [heatPowerContinuousTime_of_pos D S k (add_pos hs ht)]
  ext f : 1
  apply heatPowerContinuous_unique D S k (s + t) (add_pos hs ht) f
  · have h := heatPowerContinuous_ae D S 0 s hs
      (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure k t f)
    change _ =ᵐ[g.volumeMeasure.restrict Ω]
      ((heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure 0 s).comp
        (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
          S.isOpen S.isCompact_closure k t) f : M → ℝ) at h
    rw [heatSpectralPower_zero_comp D S k s t hs ht] at h
    exact h
  · exact heatPowerContinuous_zero_outside D S 0 s hs _

theorem hasDerivAt_heatPowerContinuousTime (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (heatPowerContinuousTime D S k)
      (-heatPowerContinuousTime D S (k + 1) t) t := by
  let a := t / 2
  have ha : 0 < a := half_pos ht
  have hat : a < t := half_lt_self ht
  have hta : 0 < t - a := sub_pos.mpr hat
  let P := heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure
  let C := heatPowerContinuous D S 0 a ha
  have hdP : HasDerivAt (fun s : ℝ => P k (s - a)) (-P (k + 1) (t - a)) t := by
    have h := Poincare.Analysis.Dirichlet.Spectral.hasDerivAt_heatPower
      (eigenbasis D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure)
      (eigenvalueNN D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure)
      k hta
    convert! h.scomp t ((hasDerivAt_id t).sub_const a) using 1
    simp only [one_smul, P, heatSpectralPower]
  have hd : HasDerivAt (fun s : ℝ => C.comp (P k (s - a)))
      (-heatPowerContinuousTime D S (k + 1) t) t := by
    have h := (hasDerivAt_const t C).clm_comp hdP
    have hfactor := heatPowerContinuous_zero_comp D S (k + 1) a (t - a) ha hta
    have hsum : a + (t - a) = t := by ring
    rw [hsum] at hfactor
    change C.comp (P (k + 1) (t - a)) = _ at hfactor
    convert! h using 1
    simp only [ContinuousLinearMap.zero_comp, zero_add, ContinuousLinearMap.comp_neg, hfactor]
  have heq : heatPowerContinuousTime D S k =ᶠ[𝓝 t] fun s => C.comp (P k (s - a)) := by
    filter_upwards [Ioi_mem_nhds hat] with s hs
    have hfactor := heatPowerContinuous_zero_comp D S k a (s - a) ha (sub_pos.mpr hs)
    have hsum : a + (s - a) = s := by ring
    simpa only [hsum] using hfactor.symm
  convert! hd.congr_of_eventuallyEq heq using 1

theorem contDiffOn_heatPowerContinuousTime (k : ℕ) :
    ContDiffOn ℝ ∞ (heatPowerContinuousTime D S k) (Ioi 0) := by
  have hall : ∀ m : ℕ, ∀ j : ℕ,
      ContDiffOn ℝ m (heatPowerContinuousTime D S j) (Ioi 0) := by
    intro m
    induction m with
    | zero =>
      intro j
      simp only [Nat.cast_zero, contDiffOn_zero]
      intro t ht
      exact (hasDerivAt_heatPowerContinuousTime D S j ht).continuousAt.continuousWithinAt
    | succ m ih =>
      intro j
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun t ht =>
        (hasDerivAt_heatPowerContinuousTime D S j ht).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
      apply (ih (j + 1)).neg.congr
      intro t ht
      exact (hasDerivAt_heatPowerContinuousTime D S j ht).deriv
  exact contDiffOn_infty.mpr (fun m => hall m k)

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
