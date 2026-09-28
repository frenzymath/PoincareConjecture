import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedPeriodInitialApproximation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ConvergentVectorInitialStates
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => State ((ℤ × Fin 2) × ι)

theorem exists_smooth_fixedPeriod_spectral_approximants
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) {U : Set W} (hU : IsOpen U)
    (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {t : ℝ} (ht : t ∈ Icc a b) {γ : ℝ → M}
    (hγp : Function.Periodic γ L) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 γ)
    (himm : ∀ x, curveVelocity (n := n) γ x ≠ 0)
    (hunit : ∀ x, curveSpeed F (fun y _ => γ y) t x = 1) :
    let c := fun x => e (γ x)
    let D0 := fun (z : S) (x : ℝ) =>
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) z (x : AddCircle L))
    let D1 := fun (z : S) (x : ℝ) =>
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) z (x : AddCircle L))
    ∃ (r : ℕ → ℝ → W) (m : ℕ → ℝ) (w : S) (wn : ℕ → S),
      (∀ j, 1 / 2 ≤ m j ∧ m j ≤ 3 / 2) ∧ Tendsto m atTop (𝓝 1) ∧
      (∀ j, ContDiff ℝ ∞ (r j)) ∧ (∀ j, Function.Periodic (r j) L) ∧
      (∀ j x, r j x ∈ U ∧ e (ρ (r j x)) = r j x) ∧
      (∀ j x, mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r j x) (deriv (r j) x) ≠ 0) ∧
      (∀ j x, curveSpeed F (fun y _ => ρ (r j y)) t x = m j) ∧
      (∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x,
        ‖r j x - c x‖ < eps ∧ ‖deriv (r j) x - deriv c x‖ < eps ∧
          ‖deriv (deriv (r j)) x - deriv (deriv c) x‖ < eps) ∧
      (∀ x, D0 w x = c x ∧ D1 w x = deriv c x) ∧
      (∀ j x, D0 (wn j) x = r j x ∧ D1 (wn j) x = deriv (r j) x) ∧
      Tendsto wn atTop (𝓝 w) ∧
      ∀ j, ContDiff ℝ ∞ (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s (wn j)) := by
  classical
  dsimp only
  let c := fun x => e (γ x)
  let eps := fun j : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j
  have heps (j : ℕ) : 0 < eps j := by dsimp only [eps]; positivity
  have hepshalf (j : ℕ) : eps j ≤ 1 / 2 := by
    have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [eps]
    linarith only [hp]
  have hepslim : Tendsto eps atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)).const_mul (1 / 2 : ℝ)
  have hepssmall (η : ℝ) (hη : 0 < η) : ∃ N : ℕ, ∀ j ≥ N, eps j < η := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hepslim η hη
    refine ⟨N, fun j hj => ?_⟩
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (heps j)] using hN j hj
  have happ (j : ℕ) := exists_smooth_constantSpeed_fixedPeriod_C2_approximation
    F he hU heU hρ hρe ht (Fact.out : 0 < L) hγp hγ himm hunit (heps j)
  choose r m _hmpos hmnear hr hrp hrfix hrimm hrspeed hrnear using happ
  have hc : ContDiff ℝ 2 c :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hγ).contDiff
  have hc1 : ContDiff ℝ 1 (deriv c) := hc.deriv' (n := 1)
  have hcd := hc.differentiable (by norm_num)
  have hcd1 := hc1.differentiable (by norm_num)
  have hcp : Function.Periodic c L := hγp.comp e
  have hcp1 := hcp.deriv_of_differentiable hcd
  have hcp2 := hcp1.deriv_of_differentiable hcd1
  have hr2 (j : ℕ) : ContDiff ℝ 2 (r j) :=
    (hr j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hr1 (j : ℕ) : ContDiff ℝ 1 (deriv (r j)) := (hr2 j).deriv' (n := 1)
  have hrd (j : ℕ) := (hr2 j).differentiable (by norm_num)
  have hrd1 (j : ℕ) := (hr1 j).differentiable (by norm_num)
  have hrp1 (j : ℕ) := (hrp j).deriv_of_differentiable (hrd j)
  have hrp2 (j : ℕ) := (hrp1 j).deriv_of_differentiable (hrd1 j)
  let lift (g : ℝ → W) (hg : Continuous g) (hp : Function.Periodic g L) :
      C(AddCircle L, W) := ⟨hp.lift,
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr hg⟩
  let f0 := lift c hc.continuous hcp
  let f1 := lift (deriv c) hc1.continuous hcp1
  let f2 := lift (deriv (deriv c)) hc1.continuous_deriv_one hcp2
  let fn0 := fun j => lift (r j) (hr j).continuous (hrp j)
  let fn1 := fun j => lift (deriv (r j)) (hr1 j).continuous (hrp1 j)
  let fn2 := fun j => lift (deriv (deriv (r j))) (hr1 j).continuous_deriv_one (hrp2 j)
  have hconv {f : C(AddCircle L, W)} {fs : ℕ → C(AddCircle L, W)}
      (hfs : ∀ j, ‖fs j - f‖ ≤ eps j) : Tendsto fs atTop (𝓝 f) := by
    apply Metric.tendsto_atTop.mpr
    intro η hη
    obtain ⟨N, hN⟩ := hepssmall η hη
    exact ⟨N, fun j hj => by simpa only [dist_eq_norm] using (hfs j).trans_lt (hN j hj)⟩
  have hfn0 : Tendsto fn0 atTop (𝓝 f0) := by
    apply hconv
    intro j
    apply (ContinuousMap.norm_le _ (heps j).le).mpr
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact (hrnear j y).1.le
  have hfn2 : Tendsto fn2 atTop (𝓝 f2) := by
    apply hconv
    intro j
    apply (ContinuousMap.norm_le _ (heps j).le).mpr
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact (hrnear j y).2.2.le
  let E : W ≃L[ℝ] (ι → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let A := E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)
  obtain ⟨w, wn, hw, hwn, hwnlim, hphase⟩ := exists_vectorPeriodic_initialStates_tendsto
    (A f0) (A f1) (A f2) (fun j => A (fn0 j)) (fun j => A (fn1 j)) (fun j => A (fn2 j))
    (fun x => E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x (hcd x).hasDerivAt)
    (fun x => E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x (hcd1 x).hasDerivAt)
    (fun j x => E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x (hrd j x).hasDerivAt)
    (fun j x => E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x (hrd1 j x).hasDerivAt)
    (A.continuous.continuousAt.tendsto.comp hfn0)
    (A.continuous.continuousAt.tendsto.comp hfn2)
  have hw0 (x : ℝ) : WithLp.toLp 2
      (vectorPeriodicJet (L := L) 1 0 (by omega) w (x : AddCircle L)) = c x := by
    rw [hw]
    exact E.symm_apply_apply (c x)
  have hwn0 (j : ℕ) (x : ℝ) : WithLp.toLp 2
      (vectorPeriodicJet (L := L) 1 0 (by omega) (wn j) (x : AddCircle L)) = r j x := by
    rw [hwn j]
    exact E.symm_apply_apply (r j x)
  have hfirst (z : S) (g : ℝ → W)
      (hz : ∀ x : ℝ, WithLp.toLp 2
        (vectorPeriodicJet (L := L) 1 0 (by omega) z (x : AddCircle L)) = g x)
      (x : ℝ) : WithLp.toLp 2
        (vectorPeriodicJet (L := L) 1 1 (by omega) z (x : AddCircle L)) = deriv g x := by
    have hd := E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_vectorPeriodicJet (L := L) (k := 1) (j := 0) (by omega) z x)
    change HasDerivAt (fun y : ℝ => E.symm
      (vectorPeriodicJet (L := L) 1 0 (by omega) z (y : AddCircle L))) _ x at hd
    have hf : (fun y : ℝ => E.symm
        (vectorPeriodicJet (L := L) 1 0 (by omega) z (y : AddCircle L))) = g := funext hz
    rw [hf] at hd
    exact hd.deriv.symm
  refine ⟨r, m, w, wn, ?_, ?_, hr, hrp, hrfix, hrimm, hrspeed, ?_,
    fun x => ⟨hw0 x, hfirst w c hw0 x⟩,
    fun j x => ⟨hwn0 j x, hfirst (wn j) (r j) (hwn0 j) x⟩, hwnlim, ?_⟩
  · intro j
    have hm := abs_lt.mp (hmnear j)
    have hhalf := hepshalf j
    constructor <;> linarith only [hm.1, hm.2, hhalf]
  · apply Metric.tendsto_atTop.mpr
    intro η hη
    obtain ⟨N, hN⟩ := hepssmall η hη
    exact ⟨N, fun j hj => by simpa only [Real.dist_eq] using (hmnear j).trans (hN j hj)⟩
  · intro η hη
    obtain ⟨N, hN⟩ := hepssmall η hη
    exact ⟨N, fun j hj x => ⟨(hrnear j x).1.trans (hN j hj),
      (hrnear j x).2.1.trans (hN j hj), (hrnear j x).2.2.trans (hN j hj)⟩⟩
  · intro j
    apply hphase j
    exact E.toContinuousLinearMap.contDiff.comp (hr j)

end PoincareConjecture.M63
