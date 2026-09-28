import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialResponseTrace
import Mathlib.Topology.CompactOpen

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M63

open SpectralHeatNative

theorem exists_initialResponseTrace_neighborhood
    {iota K Y : Type*} [Countable iota] [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace Y] (lambda : iota → NNReal) (w : State iota)
    (D : State iota → C(K, Y)) (hD : Continuous D)
    {O : Set (ℝ × Y)} (hO : IsOpen O) (hinit : ∀ x, (0, D w x) ∈ O)
    {Tcap : ℝ} (hTcap : 0 < Tcap) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∃ T0 : ℝ, 0 < T0 ∧ T0 ≤ Tcap ∧ T0 ≤ 1 ∧
      ∀ T : ℝ, ∀ hT : 0 ≤ T, T ≤ T0 → ∀ F : ForcingSpace iota T,
        ‖F‖ < r0 / 2 → ∀ t : Icc (0 : ℝ) T, ∀ x : K,
          ((t : ℝ), D (initialResponseTrace lambda w hT F t) x) ∈ O := by
  let H : ℝ × State iota → C(K, ℝ × Y) := fun z =>
    (ContinuousMap.const K z.1).prodMk (D z.2)
  have hH : Continuous H :=
    ContinuousMap.continuous_prodMk_const.comp
      (continuous_fst.prodMk (hD.comp continuous_snd))
  have hN : H ⁻¹' {g : C(K, ℝ × Y) | MapsTo g univ O} ∈ 𝓝 (0, w) :=
    ((ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hO).preimage hH).mem_nhds
      (fun x _ => hinit x)
  obtain ⟨eps, heps, hnear⟩ := Metric.mem_nhds_iff.mp hN
  have hheat : Continuous (fun t : ℝ => heat lambda t.toNNReal w) :=
    (continuous_heat_apply lambda w).comp continuous_real_toNNReal
  obtain ⟨delta, hdelta, hheatNear⟩ := Metric.continuousAt_iff.mp
    (hheat.continuousAt (x := 0)) (eps / 4) (by positivity)
  let r0 := eps / 4
  let T0 := min Tcap (min 1 (min (eps / 2) (delta / 2)))
  have hT0 : 0 < T0 := by dsimp [T0]; positivity
  have hT01 : T0 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hT0eps : T0 ≤ eps / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hT0delta : T0 ≤ delta / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r0, by dsimp [r0]; positivity, T0, hT0, min_le_left _ _, hT01, ?_⟩
  intro T hT hTT0 F hF t x
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have htT0 : (t : ℝ) ≤ T0 := t.property.2.trans hTT0
  have htdelta : dist (t : ℝ) 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    linarith only [htT0, hT0delta, hdelta]
  have hheatBound : ‖heat lambda (t : ℝ).toNNReal w - w‖ < eps / 4 := by
    have h := hheatNear htdelta
    simpa only [Real.toNNReal_zero, heat_zero, ContinuousLinearMap.id_apply,
      dist_eq_norm] using h
  have hsqrt : Real.sqrt T ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (hTT0.trans hT01)
  have htrace : ‖initialResponseTrace lambda w hT F t - heat lambda (t : ℝ).toNNReal w‖ <
      r0 := by
    apply ((initialResponseTrace_spec lambda w hT F).2.2.1 t).trans_lt
    have hb : (Real.sqrt T + 1) * ‖F‖ ≤ 2 * ‖F‖ := by
      gcongr
      linarith only [hsqrt]
    exact hb.trans_lt (by linarith only [hF])
  have hstate : dist (initialResponseTrace lambda w hT F t) w < eps := by
    calc
      _ ≤ dist (initialResponseTrace lambda w hT F t) (heat lambda (t : ℝ).toNNReal w) +
          dist (heat lambda (t : ℝ).toNNReal w) w := dist_triangle _ _ _
      _ < r0 + eps / 4 := add_lt_add
        (by simpa only [dist_eq_norm] using htrace)
        (by simpa only [dist_eq_norm] using hheatBound)
      _ < eps := by dsimp only [r0]; linarith only [heps]
  have htime : dist (t : ℝ) 0 < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    linarith only [htT0, hT0eps, heps]
  have hpair : dist ((t : ℝ), initialResponseTrace lambda w hT F t) (0, w) < eps := by
    rw [Prod.dist_eq]
    exact max_lt htime hstate
  have hmaps : MapsTo (H ((t : ℝ), initialResponseTrace lambda w hT F t)) univ O := hnear hpair
  exact hmaps (mem_univ x)

end PoincareConjecture.M63
