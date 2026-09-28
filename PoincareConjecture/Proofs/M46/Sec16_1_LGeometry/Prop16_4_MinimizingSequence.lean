import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_4_RegularRegion
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeEnergy
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x y : G.Point}

theorem pathSquareKinetic_nonneg {a b : ℝ}
    (p : M14BackwardPath G T a b x y) (s : ℝ) : 0 ≤ M14.pathSquareKinetic p s := by
  let v := (2 * s) • p.horizontal_velocity (s ^ 2)
  change 0 ≤ G.spacetime.horizontalMetric.inner (p.curve (s ^ 2)) v v
  by_cases hv : v = 0
  · simp only [hv, map_zero, le_refl]
  · exact (G.spacetime.horizontalMetric.pos (p.curve (s ^ 2)) v hv).le

theorem exists_confined_minimizing_sequence
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (C : ActionConfinement G T start x) {tau : ℝ}
    (htau : 0 < tau) (htauStart : tau ≤ T - start)
    (p₀ : M14BackwardPath G T 0 tau x y)
    (hp₀ : M14BackwardLAction G p₀ < C.barrier) :
    M14FiniteValueDomain G T 0 tau x y ∧
      ∃ (p : ℕ → M14BackwardPath G T 0 tau x y) (D : ℝ), 0 ≤ D ∧
        (∀ k, M14BackwardLAction G (p k) < C.barrier ∧
          MapsTo (p k).curve (Icc 0 tau) C.cage) ∧
        Antitone (fun k => M14BackwardLAction G (p k)) ∧
        Tendsto (fun k => M14BackwardLAction G (p k)) atTop
          (𝓝 (M14ActionValue G T 0 tau x y)) ∧
        ∀ k, IntervalIntegrable (M14.pathSquareKinetic (p k)) volume 0 (Real.sqrt tau) ∧
          (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic (p k) s) ≤ D := by
  classical
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  obtain ⟨m, hm⟩ := (C.cage_compact.image H.scalar_smooth.continuous).bddBelow
  let R := max 0 (-m)
  have hR : 0 ≤ R := le_max_left _ _
  have hscalar (q : G.Point) (hq : q ∈ C.cage) :
      -R ≤ horizontalScalarCurvature G.leafwise q := by
    have hm' := hm (mem_image_of_mem (horizontalScalarCurvature G.leafwise) hq)
    have hmR : -m ≤ R := le_max_right _ _
    linarith
  have hkinetic (p : M14BackwardPath G T 0 tau x y)
      (hp : M14BackwardLAction G p < C.barrier) :
      (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic p s) ≤
        2 * M14BackwardLAction G p + 4 * tau * R * Real.sqrt tau := by
    have h := M14.squarePath_kinetic_energy_le_action p hM12 hR (fun s hs =>
      hscalar _ (C.paths_mem tau htau htauStart y p hp (M14.squarePath_parameter_mem p hs)))
    simpa only [Real.sqrt_zero, sub_zero] using h
  have hlower (p : M14BackwardPath G T 0 tau x y)
      (hp : M14BackwardLAction G p < C.barrier) :
      -(2 * tau * R * Real.sqrt tau) ≤ M14BackwardLAction G p := by
    have hn : 0 ≤ ∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic p s :=
      intervalIntegral.integral_nonneg (Real.sqrt_nonneg tau)
        (fun s _ => pathSquareKinetic_nonneg p s)
    linarith [hkinetic p hp]
  have hbounded : BddBelow (M14ActionSet G T 0 tau x y) := by
    refine ⟨min C.barrier (-(2 * tau * R * Real.sqrt tau)), ?_⟩
    rintro a ⟨p, rfl⟩
    by_cases hp : M14BackwardLAction G p < C.barrier
    · exact (min_le_right _ _).trans (hlower p hp)
    · exact (min_le_left _ _).trans (le_of_not_gt hp)
  have hnonempty : (M14ActionSet G T 0 tau x y).Nonempty :=
    ⟨M14BackwardLAction G p₀, p₀, rfl⟩
  refine ⟨⟨hnonempty, hbounded⟩, ?_⟩
  obtain ⟨a, ha, hlimit, hamem⟩ := exists_seq_tendsto_sInf hnonempty hbounded
  choose p hp using hamem
  have hlow : M14ActionValue G T 0 tau x y < C.barrier :=
    (csInf_le hbounded ⟨p₀, rfl⟩).trans_lt hp₀
  have hlimit' : Tendsto (fun k => M14BackwardLAction G (p k)) atTop
      (𝓝 (M14ActionValue G T 0 tau x y)) := by
    simpa only [hp, M14ActionValue] using hlimit
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlimit'.eventually (Iio_mem_nhds hlow))
  let q : ℕ → M14BackwardPath G T 0 tau x y := fun k => p (k + N)
  have hq (k : ℕ) : M14BackwardLAction G (q k) < C.barrier := hN _ (Nat.le_add_left _ _)
  let D := 2 * C.barrier + 4 * tau * R * Real.sqrt tau
  have hD : 0 ≤ D := by
    have hn : 0 ≤ ∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic (q 0) s :=
      intervalIntegral.integral_nonneg (Real.sqrt_nonneg tau)
        (fun s _ => pathSquareKinetic_nonneg (q 0) s)
    have hk := hkinetic (q 0) (hq 0)
    dsimp only [D]
    linarith [hq 0]
  refine ⟨q, D, hD, fun k =>
    ⟨hq k, C.paths_mem tau htau htauStart y (q k) (hq k)⟩, ?_, ?_, ?_⟩
  · intro j k hjk
    simpa only [q, hp] using ha (Nat.add_le_add_right hjk N)
  · exact hlimit'.comp (tendsto_add_atTop_nat N)
  · intro k
    refine ⟨?_, ?_⟩
    · have hk : IntervalIntegrable (M14.pathSquareKinetic (q k)) volume
          (Real.sqrt 0) (Real.sqrt tau) :=
        M14.squarePath_kinetic_intervalIntegrable (q k) hM12
      simpa only [Real.sqrt_zero] using hk
    · have h := hkinetic (q k) (hq k)
      dsimp only [D]
      linarith [hq k]

end PoincareConjecture.Proofs.M46
