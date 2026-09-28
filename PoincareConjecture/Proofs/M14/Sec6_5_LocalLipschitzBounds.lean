import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzAction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x q0 : G.Point}

theorem exists_survivor_action_neighborhood (E : M14ExponentialFamily G T x)
    {N O : Set G.Point} (hN : IsOpen N) (hqN : q0 ∈ N)
    (hO : IsOpen O) (hqO : q0 ∈ O) (hqtime : 0 < T - G.spacetime.timeFunction q0)
    {inv : G.Point → G.Horizontal x × ℝ}
    (ha : ContinuousOn (fun q => E.action (inv q).1 (inv q).2) O)
    (hmap : ∀ q ∈ O, inv q ∈ E.domain ∧ 0 < (inv q).2)
    (hright : ∀ q ∈ O, E.gamma (inv q).1 (inv q).2 = q) :
    ∃ U : Set G.Point, IsOpen U ∧ q0 ∈ U ∧ U ⊆ N ∧ U ⊆ O ∧
      ∃ δ H D : ℝ, 0 < δ ∧ 0 ≤ D ∧
        (∀ q ∈ U, δ ≤ Real.sqrt (T - G.spacetime.timeFunction q) ∧
          Real.sqrt (T - G.spacetime.timeFunction q) ≤ H) ∧
        ∀ q ∈ U, ∀ p : M14BackwardPath G T 0 (T - G.spacetime.timeFunction q) x q,
          M14IsMinimizing p → M14BackwardLAction G p ≤ D := by
  let s0 := Real.sqrt (T - G.spacetime.timeFunction q0)
  let D := |E.action (inv q0).1 (inv q0).2| + 1
  have hs0 : 0 < s0 := Real.sqrt_pos.mpr hqtime
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have ht : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have hc : Continuous (fun q : G.Point => Real.sqrt (T - G.spacetime.timeFunction q)) :=
    Real.continuous_sqrt.comp (continuous_const.sub ht.continuous)
  let B := (N ∩ O) ∩ {q | s0 / 2 < Real.sqrt (T - G.spacetime.timeFunction q) ∧
    Real.sqrt (T - G.spacetime.timeFunction q) < s0 + 1}
  have hB : IsOpen B := (hN.inter hO).inter
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))
  have hqB : q0 ∈ B := ⟨⟨hqN, hqO⟩, by
    change s0 / 2 < s0 ∧ s0 < s0 + 1
    constructor <;> linarith⟩
  let U := B ∩ (fun q => E.action (inv q).1 (inv q).2) ⁻¹' Iio D
  have hU : IsOpen U := (ha.mono (fun _ hq => hq.1.2)).isOpen_inter_preimage hB isOpen_Iio
  have hqU : q0 ∈ U := by
    refine ⟨hqB, ?_⟩
    change E.action (inv q0).1 (inv q0).2 < |E.action (inv q0).1 (inv q0).2| + 1
    linarith [le_abs_self (E.action (inv q0).1 (inv q0).2)]
  refine ⟨U, hU, hqU, fun _ hq => hq.1.1.1, fun _ hq => hq.1.1.2,
    s0 / 2, s0 + 1, D, half_pos hs0, hD, fun _ hq => ⟨hq.1.2.1.le, hq.1.2.2.le⟩, ?_⟩
  intro q hq p hp
  exact (minimizing_action_le_exponentialAction E p hp (hmap q hq.1.1.2).1
    (hmap q hq.1.1.2).2 (hright q hq.1.1.2)).trans hq.2.le

end PoincareConjecture.M14
