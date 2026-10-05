import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The positive backward square clock on spacetime

The inverse time coordinate is the actual sqrt(T-time) and is smooth
where time is strictly before T. Relative physical square-time
neighborhoods pull back to open spacetime neighborhoods. This retains
included physical endpoints in Proposition 6.28, p. 117.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} (G : GeneralizedLGeometryTransport n X time I) (T : ℝ)

/-- The actual inverse of the positive backward square-time clock,
Proposition 6.28, p. 117. Values at or after T are only totalizations. -/
noncomputable def backwardSquareClock (q : G.Point) : ℝ :=
  Real.sqrt (T - G.spacetime.timeFunction q)

/-- The actual backward square clock is continuous everywhere,
Proposition 6.28, p. 117. -/
theorem backwardSquareClock_continuous : Continuous (backwardSquareClock G T) := by
  have ht : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  exact Real.continuous_sqrt.comp (continuous_const.sub ht.continuous)

/-- The actual backward square clock is smooth strictly before T,
including included physical boundary points, Proposition 6.28, p. 117. -/
theorem backwardSquareClock_contMDiffOn :
    ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ (backwardSquareClock G T)
      {q | G.spacetime.timeFunction q < T} := by
  intro q hq
  have ht : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  exact ((Real.contDiffAt_sqrt (ne_of_gt (sub_pos.mpr hq))).contMDiffAt.comp q
    ((contMDiff_const.sub ht).contMDiffAt)).contMDiffWithinAt

/-- Before T, the inverse square clock is physically admissible and
recovers the actual spacetime time, Proposition 6.28, p. 117. -/
theorem backwardSquareClock_admissible {q : G.Point}
    (hq : G.spacetime.timeFunction q ≤ T) :
    0 ≤ backwardSquareClock G T q ∧
      T - backwardSquareClock G T q ^ 2 = G.spacetime.timeFunction q ∧
      T - backwardSquareClock G T q ^ 2 ∈ I.domain := by
  have heq : T - backwardSquareClock G T q ^ 2 = G.spacetime.timeFunction q := by
    rw [backwardSquareClock, Real.sq_sqrt (sub_nonneg.mpr hq), sub_sub_cancel]
  refine ⟨Real.sqrt_nonneg _, heq, ?_⟩
  rw [heq, ← G.spacetime.time_range]
  exact ⟨q, rfl⟩

/-- The selected exponential clock is inverted exactly on its actual
survival domain, Proposition 6.28, p. 117. -/
theorem backwardSquareClock_exponential {x : G.Point}
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) : backwardSquareClock G T (E.gamma Z s) = s := by
  rw [backwardSquareClock, E.clock Z s hs, sub_sub_cancel,
    Real.sqrt_sq (E.domain_admissible hs).1]

/-- A relative neighborhood of a positive physical square time
contains all inverse clocks on an open spacetime neighborhood of
the endpoint, Proposition 6.28, p. 117. -/
theorem exists_backwardSquareClock_neighborhood {x : G.Point}
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) {C : Set ℝ}
    (hC : C ∈ 𝓝[{r | 0 ≤ r ∧ T - r ^ 2 ∈ I.domain}] s) :
    ∃ O : Set G.Point, IsOpen O ∧ E.gamma Z s ∈ O ∧
      ∀ q ∈ O, G.spacetime.timeFunction q < T ∧ backwardSquareClock G T q ∈ C := by
  have htime : G.spacetime.timeFunction (E.gamma Z s) < T := by
    rw [E.clock Z s hs]
    exact sub_lt_self T (sq_pos_of_pos hpos)
  have htimesm : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have hn : {q : G.Point | G.spacetime.timeFunction q < T} ∈ 𝓝 (E.gamma Z s) :=
    (isOpen_lt htimesm.continuous continuous_const).mem_nhds htime
  have hadm : ∀ᶠ q in 𝓝 (E.gamma Z s),
      backwardSquareClock G T q ∈ {r | 0 ≤ r ∧ T - r ^ 2 ∈ I.domain} := by
    filter_upwards [hn] with q hq
    exact ⟨(backwardSquareClock_admissible G T hq.le).1,
      (backwardSquareClock_admissible G T hq.le).2.2⟩
  have ht : Tendsto (backwardSquareClock G T) (𝓝 (E.gamma Z s))
      (𝓝[{r | 0 ≤ r ∧ T - r ^ 2 ∈ I.domain}] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hadm⟩
    have hcont : Tendsto (backwardSquareClock G T) (𝓝 (E.gamma Z s))
        (𝓝 (backwardSquareClock G T (E.gamma Z s))) :=
      (backwardSquareClock_continuous G T).continuousAt
    rwa [backwardSquareClock_exponential G T E hs] at hcont
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp (inter_mem hn (ht hC))
  exact ⟨O, hO, hpO, fun _ hq => hOsub hq⟩

end PoincareMT.M14
