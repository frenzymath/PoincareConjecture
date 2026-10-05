import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StrictPrefix

/-!
# Full stable carriers at earlier positive times

The actual time range supplies a slice point even when the stable
carrier is empty. Strict-prefix stability and the retained minimizing
path then give backward carrier inclusion and the exact endpoint
clause. Morgan-Tian Proposition 6.30, pp. 118-119, and the backward
star argument in Proposition 6.81, pp. 145-146.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ σ : ℝ} {x : G.Point}

/-- Every allowed positive slice has its full stable-set record,
including an empty stable carrier, Proposition 6.28, p. 117. -/
theorem stableSet_nonempty_of_allowed (E : M14ExponentialFamily G T x)
    (hτ : 0 < τ) (hallowed : T - τ ∈ I.domain) :
    Nonempty (M14StableSet G T τ x E) := by
  have hrange : range G.spacetime.timeFunction = I.domain := G.spacetime.time_range
  obtain ⟨q, hq⟩ := hrange.symm ▸ hallowed
  exact ⟨stableSetOfSlicePoint E hτ ⟨q, hq⟩⟩

/-- A full terminal stable record makes every intermediate time
allowed, even without a member of its carrier, Proposition 6.81,
pp. 145-146. -/
theorem stableSet_past_allowed (E : M14ExponentialFamily G T x)
    (H : M14StableSet G T τ x E) : Icc (T - τ) T ⊆ I.domain := by
  have hrange : range G.spacetime.timeFunction = I.domain := G.spacetime.time_range
  have hleft : T - τ ∈ I.domain := hrange ▸
    (show T - τ ∈ range G.spacetime.timeFunction from
      ⟨(H.endpoint_slice_map 0).val, (H.endpoint_slice_map 0).property⟩)
  have hright : T ∈ I.domain := hrange ▸
    (show T ∈ range G.spacetime.timeFunction from ⟨x, E.base_time⟩)
  exact I.ordConnected.out hleft hright

/-- Every earlier full stable carrier contains the later one,
Proposition 6.30, pp. 118-119. -/
theorem stableSet_carrier_mono_backward
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
    (Hσ : M14StableSet G T σ x E) (hle : σ ≤ τ) :
    H.carrier ⊆ Hσ.carrier := by
  intro Z hZ
  apply (Hσ.carrier_exact Z).mpr
  rcases hle.eq_or_lt with heq | hlt
  · subst σ
    exact (H.carrier_exact Z).mp hZ
  · exact stableInitialVector_prefix hCoordinates hM04 hM12 E Hσ.tau_pos hlt
      ((H.carrier_exact Z).mp hZ)

/-- A full stable carrier exists at every earlier positive time and
contains the supplied terminal carrier, Proposition 6.81, pp. 145-146. -/
theorem exists_stableSet_backward
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
    (hσ : 0 < σ) (hle : σ ≤ τ) :
    ∃ Hσ : M14StableSet G T σ x E, H.carrier ⊆ Hσ.carrier := by
  obtain ⟨Hσ⟩ := stableSet_nonempty_of_allowed E hσ
    (stableSet_past_allowed E H ⟨sub_le_sub_left hle T, sub_le_self T hσ.le⟩)
  exact ⟨Hσ, stableSet_carrier_mono_backward hCoordinates hM04 hM12 E H Hσ hle⟩

/-- One actual minimizing path realizes every earlier stable endpoint,
the backward-star clause used in Proposition 6.81, pp. 145-146. -/
theorem stableSet_backward_star
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T τ x E)
    {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) :
    ∃ p : M14BackwardPath G T 0 τ x (H.endpoint_map Z), M14IsMinimizing p ∧
      ∀ σ ∈ Ioc 0 τ, ∃ Hσ : M14StableSet G T σ x E,
        Z ∈ Hσ.carrier ∧ p.curve σ = Hσ.endpoint_map Z := by
  obtain ⟨p, hcurve, hmin, _⟩ := H.minimizing_path Z hZ
  refine ⟨p, hmin, ?_⟩
  intro σ hσ
  obtain ⟨Hσ, hsub⟩ := exists_stableSet_backward hCoordinates hM04 hM12 E H hσ.1 hσ.2
  exact ⟨Hσ, hsub hZ, (hcurve ⟨hσ.1.le, hσ.2⟩).trans (Hσ.endpoint_map_eq Z (hsub hZ)).symm⟩

end PoincareMT.M14
