import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StableInjectivity
import Mathlib.Tactic.Linarith

/-!
# The joint stable graph and its endpoint map

Morgan-Tian Proposition 6.28, p. 117. The clock separates different times;
fixed-time stable injectivity separates initial vectors. Continuity and the
clock equation then restrict to the frozen relative-interior joint domain.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- Stable graph points lie in the selected exponential's survival domain,
Morgan-Tian Definitions 6.17 and 6.25, pp. 113, 116. -/
theorem stableGraph_subset_domain (E : M14ExponentialFamily G T x) :
    M14StableGraph G E ⊆ E.domain := by
  rintro z ⟨τ, H, _, hZ, hs⟩
  change (z.1, z.2) ∈ E.domain
  rw [hs]
  exact H.survivor z.1 hZ

/-- The joint relative-interior domain retains survival of the same branch,
Morgan-Tian Proposition 6.28, p. 117. -/
theorem jointDomain_subset_domain (E : M14ExponentialFamily G T x) :
    M14JointDomain G E ⊆ E.domain :=
  fun _ hz => stableGraph_subset_domain E hz.1

/-- The actual endpoint map is injective on the entire stable graph,
Morgan-Tian Proposition 6.28, p. 117. -/
theorem stableGraph_endpoint_injective (E : M14ExponentialFamily G T x) :
    Set.InjOn (fun z : G.Horizontal x × ℝ => E.gamma z.1 z.2)
      (M14StableGraph G E) := by
  intro z hz w hw heq
  have hclock := congrArg G.spacetime.timeFunction heq
  rw [E.clock z.1 z.2 (stableGraph_subset_domain E hz),
    E.clock w.1 w.2 (stableGraph_subset_domain E hw)] at hclock
  obtain ⟨τ, H, hτ, hZ, hs⟩ := hz
  obtain ⟨σ, K, hσ, hW, ht⟩ := hw
  rw [hs, ht, Real.sq_sqrt hτ.le, Real.sq_sqrt hσ.le] at hclock
  have htime : τ = σ := by linarith only [hclock]
  subst σ
  have hWH : w.1 ∈ H.carrier :=
    (H.carrier_exact w.1).mpr ((K.carrier_exact w.1).mp hW)
  have hv : z.1 = w.1 := stable_endpoint_injective H hZ hWH (by
    calc
      H.endpoint_map z.1 = E.gamma z.1 (Real.sqrt τ) := H.endpoint_map_eq z.1 hZ
      _ = E.gamma z.1 z.2 := congrArg (E.gamma z.1) hs.symm
      _ = E.gamma w.1 w.2 := heq
      _ = E.gamma w.1 (Real.sqrt τ) := congrArg (E.gamma w.1) ht
      _ = H.endpoint_map w.1 := (H.endpoint_map_eq w.1 hWH).symm)
  exact Prod.ext hv (hs.trans ht.symm)

/-- The endpoint map on the joint domain is injective,
Morgan-Tian Proposition 6.28, p. 117. -/
theorem jointMap_injective (E : M14ExponentialFamily G T x) :
    Function.Injective (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) := by
  intro z w heq
  exact Subtype.ext (stableGraph_endpoint_injective E z.2.1 w.2.1 heq)

/-- Restrict the selected family's joint continuity to its stable joint domain,
Morgan-Tian Proposition 6.28, p. 117. -/
theorem jointMap_continuous (E : M14ExponentialFamily G T x) :
    Continuous (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) :=
  (E.joint_continuous.mono (jointDomain_subset_domain E)).domRestrict

/-- The joint map has the actual backward clock of its selected branches,
Morgan-Tian Definition 6.17 and Proposition 6.28, pp. 113, 117. -/
theorem jointMap_clock (E : M14ExponentialFamily G T x) (z : M14JointDomain G E) :
    G.spacetime.timeFunction (E.gamma z.1.1 z.1.2) = T - z.1.2 ^ 2 :=
  E.clock z.1.1 z.1.2 (jointDomain_subset_domain E z.2)

end PoincareMT.M14
