import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Domain.JointNeighborhood

/-!
# Actual survivor tubes without future minimizing stability

Relative openness of the supplied exponential domain gives a closed
time tube inside a compatible gauge. This requires survival and positive
time only; no membership in the joint stable domain is assumed.
Morgan-Tian Proposition 6.28, p. 117, used in the local argument for
Proposition 6.56, p. 133.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- A positive survivor has a convex spatial, closed-time tube in the
actual survivor domain and one smooth gauge inverse. The tube remains
a relative neighborhood at a physical endpoint, Proposition 6.28,
p. 117. -/
theorem exists_survivor_gauge_tube (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hsurv : (Z, s) ∈ E.domain) (hs : 0 < s) :
    ∃ (b : G.gaugeCover.index) (N : Set G.Point)
      (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b),
      IsOpen N ∧ E.gamma Z s ∈ N ∧
      ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift N ∧
      (∀ q ∈ N, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q) ∧
      (∀ q ∈ N, (lift q).1.val = G.spacetime.timeFunction q) ∧
      ∃ V : Set (G.Horizontal x), IsOpen V ∧ Convex ℝ V ∧ Z ∈ V ∧
        ∃ a c : ℝ, 0 < a ∧ a < s ∧ s ≤ c ∧
          V ×ˢ Icc a c ⊆ E.domain ∧
          (∀ z ∈ V ×ˢ Icc a c, E.gamma z.1 z.2 ∈ N) ∧
          V ×ˢ Icc a c ∈ 𝓝[M14AdmissibleParameter G T x] (Z, s) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  have hAdm := E.domain_admissible hsurv
  have hT : T ∈ I.domain := by
    rw [← G.spacetime.time_range]
    exact ⟨x, E.base_time⟩
  obtain ⟨d, hsd, hclock, hnear⟩ := exists_squareClock_prefix_neighborhood hT hs hAdm.2
  let A := M14AdmissibleParameter G T x
  let B := (univ : Set (G.Horizontal x)) ×ˢ Icc 0 d
  have hBA : B ⊆ A := fun z hz => ⟨hz.2.1, hclock z.2 hz.2⟩
  have hDn : E.domain ∈ 𝓝[A] (Z, s) := by
    obtain ⟨U, hU, hzU, hsub⟩ := E.domain_relative_open (Z, s) hsurv
    exact mem_nhdsWithin.mpr ⟨U, hU, hzU, hsub⟩
  obtain ⟨b, N, lift, hN, hpN, hlift, hrec, htime⟩ := exists_smooth_gauge_lift G (E.gamma Z s)
  have hpre : {z : G.Horizontal x × ℝ | E.gamma z.1 z.2 ∈ N} ∈ 𝓝[A] (Z, s) :=
    nhdsWithin_le_of_mem hDn
      ((E.joint_continuous (Z, s) hsurv).preimage_mem_nhdsWithin (hN.mem_nhds hpN))
  have hsmall : E.domain ∩ {z | E.gamma z.1 z.2 ∈ N} ∈ 𝓝[B] (Z, s) :=
    nhdsWithin_mono (Z, s) hBA (inter_mem hDn hpre)
  obtain ⟨U, hU, hZU, _, a, c, ha, has, hsc, _, hsub, hCn⟩ :=
    exists_open_closed_family_neighborhood isOpen_univ (mem_univ Z) hs hsd hsmall
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hZU)
  let V := ball Z ε
  have hVU : V ⊆ U := hεU
  have hVZ : Z ∈ V := mem_ball_self hε
  refine ⟨b, N, lift, hN, hpN, hlift, hrec, htime, V, isOpen_ball, convex_ball Z ε,
    hVZ, a, c, ha, has, hsc, ?_, ?_, ?_⟩
  · exact fun z hz => (hsub ⟨hVU hz.1, hz.2⟩).1
  · exact fun z hz => (hsub ⟨hVU hz.1, hz.2⟩).2
  · have hprod : A = (univ : Set (G.Horizontal x)) ×ˢ
        {r | 0 ≤ r ∧ T - r ^ 2 ∈ I.domain} := by
      ext z
      simp only [A, M14AdmissibleParameter, mem_ofPred_eq, mem_prod, mem_univ, true_and]
    change V ×ˢ Icc a c ∈ 𝓝[A] (Z, s)
    rw [hprod, nhdsWithin_prod_eq, nhdsWithin_univ]
    exact prod_mem_prod (isOpen_ball.mem_nhds hVZ) (nhdsWithin_le_of_mem hnear hCn)

end PoincareMT.M14
