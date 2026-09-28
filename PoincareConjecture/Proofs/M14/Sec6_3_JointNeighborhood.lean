import PoincareConjecture.Proofs.M14.Sec6_3_JointDomain
import PoincareConjecture.Proofs.M14.Sec6_3_SquareClockWindows
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Proofs.M14.Mathlib.ClosedFamilyNeighborhood

set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M14

theorem relativeInterior_mem_nhdsWithin {Y : Type*} [TopologicalSpace Y]
    {A S : Set Y} {z : Y} (hz : z ∈ M14RelativeInterior A S) :
    M14RelativeInterior A S ∈ 𝓝[A] z := by
  obtain ⟨_, U, hU, hzU, hsub⟩ := hz
  apply mem_nhdsWithin.mpr
  refine ⟨U, hU, hzU, ?_⟩
  intro w hw
  exact ⟨hsub hw, U, hU, hw.1, hsub⟩

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem jointDomain_time_pos (E : M14ExponentialFamily G T x)
    {z : G.Horizontal x × ℝ} (hz : z ∈ M14JointDomain G E) : 0 < z.2 := by
  obtain ⟨τ, _, hτ, _, ht⟩ := hz.1
  rw [ht]
  exact Real.sqrt_pos.mpr hτ

theorem exists_jointDomain_gauge_tube (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hz : (Z, s) ∈ M14JointDomain G E) :
    ∃ (b : G.gaugeCover.index) (N : Set G.Point)
      (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b),
      IsOpen N ∧ E.gamma Z s ∈ N ∧
      ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift N ∧
      (∀ q ∈ N, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q) ∧
      (∀ q ∈ N, (lift q).1.val = G.spacetime.timeFunction q) ∧
      ∃ V : Set (G.Horizontal x), IsOpen V ∧ Convex ℝ V ∧ Z ∈ V ∧
        ∃ a c : ℝ, 0 < a ∧ a < s ∧ s ≤ c ∧
          V ×ˢ Icc a c ⊆ M14JointDomain G E ∧
          (∀ z ∈ V ×ˢ Icc a c, E.gamma z.1 z.2 ∈ N) ∧
          V ×ˢ Icc a c ∈ 𝓝[M14AdmissibleParameter G T x] (Z, s) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  have hs : 0 < s := jointDomain_time_pos E hz
  have hsurv := jointDomain_subset_domain E hz
  have hAdm := E.domain_admissible hsurv
  have hT : T ∈ I.domain := by
    rw [← G.spacetime.time_range]
    exact ⟨x, E.base_time⟩
  obtain ⟨d, hsd, hclock, hnear⟩ := exists_squareClock_prefix_neighborhood hT hs hAdm.2
  let A := M14AdmissibleParameter G T x
  let B := (univ : Set (G.Horizontal x)) ×ˢ Icc 0 d
  have hBA : B ⊆ A := fun z hz => ⟨hz.2.1, hclock z.2 hz.2⟩
  have hJn : M14JointDomain G E ∈ 𝓝[A] (Z, s) := relativeInterior_mem_nhdsWithin hz
  have hDn : E.domain ∈ 𝓝[A] (Z, s) := mem_of_superset hJn (jointDomain_subset_domain E)
  obtain ⟨b, N, lift, hN, hpN, hlift, hrec, htime⟩ := exists_smooth_gauge_lift G (E.gamma Z s)
  have hpre : {z : G.Horizontal x × ℝ | E.gamma z.1 z.2 ∈ N} ∈ 𝓝[A] (Z, s) :=
    nhdsWithin_le_of_mem hDn
      ((E.joint_continuous (Z, s) hsurv).preimage_mem_nhdsWithin (hN.mem_nhds hpN))
  have hsmall : M14JointDomain G E ∩ {z | E.gamma z.1 z.2 ∈ N} ∈ 𝓝[B] (Z, s) :=
    nhdsWithin_mono (Z, s) hBA (inter_mem hJn hpre)
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

end PoincareConjecture.M14
