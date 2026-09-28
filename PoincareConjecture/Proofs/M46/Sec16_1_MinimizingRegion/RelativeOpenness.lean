import PoincareConjecture.Proofs.M46.Sec16_1_MinimizingRegion.MovingEndpoint
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.ConfinedAttainment
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_InteriorSurvival

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}

def confinementRegion (C : ActionConfinement G T start x) : Set G.Point :=
  {y | G.spacetime.timeFunction y ∈ Ico start T ∧
    ∃ p : M14BackwardPath G T 0 (T - G.spacetime.timeFunction y) x y,
      M14BackwardLAction G p < C.barrier}

theorem confinementRegion_local
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G) (E : M14ExponentialFamily G T x)
    (C : ActionConfinement G T start x) (hstrip : Icc start T ⊆ I.domain)
    {y : G.Point} (hy : y ∈ confinementRegion C) :
    ∃ V : Set G.Point, IsOpen V ∧ y ∈ V ∧
      V ∩ G.spacetime.timeFunction ⁻¹' Ico start T ⊆ confinementRegion C := by
  obtain ⟨hyt, p0, hp0⟩ := hy
  have htau : 0 < T - G.spacetime.timeFunction y := sub_pos.mpr hyt.2
  obtain ⟨p, hp⟩ := actionConfinement_attained hM12 C htau
    (sub_le_sub_left hyt.1 T) p0 hp0
  have hpB : M14BackwardLAction G p < C.barrier := (hp p0).trans_lt hp0
  obtain ⟨Z, hZ, htrace, _⟩ := minimizing_exponential_branch LG E p hp
  have hs : 0 < Real.sqrt (T - G.spacetime.timeFunction y) := Real.sqrt_pos.mpr htau
  obtain ⟨b, hsb, hZb, hbchoice⟩ : ∃ b : ℝ,
      Real.sqrt (T - G.spacetime.timeFunction y) ≤ b ∧ (Z, b) ∈ E.domain ∧
      (G.spacetime.timeFunction y = start ∨ Real.sqrt (T - G.spacetime.timeFunction y) < b) := by
    by_cases ht : G.spacetime.timeFunction y = start
    · exact ⟨_, le_rfl, hZ, Or.inl ht⟩
    · have hstart : start < G.spacetime.timeFunction y := lt_of_le_of_ne hyt.1 (Ne.symm ht)
      have hinterior : G.spacetime.timeFunction y ∈ interior I.domain := by
        apply mem_interior_iff_mem_nhds.mpr
        apply mem_of_superset (Ioo_mem_nhds hstart hyt.2)
        exact fun _ hz => hstrip (Ioo_subset_Icc_self hz)
      obtain ⟨b, hsb, hZb⟩ := exists_surviving_extension_at_interior E hs hZ
        (by simpa only [Real.sq_sqrt htau.le, sub_sub_cancel] using hinterior)
      exact ⟨b, hsb.le, hZb, Or.inr hsb⟩
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hgamma : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ (E.gamma Z) (Icc 0 b) :=
    E.family_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun s hs' => (E.maximal_lifetime Z).out (E.domain_zero Z) hZb hs')
  have hclock (s : ℝ) (hs' : s ∈ Icc 0 b) :
      G.spacetime.timeFunction (E.gamma Z s) = T - s ^ 2 :=
    E.clock Z s ((E.maximal_lifetime Z).out (E.domain_zero Z) hZb hs')
  obtain ⟨V, hV, hyV, hrecover⟩ := moving_endpoint_recovery hM12 p hpB (E.gamma Z)
    hsb hgamma hclock (E.gamma_at_zero Z) htrace
  rcases hbchoice with hboundary | hstrict
  · refine ⟨V, hV, hyV, ?_⟩
    intro z hz
    refine ⟨hz.2, hrecover z hz.1 (sub_pos.mpr hz.2.2) ?_⟩
    apply (Real.sqrt_le_sqrt ?_).trans hsb
    exact sub_le_sub_left (hboundary.symm ▸ hz.2.1) T
  · let W : Set G.Point := {z | Real.sqrt (T - G.spacetime.timeFunction z) < b}
    have hW : IsOpen W := isOpen_Iio.preimage
      (Real.continuous_sqrt.comp (continuous_const.sub
        (show ContMDiff (spacetimeModel 3) (𝓘(ℝ, ℝ)) ∞
          (fun z : G.Point => G.spacetime.timeFunction z) from
            G.spacetime.time_smooth).continuous))
    refine ⟨V ∩ W, hV.inter hW, ⟨hyV, hstrict⟩, ?_⟩
    intro z hz
    exact ⟨hz.2, hrecover z hz.1.1 (sub_pos.mpr hz.2.2) hz.1.2.le⟩

theorem confinementRegion_relatively_open
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G) (E : M14ExponentialFamily G T x)
    (C : ActionConfinement G T start x) (hstrip : Icc start T ⊆ I.domain) :
    ∃ U : Set G.Point, IsOpen U ∧
      confinementRegion C = U ∩ G.spacetime.timeFunction ⁻¹' Ico start T := by
  classical
  choose V hV hyV hsub using fun y : confinementRegion C =>
    confinementRegion_local hM12 LG E C hstrip y.property
  refine ⟨⋃ y : confinementRegion C, V y, isOpen_iUnion hV, ?_⟩
  ext z
  constructor
  · intro hz
    exact ⟨mem_iUnion.mpr ⟨⟨z, hz⟩, hyV ⟨z, hz⟩⟩, hz.1⟩
  · rintro ⟨hzU, hzt⟩
    obtain ⟨y, hy⟩ := mem_iUnion.mp hzU
    exact hsub y ⟨hy, hzt⟩

end PoincareConjecture.Proofs.M46
