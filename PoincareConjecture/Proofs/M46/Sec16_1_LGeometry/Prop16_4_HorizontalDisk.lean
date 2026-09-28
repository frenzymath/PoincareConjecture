import PoincareConjecture.Definitions.M14GeneralizedLGeometry
import Mathlib.Topology.Compactness.LocallyCompact










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} (G : GeneralizedLGeometryTransport n X time I)





theorem isCompact_horizontalDisk {K : Set G.Point} (hK : IsCompact K) (R : ℝ) :
    IsCompact {z : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal |
      z.proj ∈ K ∧ G.spacetime.horizontalMetric.inner z.proj z.2 z.2 ≤ R} := by
  classical
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : ∀ x, NormedAddCommGroup (G.Horizontal x) := fun x =>
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : ∀ x, InnerProductSpace ℝ (G.Horizontal x) := fun x =>
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : RiemannianBundle G.Horizontal := ⟨metric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n)) G.Horizontal :=
    ⟨⟨G.spacetime.horizontalMetric.inner,
      G.spacetime.horizontalMetric.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  let : LocallyCompactSpace (EuclideanHalfSpace 1) := by
    change LocallyCompactSpace {v : EuclideanSpace ℝ (Fin 1) // 0 ≤ v 0}
    have hc : Continuous (fun v : EuclideanSpace ℝ (Fin 1) => v 0) := by fun_prop
    exact (isClosed_le continuous_const hc).locallyCompactSpace
  let : LocallyCompactSpace
      (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) :=
    inferInstanceAs (LocallyCompactSpace
      (EuclideanHalfSpace 1 × EuclideanSpace ℝ (Fin n)))
  let : LocallyCompactSpace G.Point := ChartedSpace.locallyCompactSpace
    (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) G.Point
  let e := fun x : G.Point => trivializationAt (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  have hlocal (x : G.Point) : ∃ B : ℝ, 0 < B ∧ ∃ L : Set G.Point,
      IsCompact L ∧ x ∈ interior L ∧
      ∀ y ∈ L, y ∈ (e x).baseSet ∧ ‖(e x).continuousLinearMapAt ℝ y‖ < B := by
    obtain ⟨B, hB, hnorm⟩ := eventually_norm_trivializationAt_lt
      (EuclideanSpace ℝ (Fin n)) G.Horizontal x
    have hb : (e x).baseSet ∈ 𝓝 x :=
      (e x).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp (Filter.inter_mem hb hnorm)
    obtain ⟨L, hLc, hxL, hLU⟩ := exists_compact_subset hUopen hxU
    exact ⟨B, hB, L, hLc, hxL, fun y hy => hUsub (hLU hy)⟩
  choose B hB L hLc hxL hL using hlocal
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover (fun x => interior (L x))
    (fun x _ => isOpen_interior.mem_nhds (hxL x))
  let C := fun x : G.Point => (e x).toOpenPartialHomeomorph.symm ''
    (L x ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (B x * Real.sqrt R))
  have hCc (x : G.Point) : IsCompact (C x) := by
    apply ((hLc x).prod (isCompact_closedBall _ _)).image_of_continuousOn
    apply (e x).toOpenPartialHomeomorph.continuousOn_symm.mono
    intro z hz
    exact (e x).mem_target.mpr (hL x z.1 hz.1).1
  have hclosed : IsClosed
      {z : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal |
        z.proj ∈ K ∧ G.spacetime.horizontalMetric.inner z.proj z.2 z.2 ≤ R} := by
    have hi : Continuous
        (fun z : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
          G.spacetime.horizontalMetric.inner z.proj z.2 z.2) :=
      Continuous.inner_bundle
        (b := fun z : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal => z.proj)
        (v := fun z => z.2) (w := fun z => z.2) continuous_id continuous_id
    exact (hK.isClosed.preimage (FiberBundle.continuous_proj _ _)).inter
      (isClosed_le hi continuous_const)
  apply (S.isCompact_biUnion (fun x _ => hCc x)).of_isClosed_subset hclosed
  intro z hz
  obtain ⟨x, hxS, hx⟩ := Set.mem_iUnion₂.mp (hcover hz.1)
  have hzL : z.proj ∈ L x := interior_subset hx
  have hzb : z.proj ∈ (e x).baseSet := (hL x z.proj hzL).1
  have hzs : z ∈ (e x).source := (e x).mem_source.mpr hzb
  have hnorm : ‖z.2‖ ≤ Real.sqrt R := by
    rw [norm_eq_sqrt_real_inner]
    exact Real.sqrt_le_sqrt hz.2
  have hcoord : ‖((e x) z).2‖ ≤ B x * Real.sqrt R := by
    rw [← (e x).continuousLinearMapAt_apply_of_mem ℝ hzb z.2]
    calc
      _ ≤ ‖(e x).continuousLinearMapAt ℝ z.proj‖ * ‖z.2‖ :=
        ((e x).continuousLinearMapAt ℝ z.proj).le_opNorm z.2
      _ ≤ B x * ‖z.2‖ :=
        mul_le_mul_of_nonneg_right (hL x z.proj hzL).2.le (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (hB x).le
  apply Set.mem_iUnion₂.mpr
  refine ⟨x, hxS, (e x) z, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa only [(e x).coe_fst hzs] using hzL
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hcoord
  · exact (e x).toOpenPartialHomeomorph.left_inv hzs

end PoincareConjecture.Proofs.M46
