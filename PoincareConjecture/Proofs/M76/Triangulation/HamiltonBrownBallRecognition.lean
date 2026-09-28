import PoincareConjecture.Proofs.M76.Triangulation.HamiltonBrownBoundaryChart
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem ball_pair_regular_interior {D S : Set V3}
    (hD : IsCompact D) (hfront : frontier D = S) (hp : IsUnitBallPair V3 D S) :
    IsConnected (interior D) ∧ closure (interior D) = D := by
  obtain ⟨_, e, heb⟩ := hp
  have hiff (x : D) : (x : V3) ∈ interior D ↔ (e x : V3) ∈ ball (0 : V3) 1 := by
    rw [← self_sdiff_frontier D, hfront, mem_ball_zero_iff]
    change ((x : V3) ∈ D ∧ (x : V3) ∉ S) ↔ ‖(e x : V3)‖ < 1
    have hle := mem_closedBall_zero_iff.mp (e x).property
    simp only [x.property, true_and]
    rw [heb x, mem_sphere_zero_iff_norm]
    exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
  let q : interior D ≃ₜ ball (0 : V3) 1 :=
    e.restrictSubsets interior_subset ball_subset_closedBall hiff
  have hconn : IsConnected (interior D) := by
    let : ConnectedSpace (ball (0 : V3) 1) := isConnected_iff_connectedSpace.mp
      ((convex_ball (0 : V3) 1).isConnected ⟨0, mem_ball_self zero_lt_one⟩)
    let : ConnectedSpace (interior D) := q.connectedSpace_iff.mpr inferInstance
    exact isConnected_iff_connectedSpace.mpr inferInstance
  let I : Set (closedBall (0 : V3) 1) := Subtype.val ⁻¹' ball (0 : V3) 1
  have hIimage : (Subtype.val : closedBall (0 : V3) 1 → V3) '' I = ball (0 : V3) 1 :=
    image_preimage_eq_of_subset (by
      intro x hx
      exact ⟨⟨x, ball_subset_closedBall hx⟩, rfl⟩)
  have hIclosure : closure I = univ := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hIimage,
      closure_ball (0 : V3) one_ne_zero]
    ext x
    simp only [mem_preimage, x.property, mem_univ]
  let g : closedBall (0 : V3) 1 → V3 := fun y => e.symm y
  have hg : Continuous g := continuous_subtype_val.comp e.symm.continuous
  have hgI : g '' I = interior D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : V3) ∈ ball (0 : V3) 1 := hy
      exact (hiff (e.symm y)).mpr (by simpa only [e.apply_symm_apply] using hy')
    · intro hx
      refine ⟨e ⟨x, interior_subset hx⟩, (hiff _).mp hx, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply _)
  refine ⟨hconn, Subset.antisymm (closure_minimal interior_subset hD.isClosed) ?_⟩
  intro x hx
  have him : x ∈ g '' closure I := by
    rw [hIclosure]
    exact ⟨e ⟨x, hx⟩, mem_univ _, congrArg Subtype.val (e.symm_apply_apply _)⟩
  rw [← hgI]
  exact image_closure_subset_closure_image hg him

private theorem fill_local_halfspace {D : Set V3} (hD : IsClosed D)
    (hreg : closure (interior D) = D) {x : V3} (hx : x ∈ frontier D)
    (B : OpenPartialHomeomorph V3 V3) (hxB : x ∈ B.source)
    (ell : V3 →ᴬ[ℝ] ℝ)
    (hfront : ∀ y ∈ B.source, y ∈ frontier D ↔ ell (B y) = 0)
    (hside : ∀ y ∈ interior D, y ∈ B.source → 0 < ell (B y)) :
    ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧ U ⊆ B.source ∧
      ∀ y ∈ U, 0 ≤ ell (B y) → y ∈ D := by
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.mp B.open_target (B x) (B.map_source hxB)
  let U := B.source ∩ B ⁻¹' ball (B x) r
  have hU : IsOpen U :=
    B.continuousOn_toFun.isOpen_inter_preimage B.open_source isOpen_ball
  have hxU : x ∈ U := ⟨hxB, mem_ball_self hr⟩
  have hxcl : x ∈ closure (interior D) := hreg.symm ▸ hD.frontier_subset hx
  obtain ⟨z, hzU, hzD⟩ := mem_closure_iff.mp hxcl U hU hxU
  let P := ball (B x) r ∩ {w | 0 < ell w}
  have hPcv : Convex ℝ P := (convex_ball _ _).inter
    ((convex_Ioi (0 : ℝ)).affine_preimage ell.toAffineMap)
  have hPtarget : P ⊆ B.target := inter_subset_left.trans hrB
  have himage : IsPreconnected (B.symm '' P) := hPcv.isPreconnected.image B.symm
    (B.continuousOn_invFun.mono hPtarget)
  have havoid : Disjoint (frontier (interior D)) (B.symm '' P) := by
    apply Set.disjoint_left.mpr
    rintro y hy ⟨w, hw, rfl⟩
    have hzero := (hfront _ (B.map_target (hPtarget hw))).mp
      (frontier_interior_subset hy)
    rw [B.right_inv (hPtarget hw)] at hzero
    exact (ne_of_gt hw.2) hzero
  have hmeet : ((B.symm '' P) ∩ interior D).Nonempty := by
    refine ⟨z, ⟨B z, ⟨hzU.2, hside z hzD hzU.1⟩, B.left_inv hzU.1⟩, hzD⟩
  have hsub := himage.m76_subset_of_disjoint_frontier isOpen_interior havoid hmeet
  refine ⟨U, hU, hxU, inter_subset_left, ?_⟩
  intro y hy hle
  rcases lt_or_eq_of_le hle with hpos | hzero
  · exact interior_subset (hsub ⟨B y, ⟨hy.2, hpos⟩, B.left_inv hy.1⟩)
  · exact hD.frontier_subset ((hfront y hy.1).mpr hzero.symm)

private theorem compact_domain_eq_brown_ball {K D : Set V3}
    (hK : IsCompact K) (hD : IsCompact D) (hfront : frontier D = frontier K)
    (hconn : IsConnected (interior D)) (hreg : closure (interior D) = D)
    (hhalf : ∀ x ∈ frontier K,
      ∃ B : OpenPartialHomeomorph V3 V3, x ∈ B.source ∧
        B x 0 = 0 ∧ ∀ y ∈ B.source, y ∈ K ↔ 0 ≤ B y 0) : D = K := by
  let ell : V3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj (0 : Fin 3)).toContinuousAffineMap
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro hz
    have h : ell.toAffineMap.linear (fun _ => 1) = 1 := rfl
    rw [hz] at h
    norm_num at h
  have havoid : Disjoint (frontier (interior K)) (interior D) := by
    apply Set.disjoint_left.mpr
    intro x hxK hxD
    have hx : x ∈ frontier D := hfront.symm ▸ frontier_interior_subset hxK
    exact hx.2 hxD
  rcases hconn.isPreconnected.subset_or_subset_compl_closure isOpen_interior havoid
      with hin | hout
  · have hDK : D ⊆ K := by
      rw [← hreg]
      exact closure_minimal (hin.trans interior_subset) hK.isClosed
    have hf : frontier (K \ D) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxK : x ∈ frontier K := by
        rcases frontier_inter_subset K Dᶜ hx with hx | hx
        · exact hx.1
        · exact hfront ▸ (show x ∈ frontier D from by
            simpa only [frontier_compl] using hx.2)
      obtain ⟨B, hxB, _, hhalfB⟩ := hhalf x hxK
      have himage := B.isImage_frontier_of_affine_nonneg ell hell hhalfB
      obtain ⟨U, hU, hxU, hUB, hfill⟩ := fill_local_halfspace hD.isClosed hreg
        (hfront.symm ▸ hxK) B hxB ell
        (fun y hy => by rw [hfront]; exact (himage.apply_mem_iff hy).symm) (by
          intro y hy hyB
          have hle : 0 ≤ ell (B y) := (hhalfB y hyB).mp (interior_subset (hin hy))
          have hne : ell (B y) ≠ 0 := by
            intro hz
            have hyf := (himage.apply_mem_iff hyB).mp hz
            exact hyf.2 (hin hy)
          exact lt_of_le_of_ne hle (Ne.symm hne))
      obtain ⟨y, hyU, hyKD⟩ := mem_closure_iff.mp hx.1 U hU hxU
      exact hyKD.2 (hfill y hyU ((hhalfB y (hUB hyU)).mp hyKD.1))
    have hempty : K \ D = ∅ := by
      by_contra hne
      have hall := (isClopen_iff_frontier_eq_empty.mpr hf).eq_univ
        (Set.nonempty_iff_ne_empty.mpr hne)
      exact NormedSpace.unbounded_univ ℝ V3
        (hall ▸ hK.isBounded.subset sdiff_subset)
    exact Subset.antisymm hDK (sdiff_eq_empty.mp hempty)
  · have houtK : interior D ⊆ Kᶜ := by
      intro x hx hxK
      by_cases hxint : x ∈ interior K
      · exact hout hx (subset_closure hxint)
      · have hxf : x ∈ frontier K := ⟨hK.isClosed.closure_eq.symm ▸ hxK, hxint⟩
        exact (hfront.symm ▸ hxf).2 hx
    have hf : frontier (K ∪ D) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxK : x ∈ frontier K := by
        rcases frontier_union_subset K D hx with hx | hx
        · exact hx.1
        · exact hfront ▸ hx.2
      obtain ⟨B, hxB, _, hhalfB⟩ := hhalf x hxK
      have himage := B.isImage_frontier_of_affine_nonneg ell hell hhalfB
      obtain ⟨U, hU, hxU, hUB, hfill⟩ := fill_local_halfspace hD.isClosed hreg
        (hfront.symm ▸ hxK) B hxB (-ell)
        (fun y hy => by
          rw [hfront]
          change y ∈ frontier K ↔ -(ell (B y)) = 0
          rw [neg_eq_zero]
          exact (himage.apply_mem_iff hy).symm) (by
          intro y hy hyB
          have hnot : ¬ 0 ≤ ell (B y) := fun h => houtK hy ((hhalfB y hyB).mpr h)
          change 0 < -ell (B y)
          exact neg_pos.mpr (not_le.mp hnot))
      have hsub : U ⊆ K ∪ D := by
        intro y hy
        by_cases hle : 0 ≤ ell (B y)
        · exact Or.inl ((hhalfB y (hUB hy)).mpr hle)
        · exact Or.inr (hfill y hy (by
            change 0 ≤ -ell (B y)
            exact neg_nonneg.mpr (not_le.mp hle).le))
      exact hx.2 ((hU.subset_interior_iff.mpr hsub) hxU)
    have hall := (isClopen_iff_frontier_eq_empty.mpr hf).eq_univ
      ((hconn.nonempty.mono interior_subset).mono subset_union_right)
    exact (NormedSpace.unbounded_univ ℝ V3 (hall ▸ (hK.union hD).isBounded)).elim

theorem exists_brown_ball_pair_of_compact_halfspace_domain
    (brown : HasBrownLocallyFlatSphereBalls) {K : Set V3} (hK : IsCompact K)
    (s : sphere (0 : V3) 1 ≃ₜ frontier K)
    (hhalf : ∀ x ∈ frontier K,
      ∃ B : OpenPartialHomeomorph V3 V3, x ∈ B.source ∧
        B x 0 = 0 ∧ ∀ y ∈ B.source, y ∈ K ↔ 0 ≤ B y 0) :
    IsUnitBallPair V3 K (frontier K) := by
  let ell : V3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj (0 : Fin 3)).toContinuousAffineMap
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro hz
    have h : ell.toAffineMap.linear (fun _ => 1) = 1 := rfl
    rw [hz] at h
    norm_num at h
  have hflat : Nonempty (LocallyFlatTopologicalSphere (frontier K)) := by
    refine ⟨⟨s, ?_⟩⟩
    intro x hx
    obtain ⟨B, hxB, _, hB⟩ := hhalf x hx
    refine ⟨B, hxB, fun y hy => ?_⟩
    exact ((B.isImage_frontier_of_affine_nonneg ell hell hB).apply_mem_iff hy).symm
  obtain ⟨D, hD, hfront, hp⟩ := brown _ hflat
  obtain ⟨hconn, hreg⟩ := ball_pair_regular_interior hD hfront hp
  have heq := compact_domain_eq_brown_ball hK hD hfront hconn hreg hhalf
  exact heq ▸ hp

end PoincareConjecture.M76
