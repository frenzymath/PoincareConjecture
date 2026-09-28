import PoincareConjecture.Proofs.M76.Dehn.OriginalPairedRegionCharts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoBranchWindows
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteClippedChartInverse
import PoincareConjecture.Proofs.M76.Rigidity.SourceDiskPairCharts

set_option autoImplicit false

open Set Metric Topology Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}

theorem inverse_branch_chart_PL (step : Step s t)
    (B : OpenPartialHomeomorph t.Carrier s.Carrier)
    (hB : EqOn B (step.projection ∘ step.inclusion) B.source)
    (H : OpenPartialHomeomorph t.Carrier V3) (k : t.Index)
    (hHk : H.source ⊆ (t.charts k).source)
    (hH : (t.charts k).symm.trans H ∈ piecewiseAffineGroupoid V3)
    (l : s.Index) :
    (s.charts l).symm.trans (B.symm.trans H) ∈ piecewiseAffineGroupoid V3 := by
  let A := (s.charts l).symm.trans (B.symm.trans (t.charts k))
  let T := (s.charts l).symm.trans (B.symm.trans H)
  let F := (t.charts k).symm.trans H
  have hA : A ∈ piecewiseAffineGroupoid V3 := by
    simpa only [A, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).symm (step.branch_chart_PL B hB k l)
  have hlocal := ((mem_piecewiseAffineGroupoid_iff_forward F).mp hH).comp
    ((mem_piecewiseAffineGroupoid_iff_forward A).mp hA)
  have hsub : T.source ⊆ A.source ∩ A ⁻¹' F.source := by
    intro z hz
    have hu : B.symm ((s.charts l).symm z) ∈ (t.charts k).source := hHk hz.2.2
    refine ⟨⟨hz.1, hz.2.1, hu⟩, ?_⟩
    change (t.charts k) (B.symm ((s.charts l).symm z)) ∈ F.source
    refine ⟨(t.charts k).map_source hu, ?_⟩
    change (t.charts k).symm ((t.charts k) (B.symm ((s.charts l).symm z))) ∈ H.source
    rw [(t.charts k).left_inv hu]
    exact hz.2.2
  apply (mem_piecewiseAffineGroupoid_iff_forward T).mpr
  apply (hlocal.mono T.open_source hsub).congr
  intro z hz
  change H ((t.charts k).symm ((t.charts k) (B.symm ((s.charts l).symm z)))) =
    H (B.symm ((s.charts l).symm z))
  exact congrArg H ((t.charts k).left_inv (hHk hz.2.2))

theorem Step.exists_original_double_branch_chart
    (step : Step s t) {R : Set M} (he : PoincareConjecture.M76.PLDomain e R)
    {j : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j D)
    (hemb : IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D (t.projection ⁻¹' R))
    (hproper : ∀ z : D, j z ∈ frontier (t.projection ⁻¹' R) ↔
      (z : V2) ∈ sphere (0 : V2) 1)
    (a b : D) (hab : a ≠ b)
    (hpair : step.projection (step.inclusion (j a)) =
      step.projection (step.inclusion (j b)))
    {W : Set s.Carrier} (hW : IsOpen W)
    (haW : step.projection (step.inclusion (j a)) ∈ W) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3),
      j a ∈ w.left.source ∧ j b ∈ w.right.source ∧
      step.projection (step.inclusion (j a)) ∈ Q.source ∧
      Q.source ⊆ W ∩ w.target ∧ Q (step.projection (step.inclusion (j a))) = 0 ∧
      (∀ l, (s.charts l).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      (step.projection ∘ step.inclusion) ⁻¹' Q.source =
        (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' Q.source) ∪
          (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' Q.source) ∧
      ((Q.source ⊆ interior (s.projection ⁻¹' R) ∧
          ∀ y ∈ Q.source,
            y ∈ (step.projection ∘ step.inclusion) '' (j '' D ∩ w.left.source) ↔
              (c (Q y)).2 = 0) ∨
        ((∀ y ∈ Q.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ (c (Q y)).1.1) ∧
          (∀ y ∈ Q.source, y ∈ frontier (s.projection ⁻¹' R) ↔
            (c (Q y)).1.1 = 0) ∧
          ∀ y ∈ Q.source,
            y ∈ (step.projection ∘ step.inclusion) '' (j '' D ∩ w.left.source) ↔
              0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0)) ∧
      (∀ z : D, step.projection (step.inclusion (j z)) ∈ frontier (s.projection ⁻¹' R) ↔
        (z : V2) ∈ sphere (0 : V2) 1) ∧
      ∀ J : SimplicialComplex ℝ V3, J.faces.Finite → J.space ⊆ Q.target →
        ∃ (P : SimplicialComplex ℝ V3) (q : V3 → V2), P.faces.Finite ∧
          P.space = (w.right.trans Q) '' (j '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
          FinitePiecewiseAffineOn q P.space ∧ InjOn q P.space ∧ MapsTo q P.space D ∧
          (∀ z ∈ P.space, j (q z) ∈ (w.right.trans Q).source ∧
            (w.right.trans Q) (j (q z)) = z) ∧
          (∀ z ∈ D, j z ∈ (w.right.trans Q).source → (w.right.trans Q) (j z) ∈ J.space →
            q ((w.right.trans Q) (j z)) = z) ∧
          ∀ z ∈ P.space, z ∈ interior J.space → q z ∈ interior D →
            q z ∈ interior (q '' P.space) := by
  classical
  let p := step.projection ∘ step.inclusion
  have hp : Continuous p := step.projection.continuous.comp step.inclusion.continuous
  have hjne : j a ≠ j b := fun h => hab (hemb.injective h)
  obtain ⟨w, ha, hb⟩ := step.projectionInclusion_local.exists_twoBranchWindow
    (fun y => (step.projectionInclusion_fiber y).1)
    (fun y => (step.projectionInclusion_fiber y).2) hpair hjne
  obtain ⟨H₀, haH₀, _, hH₀a, hH₀PL, hmodel⟩ :=
    PoincareConjecture.M76.exists_original_proper_disk_pair_chart
      (t.plDomain_region he) hj hemb hDR hproper a
  obtain ⟨k, hak⟩ := t.cover (j a)
  let c : V3 ≃L[ℝ] C3 := ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let T := H₀.trans c.symm.toHomeomorph.toOpenPartialHomeomorph
  have hTPL (i : t.Index) : (t.charts i).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
    have h := (locallyPiecewiseAffineOn_affine
      c.symm.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp (hH₀PL i).1
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact h.mono ((t.charts i).symm.trans T).open_source
      (fun z hz => ⟨⟨hz.1, hz.2.1⟩, mem_univ _⟩)
  let V := w.left.source ∩ ((t.charts k).source ∩ p ⁻¹' W)
  have hV : IsOpen V := w.left.open_source.inter
    ((t.charts k).open_source.inter (hW.preimage hp))
  let H := T.restrOpen V hV
  have haH : j a ∈ H.source := ⟨⟨haH₀, mem_univ _⟩, ha, hak, haW⟩
  have hHk : H.source ⊆ (t.charts k).source := fun _ hx => hx.2.2.1
  have hHH₀ : H.source ⊆ H₀.source := fun _ hx => hx.1.1
  have hHW : MapsTo p H.source W := fun _ hx => hx.2.2.2
  have hHPL : (t.charts k).symm.trans H ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hTPL k)).mono
      ((t.charts k).symm.trans H).open_source (fun z hz => ⟨hz.1, hz.2.1⟩)
  let Q := w.left.symm.trans H
  have hleft (x : t.Carrier) (hx : x ∈ w.left.source) : w.left.symm (p x) = x :=
    (congrArg w.left.symm (congrFun w.left_eq x)).symm.trans (w.left.left_inv hx)
  have hproj (y : s.Carrier) (hy : y ∈ w.left.target) : p (w.left.symm y) = y :=
    (congrFun w.left_eq (w.left.symm y)).symm.trans (w.left.right_inv hy)
  have haQ : p (j a) ∈ Q.source := by
    refine ⟨?_, ?_⟩
    · change p (j a) ∈ w.left.target
      have heq : w.left (j a) = p (j a) := congrFun w.left_eq (j a)
      exact (congrArg (fun y => y ∈ w.left.target) heq).mp (w.left.map_source ha)
    · change w.left.symm (p (j a)) ∈ H.source
      rw [hleft (j a) ha]
      exact haH
  have hQW : Q.source ⊆ W ∩ w.target := by
    intro y hy
    refine ⟨?_, w.left_target.subset hy.1⟩
    have h := hHW hy.2
    change p (w.left.symm y) ∈ W at h
    rwa [hproj y hy.1] at h
  have hQzero : Q (p (j a)) = 0 := by
    change c.symm (H₀ (w.left.symm (p (j a)))) = 0
    rw [hleft (j a) ha, hH₀a, map_zero]
  have hQPL (l : s.Index) : (s.charts l).symm.trans Q ∈ piecewiseAffineGroupoid V3 :=
    inverse_branch_chart_PL step w.left (fun x _ => congrFun w.left_eq x) H k hHk hHPL l
  have hbranches (k : t.Index) :
      (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
      (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3 :=
    ⟨step.compatible_branch_chart w.left (fun x _ => congrFun w.left_eq x) Q hQPL k,
      step.compatible_branch_chart w.right (fun x _ => congrFun w.right_eq x) Q hQPL k⟩
  have hwhole : p ⁻¹' Q.source =
      (w.left.source ∩ p ⁻¹' Q.source) ∪ (w.right.source ∩ p ⁻¹' Q.source) := by
    ext x
    constructor
    · intro hx
      have hxw : x ∈ p ⁻¹' w.target := (hQW hx).2
      rw [w.whole_preimage] at hxw
      exact hxw.elim (fun h => Or.inl ⟨h, hx⟩) (fun h => Or.inr ⟨h, hx⟩)
    · exact fun hx => hx.elim And.right And.right
  have hcoord (y : s.Carrier) : c (Q y) = H₀ (w.left.symm y) := c.apply_symm_apply _
  have hsheet (y : s.Carrier) (hy : y ∈ Q.source) :
      y ∈ p '' (j '' D ∩ w.left.source) ↔ w.left.symm y ∈ j '' D := by
    constructor
    · rintro ⟨x, ⟨hxD, hx⟩, hxy⟩
      rw [← hxy, hleft x hx]
      exact hxD
    · intro hyD
      exact ⟨w.left.symm y, ⟨hyD, w.left.map_target hy.1⟩, hproj y hy.1⟩
  refine ⟨w, c, Q, ha, hb, haQ, hQW, hQzero, hQPL, hbranches, hwhole, ?_, ?_, ?_⟩
  · rcases hmodel with ⟨hinterior, hplane⟩ | ⟨hregion, hhalfplane⟩
    · refine Or.inl ⟨?_, ?_⟩
      · intro y hy
        have hi := hinterior (hHH₀ hy.2)
        rw [step.region_preimage R] at hi
        have h := step.projectionInclusion_local.isOpenMap.interior_preimage_subset_preimage_interior
          hi
        change p (w.left.symm y) ∈ interior (s.projection ⁻¹' R) at h
        rwa [hproj y hy.1] at h
      · intro y hy
        rw [hsheet y hy, hcoord]
        exact hplane (w.left.symm y) (hHH₀ hy.2)
    · have hr (y : s.Carrier) (hy : y ∈ Q.source) :
          y ∈ s.projection ⁻¹' R ↔ 0 ≤ (c (Q y)).1.1 := by
        have h := hregion (w.left.symm y) (hHH₀ hy.2)
        rw [step.region_preimage R] at h
        change p (w.left.symm y) ∈ s.projection ⁻¹' R ↔
          0 ≤ (H₀ (w.left.symm y)).1.1 at h
        rwa [hproj y hy.1, ← hcoord] at h
      let ell : V3 →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap)
      have hell : ell.toLinearMap ≠ 0 := by
        intro h
        have hv : ell (c.symm ((1, 0), 0)) = 1 := by
          change (c (c.symm ((1, 0), 0))).1.1 = 1
          rw [c.apply_symm_apply]
        change ell.toLinearMap (c.symm ((1, 0), 0)) = 1 at hv
        rw [h, LinearMap.zero_apply] at hv
        exact zero_ne_one hv
      have hfront := Q.isImage_frontier_of_affine_nonneg
        ell.toContinuousAffineMap hell hr
      refine Or.inr ⟨hr, ?_, ?_⟩
      · exact fun y hy => (hfront.apply_mem_iff hy).symm
      · intro y hy
        rw [hsheet y hy, hcoord]
        exact hhalfplane (w.left.symm y) (hHH₀ hy.2)
  · intro z
    have h : j z ∈ frontier (t.projection ⁻¹' R) ↔
        p (j z) ∈ frontier (s.projection ⁻¹' R) := by
      rw [step.frontier_preimage R]
      rfl
    exact h.symm.trans (hproper z)
  · intro J hJ hJQ
    obtain ⟨_, _, _, _, _, _, hmodelD, _⟩ :=
      isFinitePLBallPair_unit_cube (ι := Fin 2)
    obtain ⟨_, ⟨K, hK, hKD, _⟩, _⟩ := hmodelD
    have hjK : PolyhedralPLInCharts t.charts j K.space := hKD.symm ▸ hj
    have hinj : InjOn j K.space := by
      intro x hx y hy hxy
      exact congrArg Subtype.val (hemb.injective
        (show j (⟨x, hKD.subset hx⟩ : D) = j (⟨y, hKD.subset hy⟩ : D) from hxy))
    have htarget : (w.right.trans Q).target = Q.target := by
      apply inter_eq_left.mpr
      intro z hz
      exact w.right_target.symm.subset (hQW (Q.map_target hz)).2
    obtain ⟨P, q, hP, hPs, hq, hqD, hright, hleft⟩ :=
      hjK.exists_finite_clipped_chart_inverse K hK hinj (w.right.trans Q)
        (fun k => (hbranches k).2) J hJ (fun z hz => htarget.symm.subset (hJQ hz))
    refine ⟨P, q, hP, ?_, hq, ?_, ?_, hright, ?_, ?_⟩
    · simpa only [hKD] using hPs
    · intro x hx y hy hxy
      exact (hright x hx).2.symm.trans ((congrArg ((w.right.trans Q) ∘ j) hxy).trans
        (hright y hy).2)
    · exact fun z hz => hKD.subset (hqD hz)
    · intro z hz hzQ hzJ
      exact hleft z (hKD.symm.subset hz) hzQ hzJ
    · intro z hz hzJ hzD
      let B := w.right.trans Q
      let O := interior D ∩ j ⁻¹' B.source
      have hO : IsOpen O :=
        (hj.continuousOn.mono interior_subset).isOpen_inter_preimage
          isOpen_interior B.open_source
      have hcomp : ContinuousOn (B ∘ j) O := B.continuousOn.comp
        (hj.continuousOn.mono (fun _ hx => interior_subset hx.1)) (fun _ hx => hx.2)
      have hN : IsOpen (O ∩ (B ∘ j) ⁻¹' interior J.space) :=
        hcomp.isOpen_inter_preimage hO isOpen_interior
      have hpoint : q z ∈ O ∩ (B ∘ j) ⁻¹' interior J.space := by
        refine ⟨⟨hzD, (hright z hz).1⟩, ?_⟩
        change B (j (q z)) ∈ interior J.space
        rw [(hright z hz).2]
        exact hzJ
      have hsub : O ∩ (B ∘ j) ⁻¹' interior J.space ⊆ q '' P.space := by
        intro x hx
        have hxK : x ∈ K.space := hKD.symm.subset (interior_subset hx.1.1)
        have hxB : j x ∈ B.source := hx.1.2
        have hxJ : B (j x) ∈ J.space := interior_subset hx.2
        refine ⟨B (j x), ?_, hleft x hxK hxB hxJ⟩
        rw [hPs]
        exact ⟨⟨j x, ⟨mem_image_of_mem j hxK, hxB⟩, rfl⟩, hxJ⟩
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hN.mem_nhds hpoint) hsub)

end Geometry.OriginalPLTower
