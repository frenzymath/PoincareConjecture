import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcCrossings
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarMarkedCutCharts
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarBoundaryExtension
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateFourRegionIncidence
import PoincareConjecture.Proofs.M76.Triangulation.ConvexFrontierMarkedDecomposition
import PoincareConjecture.Proofs.M76.Triangulation.ConvexFrontierCoordinateQuadrants

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

private theorem exists_crossed_convex_frontier
    (K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hK : K.faces.Finite)
    {C : Set ((ℝ × ℝ) × ℝ)} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hKC : K.space = C) (hC0 : (0 : (ℝ × ℝ) × ℝ) ∈ interior C)
    {n : ℕ} (P : Polygon ((ℝ × ℝ) × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPC : P.boundary ℝ ⊆ frontier C)
    {a b : (ℝ × ℝ) × ℝ} (hab : a ≠ b)
    (hzero : P.boundary ℝ ∩ {x | x.2 = 0} = {a, b})
    (hneg : ∃ x ∈ P.boundary ℝ, x.2 < 0)
    (hpos : ∃ x ∈ P.boundary ℝ, 0 < x.2) :
    ∃ e : frontier C ≃ₜ frontier C, e.IsFinitePL ∧
      (∀ x : frontier C, (x : (ℝ × ℝ) × ℝ).2 = 0 ↔
        (e x : (ℝ × ℝ) × ℝ).1.1 = 0) ∧
      (∀ x : frontier C, 0 ≤ (x : (ℝ × ℝ) × ℝ).2 ↔
        0 ≤ (e x : (ℝ × ℝ) × ℝ).1.1) ∧
      ∀ x : frontier C, (x : (ℝ × ℝ) × ℝ) ∈ P.boundary ℝ ↔
        (e x : (ℝ × ℝ) × ℝ).2 = 0 := by
  classical
  let A : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  obtain ⟨arc, disk, hArc, hAi, hDisk, hDi, hcover, hequator,
      hsurface, hpositive, _⟩ :=
    K.exists_convex_frontier_marked_decomposition hK hC hcv hKC
      (by simp [Module.finrank_prod]) A.toAffineMap hC0 rfl
      P hP hinj hPC hab hzero hneg hpos
  obtain ⟨hn, hnC⟩ := hC.gauge_inv_smul_mem_frontier hcv hC0
    (show (((0, -1), 0) : (ℝ × ℝ) × ℝ) ≠ 0 by norm_num)
  obtain ⟨hp, hpC⟩ := hC.gauge_inv_smul_mem_frontier hcv hC0
    (show (((0, 1), 0) : (ℝ × ℝ) × ℝ) ≠ 0 by norm_num)
  let c := -(gauge C (((0, -1), 0) : (ℝ × ℝ) × ℝ))⁻¹
  let d := (gauge C (((0, 1), 0) : (ℝ × ℝ) × ℝ))⁻¹
  have hc : c < 0 := neg_neg_of_pos hn
  have hd : 0 < d := hp
  have hcC : ((0, c), 0) ∈ frontier C := by simpa [c, smul_eq_mul] using hnC
  have hdC : ((0, d), 0) ∈ frontier C := by simpa [d, smul_eq_mul] using hpC
  have hcd : (((0, c), 0) : (ℝ × ℝ) × ℝ) ≠ ((0, d), 0) := by
    intro h
    exact (hc.trans hd).ne (congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) h)
  obtain ⟨hB0, hB1, hT⟩ := K.isFinitePLBallPair_coordinate_frontier_quadrants
    hK hC hcv hKC hC0 hc hd hcC hdC
  let B := CoordinateFourRegions.arc (frontier C)
  let T := CoordinateFourRegions.region (frontier C)
  have hB (i : Bool × Bool) : IsFinitePLBallPair ℝ (B i)
      {((0, c), 0), ((0, d), 0)} := by
    rcases i with ⟨i, j⟩
    cases i
    · exact hB0 j
    · exact hB1 j
  have hBi : Pairwise (fun i j => B i ∩ B j = {((0, c), 0), ((0, d), 0)}) := by
    intro i j hij
    exact (CoordinateFourRegions.arc_inter_of_ne (frontier C) hij).trans
      (hcv.frontier_inter_coordinate_planes_eq_poles hC0 hc hd hcC hdC)
  have hT' (i : Bool × Bool) : IsFinitePLBallPair (ℝ × ℝ) (T i)
      (B (false, i.2) ∪ B (true, i.1)) := hT i.1 i.2
  obtain ⟨H, hH, hregions, harcs, _, _⟩ := exists_finitePL_four_disk_gluing
    arc disk B T hab hcd hArc hB hAi hBi hDisk hT' hDi
      (CoordinateFourRegions.region_contacts (frontier C))
  have htarget : (⋃ i, T i) = frontier C :=
    CoordinateFourRegions.iUnion_region (frontier C)
  let e := (Homeomorph.setCongr hcover.symm).trans
    (H.trans (Homeomorph.setCongr htarget))
  have hEarc (i : Bool × Bool) (x : frontier C) :
      (x : (ℝ × ℝ) × ℝ) ∈ arc i ↔ (e x : (ℝ × ℝ) × ℝ) ∈ B i :=
    harcs i ⟨x, hcover.symm.subset x.property⟩
  have hEregion (i : Bool × Bool) (x : frontier C) :
      (x : (ℝ × ℝ) × ℝ) ∈ disk i ↔ (e x : (ℝ × ℝ) × ℝ) ∈ T i :=
    hregions i ⟨x, hcover.symm.subset x.property⟩
  have hBzero : B (false, false) ∪ B (false, true) =
      frontier C ∩ {x | x.1.1 = 0} :=
    CoordinateFourRegions.arc_kind_union (frontier C) false
  have hBsurface : B (true, false) ∪ B (true, true) =
      frontier C ∩ {x | x.2 = 0} :=
    CoordinateFourRegions.arc_kind_union (frontier C) true
  have hTpositive : T (false, false) ∪ T (false, true) =
      frontier C ∩ {x | 0 ≤ x.1.1} :=
    CoordinateFourRegions.region_height_union (frontier C) false
  refine ⟨e, hH.setCongr hcover htarget, ?_, ?_, ?_⟩
  · intro x
    have h := or_congr (hEarc (false, false) x) (hEarc (false, true) x)
    change (x.val ∈ arc (false, false) ∪ arc (false, true)) ↔
      ((e x).val ∈ B (false, false) ∪ B (false, true)) at h
    rw [hequator, hBzero] at h
    change (x.val ∈ frontier C ∧ x.val.2 = 0) ↔
      ((e x).val ∈ frontier C ∧ (e x).val.1.1 = 0) at h
    simpa only [x.property, (e x).property, true_and] using h
  · intro x
    have h := or_congr (hEregion (false, false) x) (hEregion (false, true) x)
    change (x.val ∈ disk (false, false) ∪ disk (false, true)) ↔
      ((e x).val ∈ T (false, false) ∪ T (false, true)) at h
    rw [hpositive, hTpositive] at h
    change (x.val ∈ frontier C ∧ 0 ≤ x.val.2) ↔
      ((e x).val ∈ frontier C ∧ 0 ≤ (e x).val.1.1) at h
    simpa only [x.property, (e x).property, true_and] using h
  · intro x
    have h := or_congr (hEarc (true, false) x) (hEarc (true, true) x)
    change (x.val ∈ arc (true, false) ∪ arc (true, true)) ↔
      ((e x).val ∈ B (true, false) ∪ B (true, true)) at h
    rw [hsurface, hBsurface] at h
    change (x.val ∈ P.boundary ℝ) ↔
      ((e x).val ∈ frontier C ∧ (e x).val.2 = 0) at h
    simpa only [(e x).property, true_and] using h

theorem exists_original_crossed_star
    (K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hK : K.faces.Finite)
    (hz : (0 : (ℝ × ℝ) × ℝ) ∈ K.vertices)
    (hint : (0 : (ℝ × ℝ) × ℝ) ∈ interior K.space)
    {n : ℕ} (P : Polygon ((ℝ × ℝ) × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPK : P.boundary ℝ ⊆ (K.link 0).space)
    {a b : (ℝ × ℝ) × ℝ} (hab : a ≠ b)
    (hzero : P.boundary ℝ ∩ {x | x.2 = 0} = {a, b})
    (hneg : ∃ x ∈ P.boundary ℝ, x.2 < 0)
    (hpos : ∃ x ∈ P.boundary ℝ, 0 < x.2) :
    ∃ (C : Set ((ℝ × ℝ) × ℝ)) (g : ((ℝ × ℝ) × ℝ) → ((ℝ × ℝ) × ℝ))
      (H : (K.closedStar 0).space ≃ₜ C)
      (e : (K.link 0).space ≃ₜ frontier C),
      IsCompact C ∧ Convex ℝ C ∧ (0 : (ℝ × ℝ) × ℝ) ∈ interior C ∧
      H.IsFinitePL ∧ e.IsFinitePL ∧
      (∀ x, (H x : (ℝ × ℝ) × ℝ) = g x) ∧ g 0 = 0 ∧
      (∀ x : (K.link 0).space, g x = e x) ∧
      (∀ (x : (K.link 0).space) (r : ℝ), r ∈ Icc 0 1 →
        g (r • (x : (ℝ × ℝ) × ℝ)) = r • (e x : (ℝ × ℝ) × ℝ)) ∧
      (∀ x : (K.closedStar 0).space,
        (x : (ℝ × ℝ) × ℝ) ∈ (K.link 0).space ↔
          (H x : (ℝ × ℝ) × ℝ) ∈ frontier C) ∧
      (∀ x : (K.closedStar 0).space, (x : (ℝ × ℝ) × ℝ).2 = 0 ↔
        (H x : (ℝ × ℝ) × ℝ).1.1 = 0) ∧
      (∀ x : (K.closedStar 0).space, 0 ≤ (x : (ℝ × ℝ) × ℝ).2 ↔
        0 ≤ (H x : (ℝ × ℝ) × ℝ).1.1) ∧
      ∀ x : (K.closedStar 0).space,
        (x : (ℝ × ℝ) × ℝ) ∈ convexJoin ℝ {0} (P.boundary ℝ) ↔
          (H x : (ℝ × ℝ) × ℝ).2 = 0 := by
  classical
  let Z : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  let c : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨C, _, S, hC, hcv, hC0, _, _, hS, hboundary, hcuts⟩ :=
    K.exists_finitePL_closedStar_chart_preserving_cut_family
      hK hz hint c (fun _ : Unit => Z)
  have hsub : (K.link 0).space ⊆ (K.closedStar 0).space :=
    SimplicialComplex.space_subset_of_le (K.link_le_closedStar 0)
  let e0 := S.restrictSubsets hsub hC.isClosed.frontier_subset hboundary
  have he0 : e0.IsFinitePL := hS.restrictSubsets hsub hC.isClosed.frontier_subset
    hboundary (K.link 0) (SimplicialComplex.finite_link_faces hK 0) rfl
  obtain ⟨f, hf, hef⟩ := he0
  have hfi : InjOn f (K.link 0).space := by
    intro x hx y hy hxy
    have hexy : e0 ⟨x, hx⟩ = e0 ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e0.injective hexy)
  have hmarks (x : (K.link 0).space) :
      ((f x).2 = 0 ↔ (x : (ℝ × ℝ) × ℝ).2 = 0) ∧
      (0 ≤ (f x).2 ↔ 0 ≤ (x : (ℝ × ℝ) × ℝ).2) := by
    have h := hcuts () ⟨x, hsub x.property⟩
    change ((e0 x : (ℝ × ℝ) × ℝ).2 = 0 ↔ x.val.2 = 0) ∧
      (0 ≤ (e0 x : (ℝ × ℝ) × ℝ).2 ↔ 0 ≤ x.val.2) at h
    rwa [hef x] at h
  obtain ⟨m, Q, hQi, hQ, hQb⟩ :=
    P.exists_polygon_finitePL_image hP hinj hf hPK (hfi.mono hPK)
  have hQC : Q.boundary ℝ ⊆ frontier C := by
    rw [hQb]
    rintro y ⟨x, hx, rfl⟩
    rw [← hef ⟨x, hPK hx⟩]
    exact (e0 ⟨x, hPK hx⟩).property
  have haP : a ∈ P.boundary ℝ := (hzero.symm.subset (by simp)).1
  have hbP : b ∈ P.boundary ℝ := (hzero.symm.subset (by simp)).1
  have hfAB : f a ≠ f b := fun h => hab (hfi (hPK haP) (hPK hbP) h)
  have hQzero : Q.boundary ℝ ∩ {x | x.2 = 0} = {f a, f b} := by
    ext y
    constructor
    · rintro ⟨hy, hy0⟩
      obtain ⟨x, hx, rfl⟩ := hQb.subset hy
      have hx0 := (hmarks ⟨x, hPK hx⟩).1.mp hy0
      have hxpair := hzero.subset ⟨hx, hx0⟩
      rcases mem_insert_iff.mp hxpair with hxa | hxb
      · exact mem_insert_iff.mpr (Or.inl (congrArg f hxa))
      · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr
          (congrArg f (mem_singleton_iff.mp hxb))))
    · intro hy
      rcases mem_insert_iff.mp hy with hya | hyb
      · subst y
        exact ⟨hQb.symm.subset (mem_image_of_mem f haP),
          (hmarks ⟨a, hPK haP⟩).1.mpr (hzero.symm.subset (by simp)).2⟩
      · have hyb' := mem_singleton_iff.mp hyb
        subst y
        exact ⟨hQb.symm.subset (mem_image_of_mem f hbP),
          (hmarks ⟨b, hPK hbP⟩).1.mpr (hzero.symm.subset (by simp)).2⟩
  have hQneg : ∃ x ∈ Q.boundary ℝ, x.2 < 0 := by
    obtain ⟨x, hx, hn⟩ := hneg
    refine ⟨f x, hQb.symm.subset (mem_image_of_mem f hx), ?_⟩
    exact lt_of_not_ge (fun h => hn.not_ge ((hmarks ⟨x, hPK hx⟩).2.mp h))
  have hQpos : ∃ x ∈ Q.boundary ℝ, 0 < x.2 := by
    obtain ⟨x, hx, hp⟩ := hpos
    have hnonneg := (hmarks ⟨x, hPK hx⟩).2.mpr hp.le
    have hne : (f x).2 ≠ 0 := fun h => hp.ne' ((hmarks ⟨x, hPK hx⟩).1.mp h)
    exact ⟨f x, hQb.symm.subset (mem_image_of_mem f hx), lt_of_le_of_ne hnonneg hne.symm⟩
  obtain ⟨_, ⟨J, hJ, hJC, _⟩, _⟩ := hS.symm
  obtain ⟨d, hd, hd0, hdp, hdP⟩ := exists_crossed_convex_frontier J hJ
    hC hcv hJC hC0 Q hQ hQi hQC hfAB hQzero hQneg hQpos
  let e := e0.trans d
  have he : e.IsFinitePL := (show e0.IsFinitePL from ⟨f, hf, hef⟩).trans hd
  have hEzero (x : (K.link 0).space) : x.val.2 = 0 ↔ (e x).val.1.1 = 0 := by
    have h0 : (e0 x).val.2 = 0 ↔ x.val.2 = 0 := by
      rw [hef x]
      exact (hmarks x).1
    exact h0.symm.trans (hd0 (e0 x))
  have hEpos (x : (K.link 0).space) : 0 ≤ x.val.2 ↔ 0 ≤ (e x).val.1.1 := by
    have hp : 0 ≤ (e0 x).val.2 ↔ 0 ≤ x.val.2 := by
      rw [hef x]
      exact (hmarks x).2
    exact hp.symm.trans (hdp (e0 x))
  have hEP (x : (K.link 0).space) : x.val ∈ P.boundary ℝ ↔ (e x).val.2 = 0 := by
    have hmem : x.val ∈ P.boundary ℝ ↔ (e0 x).val ∈ Q.boundary ℝ := by
      rw [hef x, hQb]
      constructor
      · exact mem_image_of_mem f
      · rintro ⟨y, hy, hxy⟩
        exact hfi (hPK hy) x.property hxy ▸ hy
    exact hmem.trans (hdP (e0 x))
  have hne : (K.link 0).space.Nonempty := ⟨a, hPK haP⟩
  obtain ⟨g, H, hH, hHg, hg0, hbase, hray⟩ :=
    he.exists_closedStar_extension_radial K hK hz hne hC hcv hC0
  have hkeep (x : (K.link 0).space) :
      H ⟨x, hsub x.property⟩ = ⟨e x, hC.isClosed.frontier_subset (e x).property⟩ := by
    apply Subtype.ext
    exact (hHg ⟨x, hsub x.property⟩).trans (hbase x)
  have hwhole (x : (K.closedStar 0).space) :
      (x.val.2 = 0 ↔ (H x).val.1.1 = 0) ∧
      (0 ≤ x.val.2 ↔ 0 ≤ (H x).val.1.1) := by
    by_cases hx0 : x.val = 0
    · have hHx : (H x).val = 0 := (hHg x).trans (by rw [hx0, hg0])
      simp [hx0, hHx]
    · obtain ⟨z, hzlink, r, hr, hxr⟩ :=
        SimplicialComplex.exists_linkPoint_smul x.property hx0
      have hval : (H x).val = r • (e ⟨z, hzlink⟩).val := by
        rw [hHg x, hxr]
        exact hray ⟨z, hzlink⟩ r ⟨hr.1.le, hr.2⟩
      rw [hval, hxr]
      change (r * z.2 = 0 ↔ r * (e ⟨z, hzlink⟩).val.1.1 = 0) ∧
        (0 ≤ r * z.2 ↔ 0 ≤ r * (e ⟨z, hzlink⟩).val.1.1)
      simpa only [mul_eq_zero,
        hr.1.ne', false_or, mul_nonneg_iff_of_pos_left hr.1] using
        ⟨hEzero ⟨z, hzlink⟩, hEpos ⟨z, hzlink⟩⟩
  refine ⟨C, g, H, e, hC, hcv, hC0, hH, he, hHg, hg0, hbase, hray,
    H.mem_subset_iff_of_extension e hsub hC.isClosed.frontier_subset hkeep,
    fun x => (hwhole x).1, fun x => (hwhole x).2, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨z, hzP, r, hr, hxr⟩ := (mem_convexJoin_zero_iff _ _).mp hx
    have hval : (H x).val = r • (e ⟨z, hPK hzP⟩).val := by
      rw [hHg x, hxr]
      exact hray ⟨z, hPK hzP⟩ r hr
    rw [hval]
    change r * (e ⟨z, hPK hzP⟩).val.2 = 0
    rw [(hEP ⟨z, hPK hzP⟩).mp hzP, mul_zero]
  · intro hx
    by_cases hx0 : x.val = 0
    · exact (mem_convexJoin_zero_iff _ _).mpr
        ⟨a, haP, 0, by simp, by simpa only [zero_smul] using hx0⟩
    · obtain ⟨z, hzlink, r, hr, hxr⟩ :=
        SimplicialComplex.exists_linkPoint_smul x.property hx0
      have hval : (H x).val = r • (e ⟨z, hzlink⟩).val := by
        rw [hHg x, hxr]
        exact hray ⟨z, hzlink⟩ r ⟨hr.1.le, hr.2⟩
      have hez : (e ⟨z, hzlink⟩).val.2 = 0 := by
        rw [hval] at hx
        change r * (e ⟨z, hzlink⟩).val.2 = 0 at hx
        exact (mul_eq_zero.mp hx).resolve_left hr.1.ne'
      exact (mem_convexJoin_zero_iff _ _).mpr
        ⟨z, (hEP ⟨z, hzlink⟩).mpr hez, r, ⟨hr.1.le, hr.2⟩, hxr⟩

end PoincareConjecture.M76.Dehn
