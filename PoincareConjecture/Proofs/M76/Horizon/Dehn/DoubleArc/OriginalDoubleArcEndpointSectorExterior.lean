import PoincareConjecture.Proofs.M76.Mathlib.ConvexRadialNormalization
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeFeet










set_option autoImplicit false

open Set Metric Filter Geometry Geometry.SimplicialComplex
open scoped Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)



theorem exists_signed_frontier_point_avoiding_closed_positive_set
    {C J : Set V3} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : V3) ∈ interior C) (hJ : IsClosed J)
    (hJpos : ∀ x ∈ J, 0 < x 2) (signs : Fin 2 → Bool) :
    ∃ y ∈ frontier C, y ∉ J ∧ 0 < y 2 ∧
      ∀ i : Fin 2, if signs i then 0 < y i.castSucc else y i.castSucc < 0 := by
  let w : ℝ → V3 := fun t => ![if signs 0 then 1 else -1, if signs 1 then 1 else -1, t]
  have hw (t : ℝ) : w t ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    change (if signs 0 then (1 : ℝ) else -1) = 0 at h0
    cases hs : signs 0 <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at h0 <;> norm_num at h0
  let r : ℝ → V3 := fun t => (gauge C (w t))⁻¹ • w t
  have hrad (t : ℝ) : 0 < (gauge C (w t))⁻¹ ∧ r t ∈ frontier C :=
    hC.gauge_inv_smul_mem_frontier hcv hzero (hw t)
  have hr02 : r 0 2 = 0 := by change (gauge C (w 0))⁻¹ * 0 = 0; exact mul_zero _
  have hr0 : r 0 ∉ J := by
    intro hj
    have hp := hJpos (r 0) hj
    rw [hr02] at hp
    exact lt_irrefl 0 hp
  have hwc : Continuous w := by
    apply continuous_pi
    intro j
    fin_cases j <;> simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> fun_prop
  have hgc : Continuous (fun t => gauge C (w t)) :=
    (continuous_gauge hcv (mem_interior_iff_mem_nhds.mp hzero)).comp hwc
  have hgne : gauge C (w 0) ≠ 0 := by
    intro h
    exact (hrad 0).1.ne' (by simp only [h, inv_zero])
  have hrc : ContinuousAt r 0 := (hgc.continuousAt.inv₀ hgne).smul hwc.continuousAt
  have hn : r ⁻¹' Jᶜ ∈ 𝓝 (0 : ℝ) := hrc.preimage_mem_nhds (hJ.isOpen_compl.mem_nhds hr0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  let t := ε / 2
  have ht : 0 < t := half_pos hε
  have htball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact half_lt_self hε
  have hwi (i : Fin 2) : w t i.castSucc = if signs i then 1 else -1 := by
    fin_cases i <;> rfl
  refine ⟨r t, (hrad t).2, hball htball, ?_, ?_⟩
  · change 0 < (gauge C (w t))⁻¹ * t
    exact mul_pos (hrad t).1 ht
  · intro i
    cases hs : signs i
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]
      change (gauge C (w t))⁻¹ * w t i.castSucc < 0
      rw [hwi]
      simp only [hs, Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one]
      exact neg_neg_of_pos (hrad t).1
    · simp only [hs, ↓reduceIte]
      change 0 < (gauge C (w t))⁻¹ * w t i.castSucc
      rw [hwi]
      simpa only [hs, ↓reduceIte, mul_one] using (hrad t).1



theorem exists_signed_chart_frontier_point_avoiding_compact_joint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V J : Set E} {C : Set V3} (theta : V ≃ₜ C)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hzero : (0 : V3) ∈ interior C)
    (hJ : IsCompact J) (hJV : J ⊆ V)
    (hJpos : ∀ x : J, 0 < (theta ⟨x, hJV x.property⟩ : V3) 2)
    (signs : Fin 2 → Bool) :
    ∃ z : V, (theta z : V3) ∈ frontier C ∧ (z : E) ∉ J ∧
      0 < (theta z : V3) 2 ∧
      ∀ i : Fin 2, if signs i then 0 < (theta z : V3) i.castSucc
        else (theta z : V3) i.castSucc < 0 := by
  letI : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  let u : J → V := fun x => ⟨x, hJV x.property⟩
  have hu : Continuous u := continuous_subtype_val.subtype_mk _
  let f : J → V3 := fun x => theta (u x)
  have hf : Continuous f := continuous_subtype_val.comp (theta.continuous.comp hu)
  have hfc : IsCompact (range f) := isCompact_range hf
  have hfpos : ∀ y ∈ range f, 0 < y 2 := by
    rintro _ ⟨x, rfl⟩
    exact hJpos x
  obtain ⟨y, hyfront, hynot, hy2, hysigns⟩ :=
    exists_signed_frontier_point_avoiding_closed_positive_set
      hC hcv hzero hfc.isClosed hfpos signs
  have hyC : y ∈ C := hC.isClosed.closure_eq ▸ frontier_subset_closure hyfront
  let z : V := theta.symm ⟨y, hyC⟩
  have htheta : (theta z : V3) = y := by simp only [z, Homeomorph.apply_symm_apply]
  refine ⟨z, htheta.symm ▸ hyfront, ?_, htheta.symm ▸ hy2, ?_⟩
  · intro hz
    apply hynot
    refine ⟨⟨z, hz⟩, ?_⟩
    exact htheta
  · intro i
    simpa only [htheta] using hysigns i

open Classical in



theorem exists_original_endpoint_sector_exterior_point
    {E X κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K) (reg fr arc : κ) (sheet : Fin 2 → κ)
    (g : E → X) (R : Set X) (S : Fin 2 → Set X)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ g z ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ g z ∈ frontier R)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ g z ∈ S i))
    (v : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo g (K.closedStar v).space B.source)
    (hsheets : ∀ i y, y ∈ B.source → (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0))
    (hregion : B.source ⊆ interior R ∨
      (∀ y ∈ B.source, y ∈ R ↔ 0 ≤ B y 2) ∧
      ∀ y ∈ B.source, y ∈ frontier R ↔ B y 2 = 0)
    (hvFr : g v ∈ frontier R)
    (C0 : Set V3) (theta : (K.barycentricDualBlock {(v : E)}).space ≃ₜ C0)
    (hC : IsCompact C0) (hcv : Convex ℝ C0) (hzero : (0 : V3) ∈ interior C0)
    (hlink : ∀ z : (K.barycentricDualBlock {(v : E)}).space,
      (z : E) ∈ ((K.barycentricDualBlock {(v : E)}).link v).space ↔
        (theta z : V3) ∈ frontier C0)
    (hmarks : ∀ j (z : (K.barycentricDualBlock {(v : E)}).space),
      ((theta z : V3) j = 0 ↔ B (g z) j = 0) ∧
      (0 ≤ (theta z : V3) j ↔ 0 ≤ B (g z) j))
    (J : Set E) (hJ : IsCompact J)
    (hJV : J ⊆ (K.barycentricDualBlock {(v : E)}).space)
    (hJD : J ⊆ ((M reg).barycentricDualBlock {(v : E)}).space)
    (hmiss : Disjoint J (M fr).space) (signs : Fin 2 → Bool) :
    ∃ z : E, z ∈ ((M reg).barycentricDualBlock {(v : E)}).space ∧
      z ∈ ((K.barycentricDualBlock {(v : E)}).link v).space ∧ z ∉ J ∧
      z ∉ (M fr).space ∧ (∀ i, z ∉ (M (sheet i)).space) ∧
      ∀ i : Fin 2, if signs i then 0 < B (g z) i.castSucc else B (g z) i.castSucc < 0 := by
  classical
  let V := K.barycentricDualBlock {(v : E)}
  let D := (M reg).barycentricDualBlock {(v : E)}
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hvstar : (v : E) ∈ (K.closedStar v).space := by
    apply (K.closedStar v).vertices_subset_space
    change {(v : E)} ∈ K.faces ∧ insert (v : E) {(v : E)} ∈ K.faces
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (v : E)), and_self]
      using (show {(v : E)} ∈ K.faces from hvK)
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(v : E)})).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hVB : MapsTo g V.space B.source := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := mem_space_iff.mp hz
    obtain ⟨u, hu, htu⟩ := K.exists_original_star_face_of_vertex_dual_face hvK ht
    exact hsource ((K.closedStar v).convexHull_subset_space hu (htu hzt))
  have hD : D.space = V.space ∩ (M reg).space :=
    (K.barycentricDualBlock_space_inter_subcomplex (M reg) (hMK reg) {(v : E)}).symm
  obtain ⟨hhalf, hfront⟩ := hregion.resolve_left
    (fun h => disjoint_left.mp disjoint_interior_frontier (h (hsource hvstar)) hvFr)
  have hJpos (x : J) : 0 < (theta ⟨x, hJV x.property⟩ : V3) 2 := by
    have hxR : g x ∈ R := (hreg x (hVK (hJV x.property))).mp
      ((hD.subset (hJD x.property)).2)
    have hnonneg := (hmarks 2 ⟨x, hJV x.property⟩).2.mpr
      ((hhalf (g x) (hVB (hJV x.property))).mp hxR)
    refine lt_of_le_of_ne hnonneg ?_
    intro heq
    have hBzero := (hmarks 2 ⟨x, hJV x.property⟩).1.mp heq.symm
    exact disjoint_left.mp hmiss x.property
      ((hfr x (hVK (hJV x.property))).mpr
        ((hfront (g x) (hVB (hJV x.property))).mpr hBzero))
  obtain ⟨z, hzfront, hzJ, hz2, hzsigns⟩ :=
    exists_signed_chart_frontier_point_avoiding_compact_joint theta hC hcv hzero
      hJ hJV hJpos signs
  have hpos (j : Fin 3) (hy : 0 < (theta z : V3) j) : 0 < B (g z) j := by
    refine lt_of_le_of_ne ((hmarks j z).2.mp hy.le) ?_
    intro h
    exact hy.ne' ((hmarks j z).1.mpr h.symm)
  have hheight : 0 < B (g z) 2 := hpos 2 hz2
  have hzD : (z : E) ∈ D.space := by
    apply hD.superset
    exact ⟨z.property, (hreg z (hVK z.property)).mpr
      ((hhalf (g z) (hVB z.property)).mpr hheight.le)⟩
  have hstrict (i : Fin 2) :
      if signs i then 0 < B (g z) i.castSucc else B (g z) i.castSucc < 0 := by
    have hi := hzsigns i
    cases hs : signs i <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hi ⊢
    · exact lt_of_not_ge (fun h => not_le_of_gt hi ((hmarks i.castSucc z).2.mpr h))
    · exact hpos i.castSucc hi
  refine ⟨z, hzD, (hlink z).mpr hzfront, hzJ, ?_, ?_, hstrict⟩
  · intro hf
    exact hheight.ne' ((hfront (g z) (hVB z.property)).mp ((hfr z (hVK z.property)).mp hf))
  · intro i hs
    have hc := ((hsheets i (g z) (hVB z.property)).mp
      ((hsheet i z (hVK z.property)).mp hs)).2
    have hi := hstrict i
    cases hsi : signs i <;> simp only [hsi, Bool.false_eq_true, ↓reduceIte, hc] at hi <;>
      exact lt_irrefl 0 hi

end PoincareConjecture.M76.Dehn
