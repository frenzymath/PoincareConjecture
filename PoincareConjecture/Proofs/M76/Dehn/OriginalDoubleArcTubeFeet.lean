import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeFaces
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in

theorem exists_original_signed_tube_feet
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (S : Fin 2 → Set X)
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K) (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space →
      (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (p : (M arc).vertices) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (haxis : ∀ y ∈ B.source, y ∈ A ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0)
    (hsheets : ∀ i y, y ∈ B.source →
      (y ∈ S i ↔ y ∈ R ∧ B y i.castSucc = 0))
    (hregion : B.source ⊆ interior R ∨
      (∀ y ∈ B.source, y ∈ R ↔ 0 ≤ B y 2) ∧
      ∀ y ∈ B.source, y ∈ frontier R ↔ B y 2 = 0)
    (hpFr : (g p : X) ∈ frontier R) :
    let V := K.barycentricDualBlock {(p : E)}
    let D := (M reg).barycentricDualBlock {(p : E)}
    let Lp := (V.link p).space
    let Z := V.space ∩ (M arc).space
    let bZ := {z | z ∈ Z ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
    let rad := fun (i : Fin 2) (sign : Bool) =>
      {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ z ∈ (M (sheet i)).space ∧
        if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
    let foot := fun signs : Fin 2 → Bool =>
      {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
        if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
    ∃ (C0 : Set V3) (L : (Fin 3 ⊕ Fin 3) → V3 →ₗ[ℝ] ℝ)
      (theta : V.space ≃ₜ C0) (a : Fin 2 → Bool → E),
      IsCompact C0 ∧ Convex ℝ C0 ∧ (0 : V3) ∈ interior C0 ∧
      (∀ j, L j ≠ 0) ∧ C0 = {x | ∀ j, L j x ≤ 1} ∧
      theta.IsFinitePL ∧ theta.symm.IsFinitePL ∧
      (∀ z : V.space, (z : E) ∈ Lp ↔ (theta z : V3) ∈ frontier C0) ∧
      (∀ j (z : V.space),
        ((theta z : V3) j = 0 ↔ (B (g z) - B (g p)) j = 0) ∧
        (0 ≤ (theta z : V3) j ↔ 0 ≤ (B (g z) - B (g p)) j)) ∧
      IsFinitePLBallPair ℝ Z bZ ∧
      (∀ (i : Fin 2) (sign : Bool),
        let F := {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
          if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
        let O := {z | z ∈ F ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
        IsFinitePLBallPair P2 F (Z ∪ O) ∧ IsFinitePLBallPair ℝ O bZ) ∧
      (∀ (i : Fin 2) (sign : Bool),
        a i sign ≠ (p : E) ∧ IsFinitePLBallPair ℝ (rad i sign) {(p : E), a i sign} ∧
        rad i sign ∩ Lp = {a i sign} ∧
        B (g (a i sign)) i.castSucc = 0 ∧
        if sign then 0 < B (g (a i sign)) i.rev.castSucc
          else B (g (a i sign)) i.rev.castSucc < 0) ∧
      (∀ i, rad i false ∩ rad i true = {(p : E)}) ∧
      (∀ (eps delta : Bool), rad 0 eps ∩ rad 1 delta = {(p : E)}) ∧
      (∀ signs : Fin 2 → Bool,
        let U := rad 0 (signs 1) ∪ rad 1 (signs 0)
        let O := foot signs ∩ Lp
        IsFinitePLBallPair P2 (foot signs) (O ∪ U) ∧
        IsFinitePLBallPair ℝ U {a 0 (signs 1), a 1 (signs 0)} ∧
        IsFinitePLBallPair ℝ O {a 0 (signs 1), a 1 (signs 0)} ∧
        U ∩ O = {a 0 (signs 1), a 1 (signs 0)} ∧
        ∀ i, foot signs ∩ (M (sheet i)).space = rad i (signs i.rev)) ∧
      (⋃ signs : Fin 2 → Bool, foot signs) = V.space ∩ (M fr).space := by
  classical
  let V := K.barycentricDualBlock {(p : E)}
  let Lp := (V.link p).space
  let rad := fun (i : Fin 2) (sign : Bool) =>
    {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
  let foot := fun signs : Fin 2 → Bool =>
    {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
      if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
  obtain ⟨C0, L, theta, hC, hcv, h0, hL, hrep, htheta, hthetaInv,
    hlink, hmarks, hZ, hfaces, hfeet⟩ := exists_original_signed_tube_faces
      hAC hAR S K H g hg hgPL M hMK reg fr arc sheet hreg hfr harc hsheet
      p B hsource hface haxis hsheets hregion
  have hpK : (p : E) ∈ K.vertices := hMK arc p.property
  have hpA : (g p : X) ∈ A :=
    (harc p (K.vertices_subset_space hpK)).mp ((M arc).vertices_subset_space p.property)
  have hpstar : (p : E) ∈ (K.closedStar p).space := by
    apply (K.closedStar p).vertices_subset_space
    change {(p : E)} ∈ K.faces ∧ insert (p : E) {(p : E)} ∈ K.faces
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (p : E)), and_self]
      using (show {(p : E)} ∈ K.faces from hpK)
  have hpV : (p : E) ∈ V.space := by
    apply V.vertices_subset_space
    simpa only [Finset.centroid_singleton, id_eq] using
      K.faceCentroid_mem_barycentricDualBlock_vertices (show {(p : E)} ∈ K.faces from hpK)
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(p : E)})).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hVB : MapsTo (fun z => (g z : X)) V.space B.source := by
    intro z hz
    obtain ⟨v, hv, hzv⟩ := mem_space_iff.mp hz
    obtain ⟨t, ht, hvt⟩ := K.exists_original_star_face_of_vertex_dual_face hpK hv
    exact hsource ((K.closedStar p).convexHull_subset_space ht (hvt hzv))
  obtain ⟨hhalf, hfront⟩ := hregion.resolve_left
    (fun h => disjoint_left.mp disjoint_interior_frontier (h (hsource hpstar)) hpFr)
  have hBzero : B (g p) = (0 : V3) := by
    have hz := ((haxis (g p) (hsource hpstar)).mp hpA).2
    ext j
    fin_cases j
    · exact hz.1
    · exact hz.2
    · exact (hfront (g p) (hsource hpstar)).mp hpFr
  have hmark (j : Fin 3) (z : V.space) :
      ((theta z : V3) j = 0 ↔ B (g z) j = 0) ∧
      (0 ≤ (theta z : V3) j ↔ 0 ≤ B (g z) j) := by
    simpa only [hBzero, sub_zero] using hmarks j z
  have hfrtheta (z : V.space) : (z : E) ∈ (M fr).space ↔ (theta z : V3) 2 = 0 :=
    (hfr z (hVK z.property)).trans
      ((hfront (g z) (hVB z.property)).trans (hmark 2 z).1.symm)
  have hsheettheta (i : Fin 2) (z : V.space) (hzFr : (z : E) ∈ (M fr).space) :
      (z : E) ∈ (M (sheet i)).space ↔ (theta z : V3) i.castSucc = 0 := by
    have hzR : (g z : X) ∈ R := (hhalf (g z) (hVB z.property)).mpr
      ((hfront (g z) (hVB z.property)).mp ((hfr z (hVK z.property)).mp hzFr)).ge
    rw [hsheet i z (hVK z.property), hsheets i (g z) (hVB z.property)]
    simp only [hzR, true_and, (hmark i.castSucc z).1]
  have hside (sign : Bool) (j : Fin 3) (z : V.space) :
      (if sign then 0 ≤ (theta z : V3) j else (theta z : V3) j ≤ 0) ↔
        if sign then 0 ≤ B (g z) j else B (g z) j ≤ 0 := by
    cases sign
    · change (theta z : V3) j ≤ 0 ↔ B (g z) j ≤ 0
      constructor
      · intro hn
        by_contra hp
        have hp' := lt_of_not_ge hp
        exact hp'.ne' ((hmark j z).1.mp
          (le_antisymm hn ((hmark j z).2.mpr hp'.le)))
      · intro hn
        by_contra hp
        have hp' := lt_of_not_ge hp
        exact hp'.ne' ((hmark j z).1.mpr
          (le_antisymm hn ((hmark j z).2.mp hp'.le)))
    · exact (hmark j z).2
  have htheta0 : (theta ⟨p, hpV⟩ : V3) = 0 := by
    ext j
    apply (hmark j ⟨p, hpV⟩).1.mpr
    rw [hBzero]
    rfl
  obtain ⟨q, hq, hqval⟩ := hthetaInv
  have hqin (x : V3) (hx : x ∈ C0) : q x ∈ V.space := by
    rw [← hqval ⟨x, hx⟩]
    exact (theta.symm ⟨x, hx⟩).property
  have hforward (x : V3) (hx : x ∈ C0) : (theta ⟨q x, hqin x hx⟩ : V3) = x := by
    have he : (⟨q x, hqin x hx⟩ : V.space) = theta.symm ⟨x, hx⟩ :=
      Subtype.ext (hqval ⟨x, hx⟩).symm
    rw [he, theta.apply_symm_apply]
  have hback (z : V.space) : q (theta z) = z := by
    rw [← hqval (theta z), theta.symm_apply_apply]
  have hq0 : q 0 = (p : E) := by rw [← htheta0]; exact hback ⟨p, hpV⟩
  have hqi : InjOn q C0 := by
    intro x hx y hy he
    have he' : (⟨q x, hqin x hx⟩ : V.space) = ⟨q y, hqin y hy⟩ := Subtype.ext he
    have h := congrArg (fun z : V.space => (theta z : V3)) he'
    exact (hforward x hx).symm.trans (h.trans (hforward y hy))
  have hqfront (x : V3) (hx : x ∈ C0) : q x ∈ Lp ↔ x ∈ frontier C0 := by
    rw [hlink ⟨q x, hqin x hx⟩, hforward x hx]

  have hray (i : Fin 2) (sign : Bool) : ∃ b : V3,
      b ∈ frontier C0 ∧ b ≠ 0 ∧
      IsFinitePLBallPair ℝ (segment ℝ 0 b) {0, b} ∧
      segment ℝ 0 b = {x | x ∈ C0 ∧ x i.castSucc = 0 ∧ x 2 = 0 ∧
        if sign then 0 ≤ x i.rev.castSucc else x i.rev.castSucc ≤ 0} ∧
      segment ℝ 0 b ∩ frontier C0 = {b} := by
    let a : ℝ →ᴬ[ℝ] V3 := (ContinuousLinearMap.pi fun j : Fin 3 =>
      if j = i.rev.castSucc then
        (if sign then 1 else -1 : ℝ) • ContinuousLinearMap.id ℝ ℝ else 0).toContinuousAffineMap
    let r : V3 →ᴬ[ℝ] ℝ :=
      ((if sign then 1 else -1 : ℝ) • ContinuousLinearMap.proj i.rev.castSucc).toContinuousAffineMap
    have hleft (t : ℝ) : r (a t) = t := by cases sign <;> simp [a, r]
    have ha0 : a 0 = 0 := by ext j; simp [a]
    have har (x : V3) : a (r x) = x ↔ x i.castSucc = 0 ∧ x 2 = 0 := by
      fin_cases i <;> cases sign <;> simp [a, r, funext_iff, Fin.forall_fin_succ, eq_comm]
    have hrpos (x : V3) : 0 ≤ r x ↔
        if sign then 0 ≤ x i.rev.castSucc else x i.rev.castSucc ≤ 0 := by
      cases sign <;> simp [r]
    have hclosed : IsClosed (range a) := by
      have he : range a = {x | a (r x) = x} := by
        ext x
        exact ⟨fun ⟨t, ht⟩ => by
          change a (r x) = x
          rw [← ht, hleft t], fun h => ⟨r x, h⟩⟩
      rw [he]
      exact isClosed_eq (a.continuous.comp r.continuous) continuous_id
    have him : r '' (C0 ∩ range a) = a ⁻¹' C0 := by
      ext t
      constructor
      · rintro ⟨x, ⟨hx, u, rfl⟩, rfl⟩
        change a (r (a u)) ∈ C0
        rwa [hleft]
      · exact fun ht => ⟨a t, ⟨ht, mem_range_self t⟩, hleft t⟩
    have hc : IsCompact (a ⁻¹' C0) := him ▸ (hC.inter_right hclosed).image r.continuous
    have hcv' : Convex ℝ (a ⁻¹' C0) := hcv.affine_preimage a.toAffineMap
    have h0' : (0 : ℝ) ∈ interior (a ⁻¹' C0) := by
      apply preimage_interior_subset_interior_preimage a.continuous
      change a 0 ∈ interior C0
      rwa [ha0]
    let lo := sInf (a ⁻¹' C0)
    let hi := sSup (a ⁻¹' C0)
    have hI : a ⁻¹' C0 = Icc lo hi :=
      eq_Icc_of_connected_compact (hcv'.isConnected ⟨0, interior_subset h0'⟩) hc
    have hh : lo < 0 ∧ 0 < hi := by
      rw [hI, interior_Icc] at h0'
      exact h0'
    have hseg : a '' Icc 0 hi = segment ℝ 0 (a hi) := by
      rw [← segment_eq_Icc hh.2.le]
      have he : a '' segment ℝ 0 hi = segment ℝ (a 0) (a hi) :=
        image_segment ℝ a.toAffineMap 0 hi
      simpa only [ha0] using he
    have hbody : segment ℝ 0 (a hi) = {x | x ∈ C0 ∧ x i.castSucc = 0 ∧ x 2 = 0 ∧
        if sign then 0 ≤ x i.rev.castSucc else x i.rev.castSucc ≤ 0} := by
      rw [← hseg]
      ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        have haC : a t ∈ C0 := hI.symm.subset ⟨hh.1.le.trans ht.1, ht.2⟩
        have haz := (har (a t)).mp (by rw [hleft])
        exact ⟨haC, haz.1, haz.2, (hrpos (a t)).mp (by
          simpa only [hleft t] using ht.1)⟩
      · rintro ⟨hx, hz, hz2, hs⟩
        have harx := (har x).mpr ⟨hz, hz2⟩
        refine ⟨r x, ⟨(hrpos x).mpr hs, ?_⟩, harx⟩
        have ht : r x ∈ a ⁻¹' C0 := by change a (r x) ∈ C0; rwa [harx]
        exact (hI.subset ht).2
    have hfront : a ⁻¹' frontier C0 = ({lo, hi} : Set ℝ) := by
      rw [← a.frontier_preimage_convex hC.isClosed hcv ⟨0, ha0.symm ▸ h0⟩,
        hI, frontier_Icc (hh.1.trans hh.2).le]
    have hhi : a hi ∈ frontier C0 := hfront.symm.subset (Or.inr rfl)
    have hne : a hi ≠ 0 := by
      intro he
      have ht := congrArg r he
      rw [← ha0, hleft, hleft] at ht
      exact hh.2.ne' ht
    have hb := isFinitePLBallPair_affine_interval hh.2 a
      (show Function.LeftInverse r a from hleft).injective.injOn
    refine ⟨a hi, hhi, hne, ?_, hbody, ?_⟩
    · simpa only [hseg, ha0] using hb
    · apply Subset.antisymm
      · rintro x ⟨hx, hxf⟩
        obtain ⟨t, ht, rfl⟩ := hseg.symm.subset hx
        rcases hfront.subset hxf with htlo | hthi
        · exact (not_le_of_gt hh.1 (htlo ▸ ht.1)).elim
        · exact congrArg a hthi
      · rintro x rfl
        exact ⟨right_mem_segment ℝ _ _, hhi⟩
  choose b hb using hray
  let a : Fin 2 → Bool → E := fun i sign => q (b i sign)
  have hbC (i : Fin 2) (sign : Bool) : b i sign ∈ C0 :=
    hC.isClosed.closure_eq.subset (hb i sign).1.1
  have hsegC (i : Fin 2) (sign : Bool) : segment ℝ 0 (b i sign) ⊆ C0 :=
    fun _ hx => ((hb i sign).2.2.2.1.subset hx).1
  have himage (i : Fin 2) (sign : Bool) : q '' segment ℝ 0 (b i sign) = rad i sign := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxC, hxi, hx2, hxs⟩ := (hb i sign).2.2.2.1.subset hx
      have hzFr : q x ∈ (M fr).space := (hfrtheta ⟨q x, hqin x hxC⟩).mpr
        (by rwa [hforward x hxC])
      refine ⟨hqin x hxC, hzFr, (hsheettheta i ⟨q x, hqin x hxC⟩ hzFr).mpr ?_, ?_⟩
      · rwa [hforward x hxC]
      · apply (hside sign i.rev.castSucc ⟨q x, hqin x hxC⟩).mp
        rwa [hforward x hxC]
    · rintro ⟨hzV, hzFr, hzS, hzs⟩
      refine ⟨theta ⟨z, hzV⟩, (hb i sign).2.2.2.1.symm.subset ?_, hback ⟨z, hzV⟩⟩
      exact ⟨(theta ⟨z, hzV⟩).property, (hsheettheta i ⟨z, hzV⟩ hzFr).mp hzS,
        (hfrtheta ⟨z, hzV⟩).mp hzFr, (hside sign i.rev.castSucc ⟨z, hzV⟩).mpr hzs⟩
  have hrad (i : Fin 2) (sign : Bool) :
      a i sign ≠ (p : E) ∧ IsFinitePLBallPair ℝ (rad i sign) {(p : E), a i sign} ∧
      rad i sign ∩ Lp = {a i sign} ∧
      B (g (a i sign)) i.castSucc = 0 ∧
      if sign then 0 < B (g (a i sign)) i.rev.castSucc
        else B (g (a i sign)) i.rev.castSucc < 0 := by
    have han : a i sign ≠ (p : E) := fun he => (hb i sign).2.1
      (hqi (hbC i sign) (interior_subset h0) (he.trans hq0.symm))
    have hball := (hb i sign).2.2.1.image_of_subset hq (hsegC i sign) hqi
    have hball' : IsFinitePLBallPair ℝ (rad i sign) {(p : E), a i sign} := by
      simpa only [himage, image_pair, hq0] using hball
    have haR : a i sign ∈ rad i sign := hball'.1 (Or.inr rfl)
    have haV : a i sign ∈ V.space := haR.1
    have hazi : B (g (a i sign)) i.castSucc = 0 :=
      (hmark i.castSucc ⟨a i sign, haV⟩).1.mp
        ((hsheettheta i ⟨a i sign, haV⟩ haR.2.1).mp haR.2.2.1)
    have haz2 : B (g (a i sign)) 2 = 0 :=
      (hmark 2 ⟨a i sign, haV⟩).1.mp ((hfrtheta ⟨a i sign, haV⟩).mp haR.2.1)
    have hother : B (g (a i sign)) i.rev.castSucc ≠ 0 := by
      intro hz
      have he : (theta ⟨a i sign, haV⟩ : V3) = 0 := by
        ext j
        apply (hmark j ⟨a i sign, haV⟩).1.mpr
        fin_cases i <;> fin_cases j <;> assumption
      have he' : theta ⟨a i sign, haV⟩ = theta ⟨p, hpV⟩ := Subtype.ext (he.trans htheta0.symm)
      exact han (congrArg Subtype.val (theta.injective he'))
    refine ⟨han, hball', ?_, hazi, ?_⟩
    · apply Subset.antisymm
      · rintro z ⟨hz, hzL⟩
        obtain ⟨x, hx, rfl⟩ := (himage i sign).symm.subset hz
        have he := (hb i sign).2.2.2.2.subset
          ⟨hx, (hqfront x (hsegC i sign hx)).mp hzL⟩
        exact congrArg q he
      · rintro z rfl
        exact ⟨haR, (hqfront _ (hbC i sign)).mpr (hb i sign).1⟩
    · cases sign
      · exact lt_of_le_of_ne haR.2.2.2 hother
      · exact lt_of_le_of_ne haR.2.2.2 hother.symm
  have hpRad (i : Fin 2) (sign : Bool) : (p : E) ∈ rad i sign :=
    (hrad i sign).2.1.1 (Or.inl rfl)
  have hcenter {z : E} (hz : z ∈ V.space) (hzF : z ∈ (M fr).space)
      (hz0 : z ∈ (M (sheet 0)).space) (hz1 : z ∈ (M (sheet 1)).space) : z = p := by
    have he : (theta ⟨z, hz⟩ : V3) = 0 := by
      ext j
      fin_cases j
      · exact (hsheettheta 0 ⟨z, hz⟩ hzF).mp hz0
      · exact (hsheettheta 1 ⟨z, hz⟩ hzF).mp hz1
      · exact (hfrtheta ⟨z, hz⟩).mp hzF
    exact congrArg Subtype.val (theta.injective (Subtype.ext (he.trans htheta0.symm)))
  have hcross (eps delta : Bool) : rad 0 eps ∩ rad 1 delta = {(p : E)} := by
    apply Subset.antisymm
    · exact fun z hz => hcenter hz.1.1 hz.1.2.1 hz.1.2.2.1 hz.2.2.2.1
    · rintro z rfl
      exact ⟨hpRad 0 eps, hpRad 1 delta⟩
  have hopp (i : Fin 2) : rad i false ∩ rad i true = {(p : E)} := by
    apply Subset.antisymm
    · rintro z ⟨hn, hp⟩
      have ho : B (g z) i.rev.castSucc = 0 := le_antisymm hn.2.2.2 hp.2.2.2
      have hother : z ∈ (M (sheet i.rev)).space :=
        (hsheettheta i.rev ⟨z, hn.1⟩ hn.2.1).mpr ((hmark _ ⟨z, hn.1⟩).1.mpr ho)
      fin_cases i
      · exact hcenter hn.1 hn.2.1 hn.2.2.1 hother
      · exact hcenter hn.1 hn.2.1 hother hn.2.2.1
    · rintro z rfl
      exact ⟨hpRad i false, hpRad i true⟩
  have hFsheet (signs : Fin 2 → Bool) (i : Fin 2) :
      foot signs ∩ (M (sheet i)).space = rad i (signs i.rev) := by
    apply Subset.antisymm
    · exact fun z hz => ⟨hz.1.1, hz.1.2.1, hz.2, hz.1.2.2 i.rev⟩
    · rintro z ⟨hz, hzF, hzS, hzs⟩
      have hzi : B (g z) i.castSucc = 0 :=
        (hmark _ ⟨z, hz⟩).1.mp ((hsheettheta i ⟨z, hz⟩ hzF).mp hzS)
      refine ⟨⟨hz, hzF, ?_⟩, hzS⟩
      intro j
      by_cases hj : j = i
      · subst j
        cases signs i <;> simp [hzi]
      · have hj' : j = i.rev := by
          fin_cases i <;> fin_cases j <;> first | rfl | exact (hj rfl).elim
        simpa only [hj'] using hzs
  refine ⟨C0, L, theta, a, hC, hcv, h0, hL, hrep, htheta, htheta.symm,
    hlink, hmarks, hZ, hfaces, hrad, hopp, hcross, ?_, ?_⟩
  · intro signs
    let U := rad 0 (signs 1) ∪ rad 1 (signs 0)
    let O := foot signs ∩ Lp
    have hUQ : U ⊆ foot signs := by
      rintro z (hz | hz)
      · exact ((hFsheet signs 0).symm.subset hz).1
      · exact ((hFsheet signs 1).symm.subset hz).1
    have hQ : IsFinitePLBallPair P2 (foot signs) (O ∪ U) := by
      convert hfeet hpFr signs using 1
      ext z
      constructor
      · rintro (hz | hz)
        · exact ⟨hz.1, Or.inl hz.2⟩
        · rcases hz with hz | hz
          · have h := (hFsheet signs 0).symm.subset hz
            exact ⟨h.1, Or.inr (Or.inl h.2)⟩
          · have h := (hFsheet signs 1).symm.subset hz
            exact ⟨h.1, Or.inr (Or.inr h.2)⟩
      · rintro ⟨hz, hzL | hzS | hzS⟩
        · exact Or.inl ⟨hz, hzL⟩
        · exact Or.inr (Or.inl ((hFsheet signs 0).subset ⟨hz, hzS⟩))
        · exact Or.inr (Or.inr ((hFsheet signs 1).subset ⟨hz, hzS⟩))
    have hcoordcross : segment ℝ (b 0 (signs 1)) 0 ∩
        segment ℝ 0 (b 1 (signs 0)) = ({0} : Set V3) := by
      apply Subset.antisymm
      · intro x hx
        have hx0 := (hb 0 (signs 1)).2.2.2.1.subset (by
          simpa only [segment_symm (𝕜 := ℝ) (b 0 (signs 1)) 0] using hx.1)
        have hx1 := (hb 1 (signs 0)).2.2.2.1.subset hx.2
        change x = 0
        ext j
        fin_cases j
        · exact hx0.2.1
        · exact hx1.2.1
        · exact hx0.2.2.1
      · rintro x rfl
        exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
    have hUball0 := isFinitePLBallPair_two_segments
      (hb 0 (signs 1)).2.1 (hb 1 (signs 0)).2.1.symm hcoordcross
    have hUball : IsFinitePLBallPair ℝ U {a 0 (signs 1), a 1 (signs 0)} := by
      have hsub : segment ℝ (b 0 (signs 1)) 0 ∪ segment ℝ 0 (b 1 (signs 0)) ⊆ C0 := by
        rintro x (hx | hx)
        · exact hsegC 0 _ (by rwa [segment_symm] at hx)
        · exact hsegC 1 _ hx
      have hb' := hUball0.image_of_subset hq hsub hqi
      simpa only [image_union, segment_symm (𝕜 := ℝ) (b 0 (signs 1)) 0,
        himage, image_pair] using hb'
    have hends : a 0 (signs 1) ≠ a 1 (signs 0) := by
      intro he
      have hx : a 0 (signs 1) ∈ rad 0 (signs 1) ∩ rad 1 (signs 0) :=
        ⟨(hrad 0 _).2.1.1 (Or.inr rfl), he.symm ▸ (hrad 1 _).2.1.1 (Or.inr rfl)⟩
      exact (hrad 0 _).1 ((hcross _ _).subset hx)
    have hUO : U ∩ O = {a 0 (signs 1), a 1 (signs 0)} := by
      apply Subset.antisymm
      · rintro z ⟨hz | hz, _, hzL⟩
        · exact Or.inl ((hrad 0 _).2.2.1.subset ⟨hz, hzL⟩)
        · exact Or.inr ((hrad 1 _).2.2.1.subset ⟨hz, hzL⟩)
      · rintro z (rfl | rfl)
        · have hz := (hrad 0 (signs 1)).2.2.1.symm.subset (mem_singleton _)
          exact ⟨Or.inl hz.1, hUQ (Or.inl hz.1), hz.2⟩
        · have hz := (hrad 1 (signs 0)).2.2.1.symm.subset (mem_singleton _)
          exact ⟨Or.inr hz.1, hUQ (Or.inr hz.1), hz.2⟩
    obtain ⟨O', hO', hwhole, hinter⟩ :=
      hQ.exists_boundary_arc_complement hUball subset_union_right hends
    have hOeq : O' = O := by
      apply Subset.antisymm
      · intro z hz
        by_cases hzU : z ∈ U
        · exact (hUO.symm.subset (hinter.subset ⟨hzU, hz⟩)).2
        · exact (hwhole.subset (Or.inr hz)).resolve_right hzU
      · intro z hz
        by_cases hzU : z ∈ U
        · exact hO'.1 (hUO.subset ⟨hzU, hz⟩)
        · exact (hwhole.symm.subset (Or.inl hz)).resolve_left hzU
    exact ⟨hQ, hUball, by simpa only [hOeq] using hO', hUO, hFsheet signs⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨signs, hz⟩ := mem_iUnion.mp hz
      exact ⟨hz.1, hz.2.1⟩
    · rintro ⟨hz, hzF⟩
      let signs : Fin 2 → Bool := fun i => decide (0 ≤ B (g z) i.castSucc)
      refine mem_iUnion.mpr ⟨signs, hz, hzF, ?_⟩
      intro i
      by_cases hi : 0 ≤ B (g z) i.castSucc
      · simp [signs, hi]
      · simp [signs, hi, (lt_of_not_ge hi).le]

end PoincareConjecture.M76.Dehn
