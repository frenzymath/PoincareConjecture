import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeModel
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.Wall.OriginalInteriorVertexDual
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalHalfBlocks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarMarkedCutCharts
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineSectionFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in

theorem exists_original_signed_tube_faces
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
      ∀ y ∈ B.source, y ∈ frontier R ↔ B y 2 = 0) :
    let V := K.barycentricDualBlock {(p : E)}
    let D := (M reg).barycentricDualBlock {(p : E)}
    let Z := V.space ∩ (M arc).space
    let bZ := {z | z ∈ Z ∧ (z ∈ (V.link p).space ∨ z ∈ (M fr).space)}
    ∃ (C0 : Set V3) (L : (Fin 3 ⊕ Fin 3) → V3 →ₗ[ℝ] ℝ)
      (theta : V.space ≃ₜ C0),
      IsCompact C0 ∧ Convex ℝ C0 ∧ (0 : V3) ∈ interior C0 ∧
      (∀ j, L j ≠ 0) ∧ C0 = {x | ∀ j, L j x ≤ 1} ∧
      theta.IsFinitePL ∧ theta.symm.IsFinitePL ∧
      (∀ z : V.space, (z : E) ∈ (V.link p).space ↔ (theta z : V3) ∈ frontier C0) ∧
      (∀ j (z : V.space),
        ((theta z : V3) j = 0 ↔ (B (g z) - B (g p)) j = 0) ∧
        (0 ≤ (theta z : V3) j ↔ 0 ≤ (B (g z) - B (g p)) j)) ∧
      IsFinitePLBallPair ℝ Z bZ ∧
      (∀ (i : Fin 2) (sign : Bool),
        let F := {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
          if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
        let O := {z | z ∈ F ∧ (z ∈ (V.link p).space ∨ z ∈ (M fr).space)}
        IsFinitePLBallPair P2 F (Z ∪ O) ∧ IsFinitePLBallPair ℝ O bZ) ∧
      ((g p : X) ∈ frontier R → ∀ signs : Fin 2 → Bool,
        let F := {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
          if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
        IsFinitePLBallPair P2 F
          {z | z ∈ F ∧ (z ∈ (V.link p).space ∨
            z ∈ (M (sheet 0)).space ∨ z ∈ (M (sheet 1)).space)}) := by
  classical
  let V := K.barycentricDualBlock {(p : E)}
  let D := (M reg).barycentricDualBlock {(p : E)}
  let Z := V.space ∩ (M arc).space
  let bZ := {z | z ∈ Z ∧ (z ∈ (V.link p).space ∨ z ∈ (M fr).space)}
  have hpK : (p : E) ∈ K.vertices := hMK arc p.property
  have hpA : (g p : X) ∈ A :=
    (harc p (K.vertices_subset_space hpK)).mp ((M arc).vertices_subset_space p.property)
  have hpstar : (p : E) ∈ (K.closedStar p).space := by
    apply (K.closedStar p).vertices_subset_space
    change {(p : E)} ∈ K.faces ∧ insert (p : E) {(p : E)} ∈ K.faces
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (p : E)), and_self]
      using (show {(p : E)} ∈ K.faces from hpK)
  have hpzero := ((haxis (g p) (hsource hpstar)).mp hpA).2
  let J := K.barycentricSubdivision
  have hJs : J.space = K.space := K.barycentricSubdivision_isSubdivision.space_eq
  let HJ : C ≃ₜ J.space := H.trans (Homeomorph.setCongr hJs.symm)
  have hgJ (z : J.space) : (g z : X) = (HJ.symm z : X) := hg ⟨z, hJs.subset z.property⟩
  have hpJ : (p : E) ∈ J.vertices := K.barycentricSubdivision_isSubdivision.vertices_subset hpK
  have hVeq : V = J.closedStar p := K.barycentricDualBlock_singleton_eq_closedStar hpK
  have hVfin : V.faces.Finite :=
    K.barycentricSubdivision_finite.subset (K.barycentricDualBlock_le {(p : E)})
  have hVK : V.space ⊆ K.space := fun _ hz =>
    hJs.subset (space_subset_of_le (K.barycentricDualBlock_le {(p : E)}) hz)
  have hcontain : ∀ s ∈ V.faces, ∃ t ∈ (K.closedStar p).faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) :=
    fun _ hs => K.exists_original_star_face_of_vertex_dual_face hpK hs
  have hVsource : MapsTo (fun z => (g z : X)) V.space B.source := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := mem_space_iff.mp hz
    obtain ⟨t, ht, hst⟩ := hcontain s hs
    exact hsource ((K.closedStar p).convexHull_subset_space ht (hst hzs))
  have hVp : (p : E) ∈ V.vertices := by
    rw [hVeq]
    change {(p : E)} ∈ J.faces ∧ insert (p : E) {(p : E)} ∈ J.faces
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (p : E)), and_self]
      using (show {(p : E)} ∈ J.faces from hpJ)
  have hVself : V.closedStar p = V := by
    rw [hVeq]
    ext s
    change ((s ∈ J.faces ∧ insert (p : E) s ∈ J.faces) ∧
      insert (p : E) s ∈ J.faces ∧ insert (p : E) (insert (p : E) s) ∈ J.faces) ↔
      s ∈ J.faces ∧ insert (p : E) s ∈ J.faces
    simp only [Finset.insert_idem, and_self, and_assoc]
  have hnb := J.exists_original_open_neighborhood_inside_closedStar
    K.barycentricSubdivision_finite HJ g hgJ hpJ (hAC hpA) B (hVeq ▸ hVsource)
  rw [← hVeq] at hnb
  obtain ⟨hinj, _, hint⟩ := hnb
  let f : E → V3 := fun z => B (g z) - B (g p)
  let shift : V3 →ᴬ[ℝ] V3 :=
    ContinuousAffineMap.id ℝ V3 - ContinuousAffineMap.const ℝ V3 (B (g p))
  have hf : V.AffineOnFaces f := (hface.of_face_containment hcontain).postcomp shift
  have hfi : InjOn f V.space := by
    intro x hx y hy hxy
    apply hinj hx hy
    simpa only [f, sub_add_cancel] using congrArg (fun v : V3 => v + B (g p)) hxy
  have hfp : f p = 0 := sub_self _
  have hfint : (0 : V3) ∈ interior (f '' V.space) := by
    have himage : f '' V.space = (Homeomorph.subRight (B (g p))) ''
        ((fun z => B (g z)) '' V.space) := by rw [image_image]; rfl
    rw [himage, ← Homeomorph.image_interior]
    exact ⟨B (g p), hint, sub_self _⟩
  have hcoord (z : E) (i : Fin 2) : f z i.castSucc = B (g z) i.castSucc := by
    fin_cases i <;> simp [f, hpzero.1, hpzero.2]
  have hcoord0 (z : E) : f z 0 = B (g z) 0 := hcoord z 0
  have hcoord1 (z : E) : f z 1 = B (g z) 1 := hcoord z 1
  let endpoint : Bool := decide ((g p : X) ∈ frontier R)
  have hregions (z : E) (hz : z ∈ V.space) :
      (z ∈ (M reg).space ↔ (endpoint = true → 0 ≤ f z 2)) ∧
      (z ∈ (M fr).space ↔ endpoint = true ∧ f z 2 = 0) := by
    by_cases hpF : (g p : X) ∈ frontier R
    · obtain ⟨hhalf, hfront⟩ := hregion.resolve_left
        (fun h => disjoint_left.mp disjoint_interior_frontier (h (hsource hpstar)) hpF)
      have hp2 : B (g p) 2 = 0 := (hfront _ (hsource hpstar)).mp hpF
      simp only [hreg z (hVK hz), hfr z (hVK hz), hhalf _ (hVsource hz),
        hfront _ (hVsource hz), endpoint, hpF, decide_true, true_implies, true_and]
      simp [f, hp2]
    · have hpnot : (p : E) ∉ (M fr).vertices := fun h => hpF
        ((hfr p (K.vertices_subset_space hpK)).mp ((M fr).vertices_subset_space h))
      have hfoot : V.space ∩ (M fr).space = ∅ := by
        rw [K.barycentricDualBlock_space_inter_subcomplex (M fr) (hMK fr) {(p : E)}]
        exact (M fr).barycentricDualBlock_space_eq_empty_of_not_face
          (Finset.singleton_nonempty (p : E)) hpnot
      have hball := isFinitePLBallPair_original_interior_vertex_dual K H g hg
        hpK (hAC hpA) B hsource hface
      have hconn := hball.isConnected.isPreconnected.image
        (fun z => (g z : X)) (hgPL.continuousOn.mono hVK)
      have hdis : Disjoint (frontier (interior R)) ((fun z => (g z : X)) '' V.space) := by
        apply disjoint_left.mpr
        rintro _ hfront ⟨w, hw, rfl⟩
        exact (hfoot.subset ⟨hw, (hfr w (hVK hw)).mpr (frontier_interior_subset hfront)⟩).elim
      have hpR : (g p : X) ∈ interior R := by
        by_contra hn
        exact hpF ⟨subset_closure (hAR hpA), hn⟩
      have hzR := hconn.m76_subset_of_disjoint_frontier isOpen_interior hdis
        ⟨g p, mem_image_of_mem _ (V.vertices_subset_space hVp), hpR⟩ (mem_image_of_mem _ hz)
      have hzreg := (hreg z (hVK hz)).mpr (interior_subset hzR)
      have hzfr : z ∉ (M fr).space := fun h =>
        disjoint_left.mp disjoint_interior_frontier hzR ((hfr z (hVK hz)).mp h)
      simp [endpoint, hpF, hzreg, hzfr]
  have hsheetf (i : Fin 2) (z : E) (hz : z ∈ V.space) :
      z ∈ (M (sheet i)).space ↔ (endpoint = true → 0 ≤ f z 2) ∧ f z i.castSucc = 0 := by
    rw [hsheet i z (hVK hz), hsheets i (g z) (hVsource hz),
      ← hreg z (hVK hz), (hregions z hz).1, hcoord]
  have harcf (z : E) (hz : z ∈ V.space) : z ∈ (M arc).space ↔
      (endpoint = true → 0 ≤ f z 2) ∧ f z 0 = 0 ∧ f z 1 = 0 := by
    rw [harc z (hVK hz), haxis (g z) (hVsource hz),
      ← hreg z (hVK hz), (hregions z hz).1]
    simp only [f, Pi.sub_apply, hpzero.1, hpzero.2, sub_zero]
  have hDspace : D.space = V.space ∩ (M reg).space :=
    (K.barycentricDualBlock_space_inter_subcomplex (M reg) (hMK reg) {(p : E)}).symm
  let I := hf.embeddedImage hfi
  have hI : I.faces.Finite := hf.embeddedImage_finite hfi hVfin
  have hIs : I.space = f '' V.space := hf.embeddedImage_space hfi
  have hIstar : (I.closedStar 0).space = f '' V.space := by
    simpa only [hfp, hVself] using hf.embeddedImage_closedStar_space hfi hVp
  have hIlink : (I.link 0).space = f '' (V.link p).space := by
    simpa only [hfp] using hf.embeddedImage_link_space hfi hVp
  have hzI : (0 : V3) ∈ I.vertices := by
    rw [hf.embeddedImage_vertices hfi]
    exact ⟨p, hVp, hfp⟩
  obtain ⟨C0, L, T, hC, hcv, hC0, hL, hrep, hT, hTlink, hcuts⟩ :=
    I.exists_finitePL_closedStar_chart_preserving_cut_family hI hzI
      (hIs.symm ▸ hfint) (ContinuousLinearEquiv.refl ℝ V3)
      (fun j : Fin 3 => LinearMap.proj j)
  let u : V.space ≃ₜ (I.closedStar 0).space :=
    (hf.homeomorphImage hVfin hfi).trans (Homeomorph.setCongr hIstar.symm)
  have hu : u.IsFinitePL := ⟨f, hf.finitePiecewiseAffineOn hVfin, fun _ => rfl⟩
  let theta : V.space ≃ₜ C0 := u.trans T
  have htheta : theta.IsFinitePL := hu.trans hT
  have hlinksub : (V.link p).space ⊆ V.space :=
    space_subset_of_le (show V.link p ≤ V from fun _ hs => hs.1)
  have hlink (z : V.space) : (z : E) ∈ (V.link p).space ↔ (theta z : V3) ∈ frontier C0 := by
    have hfz : f z ∈ (I.link 0).space ↔ (z : E) ∈ (V.link p).space := by
      rw [hIlink]
      exact ⟨fun ⟨w, hw, he⟩ => hfi (hlinksub hw) z.property he ▸ hw,
        fun hz => mem_image_of_mem f hz⟩
    exact hfz.symm.trans (hTlink (u z))
  have hmarks (j : Fin 3) (z : V.space) :
      ((theta z : V3) j = 0 ↔ f z j = 0) ∧
      (0 ≤ (theta z : V3) j ↔ 0 ≤ f z j) := hcuts j (u z)
  refine ⟨C0, L, theta, hC, hcv, hC0, hL, hrep, htheta, htheta.symm,
    hlink, hmarks, ?_⟩
  obtain ⟨q, hq, hqval⟩ := htheta.symm
  have hqin (x : V3) (hx : x ∈ C0) : q x ∈ V.space := by
    rw [← hqval ⟨x, hx⟩]
    exact (theta.symm ⟨x, hx⟩).property
  have hforward (x : V3) (hx : x ∈ C0) : (theta ⟨q x, hqin x hx⟩ : V3) = x := by
    have he : (⟨q x, hqin x hx⟩ : V.space) = theta.symm ⟨x, hx⟩ :=
      Subtype.ext (hqval ⟨x, hx⟩).symm
    rw [he, theta.apply_symm_apply]
  have hback (z : V.space) : q (theta z) = z := by
    rw [← hqval (theta z), theta.symm_apply_apply]
  have hqi : InjOn q C0 := by
    intro x hx y hy he
    have he' : (⟨q x, hqin x hx⟩ : V.space) = ⟨q y, hqin y hy⟩ := Subtype.ext he
    have ht := congrArg (fun z : V.space => (theta z : V3)) he'
    exact (hforward x hx).symm.trans (ht.trans (hforward y hy))
  have hqzero (x : V3) (hx : x ∈ C0) (j : Fin 3) : x j = 0 ↔ f (q x) j = 0 := by
    have h := (hmarks j ⟨q x, hqin x hx⟩).1
    rwa [hforward x hx] at h
  have hqpos (x : V3) (hx : x ∈ C0) (j : Fin 3) : 0 ≤ x j ↔ 0 ≤ f (q x) j := by
    have h := (hmarks j ⟨q x, hqin x hx⟩).2
    rwa [hforward x hx] at h
  have hqside (x : V3) (hx : x ∈ C0) (j : Fin 3) (b : Bool) :
      (if b then 0 ≤ x j else x j ≤ 0) ↔
        (if b then 0 ≤ f (q x) j else f (q x) j ≤ 0) := by
    cases b
    · change x j ≤ 0 ↔ f (q x) j ≤ 0
      constructor
      · intro hn
        by_contra hp
        have hz := le_antisymm hn ((hqpos x hx j).mpr (le_of_lt (lt_of_not_ge hp)))
        exact (lt_of_not_ge hp).ne' ((hqzero x hx j).mp hz)
      · intro hn
        by_contra hp
        have hz := le_antisymm hn ((hqpos x hx j).mp (le_of_lt (lt_of_not_ge hp)))
        exact (lt_of_not_ge hp).ne' ((hqzero x hx j).mpr hz)
    · exact hqpos x hx j
  have hqfront (x : V3) (hx : x ∈ C0) : x ∈ frontier C0 ↔ q x ∈ (V.link p).space := by
    rw [hlink ⟨q x, hqin x hx⟩, hforward x hx]
  have himage (P : V3 → Prop) (Q : E → Prop)
      (hPQ : ∀ x ∈ C0, P x ↔ Q (q x)) :
      q '' {x | x ∈ C0 ∧ P x} = {z | z ∈ V.space ∧ Q z} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hqin x hx.1, (hPQ x hx.1).mp hx.2⟩
    · rintro ⟨hz, hQ⟩
      refine ⟨theta ⟨z, hz⟩, ⟨(theta ⟨z, hz⟩).property, ?_⟩, hback ⟨z, hz⟩⟩
      apply (hPQ _ (theta ⟨z, hz⟩).property).mpr
      simpa only [hback] using hQ

  have hsection {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [FiniteDimensional ℝ Y] {α : Type} [Fintype α]
      (a : Y →ᴬ[ℝ] V3) (r : V3 →ᴬ[ℝ] Y) (hleft : Function.LeftInverse r a)
      (ha0 : a 0 = 0) (cuts : α → Y →ₗ[ℝ] ℝ)
      (hpos : ∃ v : Y, ∀ i, 0 < cuts i v) :
      IsFinitePLBallPair Y {w | a w ∈ C0 ∧ ∀ i, 0 ≤ cuts i w}
        {w | (a w ∈ C0 ∧ ∀ i, 0 ≤ cuts i w) ∧
          (a w ∈ frontier C0 ∨ ∃ i, cuts i w = 0)} := by
    have hright : LeftInvOn a r (range a) := by rintro _ ⟨w, rfl⟩; rw [hleft w]
    have hrange : range a = {x | a (r x) = x} :=
      Set.ext fun x => ⟨fun hx => hright hx, fun hx => ⟨r x, hx⟩⟩
    have hclosed : IsClosed (range a) := by
      rw [hrange]
      exact isClosed_eq (a.continuous.comp r.continuous) continuous_id
    have him : r '' (C0 ∩ range a) = a ⁻¹' C0 := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        change a (r x) ∈ C0
        rw [hright hx.2]
        exact hx.1
      · exact fun hw => ⟨a w, ⟨hw, mem_range_self w⟩, hleft w⟩
    have hcpt : IsCompact (a ⁻¹' C0) := him ▸ (hC.inter_right hclosed).image r.continuous
    have hz : (0 : Y) ∈ interior (a ⁻¹' C0) := by
      apply preimage_interior_subset_interior_preimage a.continuous
      change a 0 ∈ interior C0
      rw [ha0]
      exact hC0
    obtain ⟨v, hv⟩ := hpos
    have hnonzero (i : α) : cuts i ≠ 0 := by
      intro he
      have h := hv i
      rw [he, LinearMap.zero_apply] at h
      exact (lt_irrefl _ h)
    let Q : Set Y := {w | ∀ i, 0 ≤ cuts i w}
    have hQc : IsClosed Q := by
      simp only [Q, ofPred_forall]
      exact isClosed_iInter fun i =>
        isClosed_le continuous_const (cuts i).continuous_of_finiteDimensional
    have hQi : interior Q = {w | ∀ i, 0 < cuts i w} := by
      have h := interior_finite_affine_halfspaces (fun i => -(cuts i).toAffineMap)
        (fun i => by simpa using hnonzero i)
      simpa only [Q, AffineMap.coe_neg, Pi.neg_apply, LinearMap.coe_toAffineMap,
        neg_nonpos, neg_lt_zero] using h
    let T0 := a ⁻¹' C0 ∩ Q
    have hTc : IsCompact T0 := hcpt.inter_right hQc
    have hTi : interior T0 = a ⁻¹' interior C0 ∩ {w | ∀ i, 0 < cuts i w} := by
      change interior (a ⁻¹' C0 ∩ Q) = _
      rw [interior_inter, a.interior_preimage_convex hcv ⟨0, ha0.symm ▸ hC0⟩, hQi]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hz
    let t := ε / (‖v‖ + 1)
    have ht : 0 < t := div_pos hε (by positivity)
    have htv : t * ‖v‖ < ε := by
      change ε / (‖v‖ + 1) * ‖v‖ < ε
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    have hw : t • v ∈ interior (a ⁻¹' C0) := by
      apply hball
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      exact htv
    have hne : (interior T0).Nonempty := by
      refine ⟨t • v, ?_⟩
      change t • v ∈ interior (a ⁻¹' C0 ∩ Q)
      rw [interior_inter, hQi]
      exact ⟨hw, fun i => by simpa only [map_smul, smul_eq_mul] using mul_pos ht (hv i)⟩
    let forms : Finset (Y →ᵃ[ℝ] ℝ) :=
      Finset.univ.image (fun i => (L i).toAffineMap.comp a.toAffineMap - AffineMap.const ℝ Y 1) ∪
        Finset.univ.image (fun i => -(cuts i).toAffineMap)
    have hforms : T0 = {w | ∀ A ∈ forms, A w ≤ 0} := by
      ext w
      simp only [T0, mem_inter_iff, mem_preimage, hrep, Q, mem_ofPred_eq, forms,
        Finset.forall_mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        forall_exists_index, forall_apply_eq_imp_iff, AffineMap.coe_sub, Pi.sub_apply,
        AffineMap.comp_apply, AffineMap.const_apply, LinearMap.coe_toAffineMap,
        AffineMap.coe_neg, Pi.neg_apply, sub_nonpos, neg_nonpos]
      rfl
    have hb := isFinitePLBallPair_of_affine_halfspaces hTc forms hforms hne
    have hfront : frontier T0 = {w | w ∈ T0 ∧
        (a w ∈ frontier C0 ∨ ∃ i, cuts i w = 0)} := by
      rw [frontier, hTc.isClosed.closure_eq, hTi]
      ext w
      constructor
      · rintro ⟨hwT, hn⟩
        refine ⟨hwT, ?_⟩
        by_cases hi : a w ∈ interior C0
        · obtain ⟨i, hni⟩ := not_forall.mp (fun h => hn ⟨hi, h⟩)
          exact Or.inr ⟨i, le_antisymm (not_lt.mp hni) (hwT.2 i)⟩
        · exact Or.inl ⟨hC.isClosed.closure_eq.symm ▸ hwT.1, hi⟩
      · rintro ⟨hwT, hb | ⟨i, hi⟩⟩
        · exact ⟨hwT, fun h => hb.2 h.1⟩
        · exact ⟨hwT, fun h => (lt_irrefl (0 : ℝ)) (hi ▸ h.2 i)⟩
    rw [hfront] at hb
    convert hb using 1 <;> ext w <;>
      simp only [T0, Q, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  let idx : Fin 3 → Fin 2 → Fin 3 := ![![1, 2], ![0, 2], ![0, 1]]
  have hidx0 (i : Fin 2) : idx i.castSucc 0 = i.rev.castSucc := by fin_cases i <;> rfl
  have hidx1 (i : Fin 2) : idx i.castSucc 1 = 2 := by fin_cases i <;> rfl
  let a (j : Fin 3) : P2 →ᴬ[ℝ] V3 := (ContinuousLinearMap.pi fun k : Fin 3 =>
    if k = idx j 0 then ContinuousLinearMap.fst ℝ ℝ ℝ else
      if k = idx j 1 then ContinuousLinearMap.snd ℝ ℝ ℝ else 0).toContinuousAffineMap
  let r (j : Fin 3) : V3 →ᴬ[ℝ] P2 :=
    ((ContinuousLinearMap.proj (idx j 0)).prod
      (ContinuousLinearMap.proj (idx j 1))).toContinuousAffineMap
  have hleft (j : Fin 3) : Function.LeftInverse (r j) (a j) := by
    intro w
    fin_cases j <;> simp [a, r, idx]
  have ha0 (j : Fin 3) : a j 0 = 0 := by fin_cases j <;> ext k <;> fin_cases k <;> simp [a, idx]
  have har (j : Fin 3) (x : V3) : a j (r j x) = x ↔ x j = 0 := by
    fin_cases j <;> simp [a, r, idx, funext_iff, Fin.forall_fin_succ, eq_comm]
  have hplane (j : Fin 3) (active signs : Fin 2 → Bool) :
      IsFinitePLBallPair P2
        {z | z ∈ V.space ∧ f z j = 0 ∧ ∀ k : Fin 2, active k = true →
          if signs k then 0 ≤ f z (idx j k) else f z (idx j k) ≤ 0}
        {z | z ∈ V.space ∧ f z j = 0 ∧
          (∀ k : Fin 2, active k = true →
            if signs k then 0 ≤ f z (idx j k) else f z (idx j k) ≤ 0) ∧
          (z ∈ (V.link p).space ∨ ∃ k : Fin 2, active k = true ∧ f z (idx j k) = 0)} := by
    let cuts : {k : Fin 2 // active k = true} → P2 →ₗ[ℝ] ℝ := fun k =>
      (if signs k then 1 else -1 : ℝ) •
        (if (k : Fin 2) = 0 then LinearMap.fst ℝ ℝ ℝ else LinearMap.snd ℝ ℝ ℝ)
    have hpos : ∃ v : P2, ∀ k, 0 < cuts k v := by
      refine ⟨(if signs 0 then 1 else -1, if signs 1 then 1 else -1), ?_⟩
      rintro ⟨k, hk⟩
      fin_cases k
      · cases hs : signs 0 <;> norm_num [cuts, hs]
      · cases hs : signs 1 <;> norm_num [cuts, hs]
    have hside (x : V3) : (∀ k, 0 ≤ cuts k (r j x)) ↔
        ∀ k : Fin 2, active k = true →
          if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0 := by
      simp only [Subtype.forall]
      apply forall_congr'
      intro k
      apply forall_congr'
      intro hk
      fin_cases k
      · cases hs : signs 0 <;> simp [cuts, r, hs]
      · cases hs : signs 1 <;> simp [cuts, r, hs]
    have hzero (x : V3) : (∃ k, cuts k (r j x) = 0) ↔
        ∃ k : Fin 2, active k = true ∧ x (idx j k) = 0 := by
      constructor
      · rintro ⟨⟨k, hk⟩, hz⟩
        refine ⟨k, hk, ?_⟩
        fin_cases k
        · cases hs : signs 0 <;> simpa [cuts, r, hs] using hz
        · cases hs : signs 1 <;> simpa [cuts, r, hs] using hz
      · rintro ⟨k, hk, hz⟩
        refine ⟨⟨k, hk⟩, ?_⟩
        fin_cases k
        · cases hs : signs 0 <;> simpa [cuts, r, hs] using hz
        · cases hs : signs 1 <;> simpa [cuts, r, hs] using hz
    let U : Set P2 := {w | a j w ∈ C0 ∧ ∀ k, 0 ≤ cuts k w}
    let bU : Set P2 := {w | w ∈ U ∧ (a j w ∈ frontier C0 ∨ ∃ k, cuts k w = 0)}
    have huBall : IsFinitePLBallPair P2 U bU := hsection (a j) (r j) (hleft j) (ha0 j) cuts hpos
    have hUimage : a j '' U = {x | x ∈ C0 ∧ x j = 0 ∧ ∀ k : Fin 2,
        active k = true → if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0} := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨hw.1, (har j _).mp (by rw [hleft j]), ?_⟩
        apply (hside _).mp
        rw [hleft j w]
        exact hw.2
      · rintro ⟨hx, hz, hs⟩
        refine ⟨r j x, ⟨?_, (hside x).mpr hs⟩, (har j x).mpr hz⟩
        rwa [(har j x).mpr hz]
    have hbUimage : a j '' bU = {x | x ∈ C0 ∧ x j = 0 ∧
        (∀ k : Fin 2, active k = true →
          if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0) ∧
        (x ∈ frontier C0 ∨ ∃ k : Fin 2, active k = true ∧ x (idx j k) = 0)} := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        have h := hUimage.subset (mem_image_of_mem (a j) hw.1)
        refine ⟨h.1, h.2.1, h.2.2, ?_⟩
        rcases hw.2 with hc | hc
        · exact Or.inl hc
        · right
          apply (hzero _).mp
          rw [hleft j w]
          exact hc
      · rintro ⟨hx, hz, hs, hb⟩
        refine ⟨r j x, ⟨⟨?_, (hside x).mpr hs⟩, ?_⟩, (har j x).mpr hz⟩
        · rwa [(har j x).mpr hz]
        · rw [(har j x).mpr hz]
          exact hb.imp id (hzero x).mpr
    have hb := (huBall.affine_image (a j) (hleft j).injective.injOn).image_of_subset hq
      (by rintro _ ⟨w, hw, rfl⟩; exact hw.1) hqi
    rw [hUimage, hbUimage] at hb
    have hbdy := himage
      (fun x => x j = 0 ∧ ∀ k : Fin 2, active k = true →
        if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0)
      (fun z => f z j = 0 ∧ ∀ k : Fin 2, active k = true →
        if signs k then 0 ≤ f z (idx j k) else f z (idx j k) ≤ 0)
      (fun x hx => (hqzero x hx j).and (forall_congr' fun k =>
        forall_congr' fun (_ : active k = true) => hqside x hx (idx j k) (signs k)))
    have hrim := himage
      (fun x => x j = 0 ∧ (∀ k : Fin 2, active k = true →
        if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0) ∧
        (x ∈ frontier C0 ∨ ∃ k : Fin 2, active k = true ∧ x (idx j k) = 0))
      (fun z => f z j = 0 ∧ (∀ k : Fin 2, active k = true →
        if signs k then 0 ≤ f z (idx j k) else f z (idx j k) ≤ 0) ∧
        (z ∈ (V.link p).space ∨ ∃ k : Fin 2, active k = true ∧ f z (idx j k) = 0))
      (fun x hx => (hqzero x hx j).and
        ((forall_congr' fun k => forall_congr' fun (_ : active k = true) =>
          hqside x hx (idx j k) (signs k)).and
          ((hqfront x hx).or (exists_congr fun k =>
            and_congr_right' (hqzero x hx (idx j k))))))
    simpa only [hbdy, hrim] using hb
  let ax : ℝ →ᴬ[ℝ] V3 := (ContinuousLinearMap.pi fun j : Fin 3 =>
    if j = 2 then ContinuousLinearMap.id ℝ ℝ else 0).toContinuousAffineMap
  let az : V3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj (2 : Fin 3)).toContinuousAffineMap
  have haxleft : Function.LeftInverse az ax := by intro t; simp [ax, az]
  have hax0 : ax 0 = 0 := by ext j; fin_cases j <;> simp [ax]
  have hax (x : V3) : ax (az x) = x ↔ x 0 = 0 ∧ x 1 = 0 := by
    simp [ax, az, funext_iff, Fin.forall_fin_succ, eq_comm]
  let axisCuts : {k : Unit // endpoint = true} → ℝ →ₗ[ℝ] ℝ := fun _ => LinearMap.id
  have haxpos : ∃ t : ℝ, ∀ k : {k : Unit // endpoint = true}, 0 < axisCuts k t :=
    ⟨1, fun _ => zero_lt_one⟩
  have haxisBall := hsection ax az haxleft hax0 axisCuts haxpos
  let U : Set ℝ := {t | ax t ∈ C0 ∧ (endpoint = true → 0 ≤ t)}
  let bU : Set ℝ := {t | t ∈ U ∧ (ax t ∈ frontier C0 ∨ endpoint = true ∧ t = 0)}
  have haxisCond (t : ℝ) : (∀ k, 0 ≤ axisCuts k t) ↔ (endpoint = true → 0 ≤ t) :=
    ⟨fun h he => h ⟨(), he⟩, fun h k => h k.property⟩
  have haxisZero (t : ℝ) : (∃ k, axisCuts k t = 0) ↔ endpoint = true ∧ t = 0 :=
    ⟨fun ⟨k, hk⟩ => ⟨k.property, hk⟩, fun ⟨he, ht⟩ => ⟨⟨(), he⟩, ht⟩⟩
  have huBall : IsFinitePLBallPair ℝ U bU := by
    convert haxisBall using 1 <;> ext t <;>
      simp only [U, bU, mem_ofPred_eq, haxisCond, haxisZero]
  have hAU : ax '' U = {x | x ∈ C0 ∧ x 0 = 0 ∧ x 1 = 0 ∧
      (endpoint = true → 0 ≤ x 2)} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hz := (hax (ax t)).mp (by rw [haxleft])
      exact ⟨ht.1, hz.1, hz.2, by simpa [ax] using ht.2⟩
    · rintro ⟨hx, hz0, hz1, hp⟩
      refine ⟨az x, ⟨?_, hp⟩, (hax x).mpr ⟨hz0, hz1⟩⟩
      rwa [(hax x).mpr ⟨hz0, hz1⟩]
  have hAbU : ax '' bU = {x | x ∈ C0 ∧ x 0 = 0 ∧ x 1 = 0 ∧
      (endpoint = true → 0 ≤ x 2) ∧ (x ∈ frontier C0 ∨ endpoint = true ∧ x 2 = 0)} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have h := hAU.subset (mem_image_of_mem ax ht.1)
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, by simpa [ax] using ht.2⟩
    · rintro ⟨hx, hz0, hz1, hp, hb⟩
      refine ⟨az x, ⟨⟨?_, hp⟩, ?_⟩, (hax x).mpr ⟨hz0, hz1⟩⟩
      · rwa [(hax x).mpr ⟨hz0, hz1⟩]
      · rwa [(hax x).mpr ⟨hz0, hz1⟩]
  have haxisImage := (huBall.affine_image ax haxleft.injective.injOn).image_of_subset hq
    (by rintro _ ⟨t, ht, rfl⟩; exact ht.1) hqi
  rw [hAU, hAbU] at haxisImage
  have hZimage : q '' {x | x ∈ C0 ∧ x 0 = 0 ∧ x 1 = 0 ∧
      (endpoint = true → 0 ≤ x 2)} = Z := by
    rw [himage _ (fun z => f z 0 = 0 ∧ f z 1 = 0 ∧ (endpoint = true → 0 ≤ f z 2))
      (fun x hx => (hqzero x hx 0).and ((hqzero x hx 1).and
        (forall_congr' fun (_ : endpoint = true) => hqpos x hx 2)))]
    ext z
    by_cases hz : z ∈ V.space
    · simp only [mem_ofPred_eq, Z, mem_inter_iff, hz, true_and, harcf z hz]
      exact ⟨fun h => ⟨h.2.2, h.1, h.2.1⟩, fun h => ⟨h.2.1, h.2.2, h.1⟩⟩
    · simp [hz, Z]
  have hbZimage : q '' {x | x ∈ C0 ∧ x 0 = 0 ∧ x 1 = 0 ∧
      (endpoint = true → 0 ≤ x 2) ∧ (x ∈ frontier C0 ∨ endpoint = true ∧ x 2 = 0)} = bZ := by
    rw [himage _ (fun z => f z 0 = 0 ∧ f z 1 = 0 ∧
      (endpoint = true → 0 ≤ f z 2) ∧
      (z ∈ (V.link p).space ∨ endpoint = true ∧ f z 2 = 0))
      (fun x hx => (hqzero x hx 0).and ((hqzero x hx 1).and
        ((forall_congr' fun (_ : endpoint = true) => hqpos x hx 2).and
          ((hqfront x hx).or (and_congr_right' (hqzero x hx 2))))))]
    ext z
    by_cases hz : z ∈ V.space
    · simp only [bZ, Z, mem_ofPred_eq, mem_inter_iff, hz, true_and, harcf z hz,
        (hregions z hz).2]
      exact ⟨fun h => ⟨⟨h.2.2.1, h.1, h.2.1⟩, h.2.2.2⟩,
        fun h => ⟨h.1.2.1, h.1.2.2, h.1.1, h.2⟩⟩
    · simp [hz, bZ, Z]
  have hZ : IsFinitePLBallPair ℝ Z bZ := by simpa only [hZimage, hbZimage] using haxisImage
  refine ⟨hZ, ?_, ?_⟩
  · intro i sign
    let F : Set E := {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
      if sign then 0 ≤ B (g z) i.rev.castSucc else B (g z) i.rev.castSucc ≤ 0}
    let O : Set E := {z | z ∈ F ∧ (z ∈ (V.link p).space ∨ z ∈ (M fr).space)}
    have hb := hplane i.castSucc ![true, endpoint] ![sign, true]
    have hcond (z : E) : (∀ k : Fin 2,
        (![true, endpoint] : Fin 2 → Bool) k = true →
          if (![sign, true] : Fin 2 → Bool) k then 0 ≤ f z (idx i.castSucc k)
          else f z (idx i.castSucc k) ≤ 0) ↔
        (if sign then 0 ≤ f z i.rev.castSucc else f z i.rev.castSucc ≤ 0) ∧
          (endpoint = true → 0 ≤ f z 2) := by
      simp [Fin.forall_fin_two, hidx0, hidx1]
    have hzeros (z : E) : (∃ k : Fin 2,
        (![true, endpoint] : Fin 2 → Bool) k = true ∧ f z (idx i.castSucc k) = 0) ↔
        f z i.rev.castSucc = 0 ∨ endpoint = true ∧ f z 2 = 0 := by
      simp [Fin.exists_fin_two, hidx0, hidx1]
    have hbody : {z | z ∈ V.space ∧ f z i.castSucc = 0 ∧ ∀ k : Fin 2,
        (![true, endpoint] : Fin 2 → Bool) k = true →
          if (![sign, true] : Fin 2 → Bool) k then 0 ≤ f z (idx i.castSucc k)
          else f z (idx i.castSucc k) ≤ 0} = F := by
      ext z
      by_cases hz : z ∈ V.space
      · simp only [F, hDspace, mem_ofPred_eq, mem_inter_iff, hz, true_and,
          (hregions z hz).1, hsheetf i z hz, hcond, ← hcoord z i.rev]
        exact ⟨fun h => ⟨h.2.2, ⟨h.2.2, h.1⟩, h.2.1⟩,
          fun h => ⟨h.2.1.2, h.2.2, h.1⟩⟩
      · simp [F, hDspace, hz]
    have hZF : Z ⊆ F := by
      intro z hz
      obtain ⟨hr, hz0, hz1⟩ := (harcf z hz.1).mp hz.2
      refine ⟨hDspace.symm.subset ⟨hz.1, (hregions z hz.1).1.mpr hr⟩,
        (hsheetf i z hz.1).mpr ⟨hr, ?_⟩, ?_⟩
      · fin_cases i <;> assumption
      · have ho : B (g z) i.rev.castSucc = 0 := by
          rw [← hcoord z i.rev]
          fin_cases i <;> assumption
        cases sign <;> simp [ho]
    have hrim : {z | z ∈ V.space ∧ f z i.castSucc = 0 ∧
        (∀ k : Fin 2, (![true, endpoint] : Fin 2 → Bool) k = true →
          if (![sign, true] : Fin 2 → Bool) k then 0 ≤ f z (idx i.castSucc k)
          else f z (idx i.castSucc k) ≤ 0) ∧
        (z ∈ (V.link p).space ∨ ∃ k : Fin 2,
          (![true, endpoint] : Fin 2 → Bool) k = true ∧ f z (idx i.castSucc k) = 0)} = Z ∪ O := by
      ext z
      constructor
      · rintro ⟨hz, hi, hc, hb⟩
        have hzF := hbody.subset ⟨hz, hi, hc⟩
        rcases hb with hL | hzero
        · exact Or.inr ⟨hzF, Or.inl hL⟩
        rcases (hzeros z).mp hzero with ho | hFr
        · apply Or.inl
          refine ⟨hz, (harcf z hz).mpr ⟨((hcond z).mp hc).2, ?_⟩⟩
          fin_cases i
          · exact ⟨hi, ho⟩
          · exact ⟨ho, hi⟩
        · exact Or.inr ⟨hzF, Or.inr ((hregions z hz).2.mpr hFr)⟩
      · rintro (hzZ | hzO)
        · obtain ⟨hz, hi, hc⟩ := hbody.symm.subset (hZF hzZ)
          have hza := (harcf z hz).mp hzZ.2
          refine ⟨hz, hi, hc, Or.inr ((hzeros z).mpr (Or.inl ?_))⟩
          fin_cases i
          · exact hza.2.2
          · exact hza.2.1
        · obtain ⟨hz, hi, hc⟩ := hbody.symm.subset hzO.1
          refine ⟨hz, hi, hc, ?_⟩
          rcases hzO.2 with hL | hFr
          · exact Or.inl hL
          · exact Or.inr ((hzeros z).mpr (Or.inr ((hregions z hz).2.mp hFr)))
    have hF : IsFinitePLBallPair P2 F (Z ∪ O) := by simpa only [hbody, hrim] using hb
    have hZO : Z ∩ O = bZ := by
      ext z
      change (z ∈ Z ∧ z ∈ F ∧ (z ∈ (V.link p).space ∨ z ∈ (M fr).space)) ↔ _
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hZF h.1, h.2⟩⟩
    obtain ⟨x, y, hxy, hbpair⟩ := hZ.exists_boundary_eq_pair
    obtain ⟨O', hO', hwhole, hinter⟩ := hF.exists_boundary_arc_complement
      (hbpair ▸ hZ) subset_union_left hxy
    have hOeq : O' = O := by
      apply Subset.antisymm
      · intro z hz
        by_cases hzZ : z ∈ Z
        · exact (hZO.symm.subset (hbpair.symm.subset (hinter.subset ⟨hzZ, hz⟩))).2
        · exact (hwhole.subset (Or.inr hz)).resolve_left hzZ
      · intro z hz
        by_cases hzZ : z ∈ Z
        · exact hO'.1 (hbpair.subset (hZO.subset ⟨hzZ, hz⟩))
        · exact (hwhole.symm.subset (Or.inr hz)).resolve_left hzZ
    exact ⟨hF, by simpa only [hOeq, ← hbpair] using hO'⟩
  · intro hpF signs
    have hep : endpoint = true := by simp [endpoint, hpF]
    have hb := hplane 2 ![true, true] signs
    let F : Set E := {z | z ∈ V.space ∧ z ∈ (M fr).space ∧ ∀ i : Fin 2,
      if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
    have hbody : {z | z ∈ V.space ∧ f z 2 = 0 ∧ ∀ k : Fin 2,
        (![true, true] : Fin 2 → Bool) k = true →
          if signs k then 0 ≤ f z (idx 2 k) else f z (idx 2 k) ≤ 0} = F := by
      ext z
      by_cases hz : z ∈ V.space
      · simp only [F, mem_ofPred_eq, hz, true_and, (hregions z hz).2, hep]
        simp [idx, Fin.forall_fin_two, hcoord0, hcoord1]
      · simp [F, hz]
    have hrim : {z | z ∈ V.space ∧ f z 2 = 0 ∧
        (∀ k : Fin 2, (![true, true] : Fin 2 → Bool) k = true →
          if signs k then 0 ≤ f z (idx 2 k) else f z (idx 2 k) ≤ 0) ∧
        (z ∈ (V.link p).space ∨ ∃ k : Fin 2,
          (![true, true] : Fin 2 → Bool) k = true ∧ f z (idx 2 k) = 0)} =
        {z | z ∈ F ∧ (z ∈ (V.link p).space ∨
          z ∈ (M (sheet 0)).space ∨ z ∈ (M (sheet 1)).space)} := by
      ext z
      constructor
      · rintro ⟨hz, hz2, hc, hL | ⟨k, _, hk⟩⟩
        · exact ⟨hbody.subset ⟨hz, hz2, hc⟩, Or.inl hL⟩
        · refine ⟨hbody.subset ⟨hz, hz2, hc⟩, Or.inr ?_⟩
          have hr : endpoint = true → 0 ≤ f z 2 := fun _ => hz2.symm ▸ le_rfl
          fin_cases k
          · exact Or.inl ((hsheetf 0 z hz).mpr ⟨hr, hk⟩)
          · exact Or.inr ((hsheetf 1 z hz).mpr ⟨hr, hk⟩)
      · rintro ⟨hzF, hb⟩
        obtain ⟨hz, hz2, hc⟩ := hbody.symm.subset hzF
        refine ⟨hz, hz2, hc, ?_⟩
        rcases hb with hL | hS0 | hS1
        · exact Or.inl hL
        · exact Or.inr ⟨0, rfl, ((hsheetf 0 z hz).mp hS0).2⟩
        · exact Or.inr ⟨1, rfl, ((hsheetf 1 z hz).mp hS1).2⟩
    simpa only [hbody, hrim] using hb

end PoincareConjecture.M76.Dehn
