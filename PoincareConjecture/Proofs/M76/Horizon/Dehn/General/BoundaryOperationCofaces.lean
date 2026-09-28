import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryMotionHistory
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoCofaceCarrierGerm
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFacetInterior
import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedFaceDimension

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

set_option maxHeartbeats 800000 in

theorem Step.exists_boundary_rim_cofaces_with_history
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup)
    (a b : D) (hab : a ≠ b) (haRim : (a : V2) ∈ Rim)
    (hpair : step.projection (step.inclusion (old.map a)) =
      step.projection (step.inclusion (old.map b)))
    {U : Set s.Carrier} (hU : IsOpen U)
    (haU : step.projection (step.inclusion (old.map a)) ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
      (J B₀ P C₀ K₀ K₁ B K : SimplicialComplex ℝ V3)
      (q : V3 → V2) (ρ : ℝ) (H : PLCarrierMotion J.space C₀.space ε)
      (G : I → t.Carrier ≃ₜ t.Carrier) (new : StageMarkedDisk t R Fmark base Jgroup)
      (eta : old.rim.Homotopy new.rim),
      old.map a ∈ w.left.source ∧ old.map b ∈ w.right.source ∧
      step.projection (step.inclusion (old.map a)) ∈ Q.source ∧
      Q (step.projection (step.inclusion (old.map a))) = 0 ∧
      Q.source ⊆ U ∩ w.target ∧
      (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ (c (Q y)).1.1) ∧
      (∀ y ∈ Q.source, y ∈ frontier (s.projection ⁻¹' R) ↔ (c (Q y)).1.1 = 0) ∧
      J.faces.Finite ∧ J.space ⊆ Q.target ∧ (0 : V3) ∈ interior J.space ∧
      0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
      P.space = (w.right.trans Q) '' (old.map '' Rim ∩ (w.right.trans Q).source) ∩
        J.space ∧ P.space = B₀.space ∩ {z | (c z).1.1 = 0} ∧
      C₀.space = B₀.space \ ball (0 : V3) ρ ∧ K₀.space = P.space ∧
      K₁.space = P.space ∩ (C₀.space ∪ frontier J.space) ∧
      K.faces = (fun face => face.image (H.map 1)) '' K₀.faces ∧
      K.vertices = H.map 1 '' K₀.vertices ∧
      (∀ v ∈ K₀.vertices,
        (c (H.map 1 v)).2 = 0 ↔ v ∈ K₁.vertices ∧ (c v).2 = 0) ∧
      (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
        (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
      Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
      Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
      (∀ x, G 0 x = x) ∧
      (∀ u, EqOn (G u)
        ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
          (w.right.trans Q).source) ∧
      (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
      (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' C₀.space)) ∧
      (∀ u, EqOn (G u) id w.left.source) ∧
      (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
        (G u) ⁻¹' frontier (t.projection ⁻¹' R) = frontier (t.projection ⁻¹' R) ∧
        (G u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
      (∀ u k l, (t.charts k).symm.trans
        ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ x, new.map x = G 1 (old.map x)) ∧
      new.basepath = old.basepath.trans (eta.evalAt squareRimBase) ∧
      (∀ y ∈ Q.source,
        y ∈ (step.projection ∘ step.inclusion) '' (old.map '' D ∩ w.left.source) ↔
          0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0) ∧
      (∀ y ∈ Q.source,
        y ∈ (step.projection ∘ step.inclusion) '' (new.map '' D ∩ w.left.source) ↔
          0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0) ∧
      B.faces.Finite ∧ K.faces.Finite ∧ K ≤ B ∧
      B.space = (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩
        J.space ∧
      K.space = (w.right.trans Q) '' (new.map '' Rim ∩ (w.right.trans Q).source) ∩
        J.space ∧
      K.space = B.space ∩ {z | (c z).1.1 = 0} ∧
      B.AffineOnFaces q ∧ InjOn q B.space ∧ MapsTo q B.space D ∧
      (∀ z ∈ B.space, z ∈ K.space ↔ q z ∈ Rim) ∧
      (∀ edge ∈ K.faces, edge.card = 2 → ∀ z,
        z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)) →
        z ∈ interior J.space →
        ∃ face ∈ B.faces, edge ⊆ face ∧ face.card = 3 ∧
          (∀ other ∈ B.faces, edge ⊆ other → other ⊆ face) ∧
          ∀ O : Set V3, IsOpen O → z ∈ O →
            ∃ V : Set V3, IsOpen V ∧ z ∈ V ∧ V ⊆ O ∩ interior J.space ∧
              ∀ x ∈ V, x ∈ B.space ↔ x ∈ convexHull ℝ (face : Set V3)) ∧
      Nonempty (BoundaryMotionHistory old.map (w.right.trans Q) c J C₀ B q ε H) ∧
      ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (E : SimplicialComplex ℝ V2)
        (first : Z.space ≃ₜ E.space),
        Z.faces.Finite ∧ E.faces.Finite ∧
        Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
          step.projection (step.inclusion (new.map z.1)) =
            step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
        E.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
          step.projection (step.inclusion (new.map x)) =
            step.projection (step.inclusion (new.map y))} ∧
        first.IsFinitePL ∧ first.symm.IsFinitePL ∧
        ∀ z : Z.space, (first z : V2) = z.val.1 := by
  classical
  obtain ⟨w, c, Q, J, B₀, P, C₀, R₀, B₁, K₀, K₁, L, q₀, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQPL, hbranches, hregion, hfront, hsheet,
    hJ, _hcv, hJQ, _hzeroJ, _hρ, _hball, hclosed, _hB₀, _hP, _hC₀, hB₀s, hPs,
    _hPr, _hC₀s, _hq₀, _hq₀i, hq₀D, hright, hleft, hrim,
    _hR₀, _hR₀J, _hB₁R₀, _hB₁s, _hqB₁, _hK₀B₁, _hK₀s, _hK₁K₀,
    _hK₁s, _hfull, _hL, _hLs, hwhole, _hδ, _hmargin, hmotions⟩ :=
    step.exists_original_boundary_branch_operation_with_closed_support
      he hF hopen old a b hab haRim hpair hU haU
  obtain ⟨H, _hH, hheight, _hsigns, _hzero, _hfaces, _hbranchfaces, _hposition,
    B, K, hB, hK, hKB, _hprotected, _hBfaces, hKfaces, hKvertices, hBs, hKs, hqB, hqi,
    G, new, eta, hG, hGinv, hGzero, _hformula, hGout, _hGprotected, hGleft,
    hGregion, hGPL, hnewmap, hpath, himage, hrimimage,
    Z, E, first, hZ, hE, hZs, hEs, hfirst, hfirstinv, hfirstval⟩ := hmotions ε hε
  let T := w.right.trans Q
  let q := q₀ ∘ (H.map 1).symm
  have hqi' : InjOn q B.space := hqi
  have hqB' : B.AffineOnFaces q := hqB
  have hinv (z : V3) (hz : z ∈ B.space) : (H.map 1).symm z ∈ B₀.space := by
    obtain ⟨x, hx, rfl⟩ := hBs.subset hz
    simpa only [(H.map 1).symm_apply_apply] using hx
  have hqD : MapsTo q B.space D := fun _ hz => hq₀D (hinv _ hz)
  have hqimage : q '' B.space = q₀ '' B₀.space := by
    rw [hBs, image_image]
    congr 1
    funext x
    exact congrArg q₀ ((H.map 1).symm_apply_apply x)
  have hKzero : K.space = B.space ∩ {z | (c z).1.1 = 0} := by
    rw [hKs, hPs, hBs]
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
      exact ⟨mem_image_of_mem (H.map 1) hx, (hheight 1 x).trans hx0⟩
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, ⟨hx, (hheight 1 x).symm.trans hz⟩, rfl⟩
  have hqrim (z : V3) (hz : z ∈ B.space) : z ∈ K.space ↔ q z ∈ Rim := by
    have hmem : z ∈ K.space ↔ (H.map 1).symm z ∈ P.space := by
      rw [hKs]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa only [(H.map 1).symm_apply_apply] using hx
      · intro h
        exact ⟨(H.map 1).symm z, h, (H.map 1).apply_symm_apply z⟩
    exact hmem.trans (hrim _ (hinv z hz))
  have hleftimage : new.map '' D ∩ w.left.source = old.map '' D ∩ w.left.source := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hx⟩
      have he : G 1 (old.map y) = x := (hnewmap y).symm.trans hyx
      have hold : old.map y = x := (G 1).injective (he.trans (hGleft 1 hx).symm)
      exact ⟨⟨y, hy, hold⟩, hx⟩
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨⟨y, hy, (hnewmap y).trans (hGleft 1 hx)⟩, hx⟩
  have hcofaces (edge : Finset V3) (hedge : edge ∈ K.faces) (he2 : edge.card = 2)
      (z : V3) (hze : z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)))
      (hzJ : z ∈ interior J.space) :
      ∃ face ∈ B.faces, edge ⊆ face ∧ face.card = 3 ∧
        (∀ other ∈ B.faces, edge ⊆ other → other ⊆ face) ∧
        ∀ O : Set V3, IsOpen O → z ∈ O →
          ∃ V : Set V3, IsOpen V ∧ z ∈ V ∧ V ⊆ O ∩ interior J.space ∧
            ∀ x ∈ V, x ∈ B.space ↔ x ∈ convexHull ℝ (face : Set V3) := by
    have heB := hKB hedge
    have hzK := K.convexHull_subset_space hedge (intrinsicInterior_subset hze)
    have hzB := SimplicialComplex.space_subset_of_le hKB hzK
    have hzRim : q z ∈ Rim := (hqrim z hzB).mp hzK
    have hinvJ : (H.map 1).symm z ∈ interior J.space := by
      have hi := ((H.map 1).image_interior J.space).trans (congrArg interior (H.carrier 1))
      obtain ⟨x, hx, rfl⟩ := hi.symm.subset hzJ
      simpa only [(H.map 1).symm_apply_apply] using hx
    have hparam := hright _ (hinv z hzB)
    let N := hqB'.embeddedImage hqi'
    have hN : N.faces.Finite := hqB'.embeddedImage_finite hqi' hB
    have hNs : N.space = q₀ '' B₀.space :=
      (hqB'.embeddedImage_space hqi').trans hqimage
    have hND : N.space ⊆ D := by
      rw [hqB'.embeddedImage_space hqi']
      rintro _ ⟨x, hx, rfl⟩
      exact hqD hx
    have hqz : q z ∈ closure (interior N.space) := by
      let V := T.source ∩ T ⁻¹' interior J.space
      have hV : IsOpen V := T.isOpen_inter_preimage isOpen_interior
      have hpre : IsOpen ((fun x : D => old.map x) ⁻¹' V) :=
        hV.preimage old.embedding.continuous
      obtain ⟨O, hO, hOpre⟩ := isOpen_induced_iff.mp hpre
      have hpoint : q z ∈ O := by
        have hxV : (⟨q z, hqD hzB⟩ : D) ∈ (fun x : D => old.map x) ⁻¹' V := by
          change old.map (q z) ∈ V
          refine ⟨hparam.1, ?_⟩
          change T (old.map (q₀ ((H.map 1).symm z))) ∈ interior J.space
          rw [hparam.2]
          exact hinvJ
        exact hOpre.symm.subset hxV
      have hcover : D ∩ O ⊆ N.space := by
        intro x hx
        have hxV : old.map x ∈ V :=
          hOpre.subset (show (⟨x, hx.1⟩ : D) ∈ Subtype.val ⁻¹' O from hx.2)
        have hcoord : T (old.map x) ∈ B₀.space := hB₀s.symm.subset
          ⟨⟨old.map x, ⟨mem_image_of_mem old.map hx.1, hxV.1⟩, rfl⟩,
            interior_subset hxV.2⟩
        rw [hNs]
        exact ⟨T (old.map x), hcoord, hleft x hx.1 hxV.1 (interior_subset hxV.2)⟩
      have hlocal : interior D ∩ O ⊆ interior N.space :=
        interior_maximal (fun x hx => hcover ⟨interior_subset hx.1, hx.2⟩)
          (isOpen_interior.inter hO)
      apply closure_mono hlocal
      apply hO.closure_inter
      refine ⟨?_, hpoint⟩
      rw [interior_closedBall _ one_ne_zero, closure_ball _ one_ne_zero]
      exact hqD hzB
    have hface (u : Finset V3) (hu : u ∈ B.faces) : u.image q ∈ N.faces :=
      (hqB'.image_mem_embeddedImage_iff hqi' (B.subset_space hu)).mpr hu
    have hcard (u : Finset V3) (hu : u ∈ B.faces) : (u.image q).card = u.card :=
      Finset.card_image_iff.mpr (hqi'.mono (B.subset_space hu))
    have hqedge : q z ∈ intrinsicInterior ℝ (convexHull ℝ (edge.image q : Set V2)) := by
      obtain ⟨a, ha⟩ := hqB' edge heB
      have hai : InjOn a (convexHull ℝ (edge : Set V3)) := by
        intro x hx y hy hxy
        exact hqi' (B.convexHull_subset_space heB hx) (B.convexHull_subset_space heB hy)
          ((ha hx).trans (hxy.trans (ha hy).symm))
      have hspan := a.toAffineMap.injOn_affineSpan_of_injOn_convex
        (convex_convexHull ℝ (edge : Set V3)) ⟨z, intrinsicInterior_subset hze⟩ hai
      rw [Finset.coe_image, ← hqB'.image_convexHull heB, ha.image_eq,
        ha (intrinsicInterior_subset hze), ← intrinsicClosure_sdiff_intrinsicFrontier]
      refine ⟨subset_intrinsicClosure (mem_image_of_mem a (intrinsicInterior_subset hze)), ?_⟩
      intro hfrontier
      have himagefront := a.toAffineMap.intrinsicFrontier_image_of_injOn
        (convexHull ℝ (edge : Set V3)) hspan
      obtain ⟨y, hy, hyz⟩ := himagefront.subset hfrontier
      have hyspan : y ∈ affineSpan ℝ (convexHull ℝ (edge : Set V3)) :=
        intrinsicClosure_subset_affineSpan (by
          rw [← intrinsicClosure_sdiff_intrinsicInterior] at hy
          exact hy.1)
      have heq : y = z := hspan hyspan
        (subset_affineSpan ℝ _ (intrinsicInterior_subset hze)) hyz
      rw [heq, ← intrinsicClosure_sdiff_intrinsicInterior] at hy
      exact hy.2 hze
    obtain ⟨face', hface', hfacecard, hzface'⟩ :=
      N.exists_full_face_of_mem_closure_interior hN hqz
    change face' ∈ (hqB'.embeddedImage hqi').faces at hface'
    rw [hqB'.embeddedImage_faces hqi'] at hface'
    obtain ⟨face, hfaceB, rfl⟩ := hface'
    have hface3 : face.card = 3 := by
      rw [hcard face hfaceB] at hfacecard
      simpa using hfacecard
    have hzface : z ∈ convexHull ℝ (face : Set V3) := by
      rw [Finset.coe_image, ← hqB'.image_convexHull hfaceB] at hzface'
      obtain ⟨y, hy, hyz⟩ := hzface'
      exact hqi' (B.convexHull_subset_space hfaceB hy) hzB hyz ▸ hy
    have hef : edge ⊆ face := B.subset_of_mem_intrinsicInterior_face heB hfaceB hze hzface
    have hunique (other : Finset V3) (hother : other ∈ B.faces)
        (heo : edge ⊆ other) (ho3 : other.card = 3) : other = face := by
      by_contra hne
      have himagene : other.image q ≠ face.image q := by
        intro heq
        apply hne
        apply Finset.coe_injective
        apply (hqi'.image_eq_image_iff (B.subset_space hother) (B.subset_space hfaceB)).mp
        exact (Finset.coe_image.symm.trans
          (congrArg (fun a : Finset V2 => (a : Set V2)) heq)).trans Finset.coe_image
      have hinterior := N.mem_interior_space_of_paired_facet
        (by rw [hcard edge heB, he2]; simp)
        (hface other hother) (hface face hfaceB)
        (by rw [hcard other hother, ho3]; simp)
        (by rw [hcard face hfaceB, hface3]; simp)
        (Finset.image_subset_image heo) (Finset.image_subset_image hef) himagene hqedge
      have hrimfront : q z ∈ frontier D := by
        rw [frontier_closedBall _ one_ne_zero]
        exact hzRim
      exact hrimfront.2 (interior_mono hND hinterior)
    have hexhaust (other : Finset V3) (hother : other ∈ B.faces)
        (heo : edge ⊆ other) : other ⊆ face := by
      have hupper : other.card ≤ 3 := by
        simpa using hqB'.face_card_le_of_injOn hqi' hother
      have hlower := Finset.card_le_card heo
      by_cases htwo : other.card = 2
      · have heq : edge = other := Finset.eq_of_subset_of_card_le heo (by omega)
        exact heq ▸ hef
      · have hthree : other.card = 3 := by omega
        rw [hunique other hother heo hthree]
    refine ⟨face, hfaceB, hef, hface3, hexhaust, ?_⟩
    intro O hO hzO
    obtain ⟨V, hV, hzV, hcarrier⟩ := B.exists_open_two_coface_carrier_germ
      hB heB hfaceB hfaceB (fun u hu heu => Or.inl (hexhaust u hu heu)) hze
    refine ⟨V ∩ (O ∩ interior J.space), hV.inter (hO.inter isOpen_interior),
      ⟨hzV, hzO, hzJ⟩, inter_subset_right, ?_⟩
    intro x hx
    simpa only [union_self] using hcarrier x hx.1
  refine ⟨w, c, Q, J, B₀, P, C₀, K₀, K₁, B, K, q, ρ, H, G, new, eta,
    ha, hb, haQ, hQzero, hQU, hQPL, hbranches, hregion, hfront,
    hJ, hJQ, _hzeroJ, _hρ, _hball, _hPr, hPs, _hC₀s, _hK₀s, _hK₁s,
    hKfaces, hKvertices, _hzero, hwhole, hG, hGinv, hGzero, _hformula,
    hGout, _hGprotected, hGleft, hGregion, hGPL, hnewmap, hpath, hsheet, ?_, hB, hK, hKB,
    hBs.trans himage.symm, hKs.trans hrimimage.symm, hKzero, hqB', hqi', hqD,
    hqrim, hcofaces, ?_, Z, E, first, hZ, hE, hZs, hEs, hfirst, hfirstinv, hfirstval⟩
  · intro y hy
    rw [hleftimage]
    exact hsheet y hy
  · refine ⟨{
      ambient := R₀
      sheet := B₁
      parameter := q₀
      radius := ρ
      radius_pos := _hρ
      closed_support := hclosed
      protected_space := by rw [_hB₁s]; exact _hC₀s
      ambient_finite := _hR₀
      ambient_subdivision := _hR₀J
      sheet_subcomplex := _hB₁R₀
      sheet_space := _hB₁s.trans hB₀s
      parameter_affine := _hqB₁
      parameter_injective := _hq₀i.mono _hB₁s.subset
      parameter_inside := hq₀D.mono _hB₁s.subset Subset.rfl
      parameter_right := fun z hz => hright z (_hB₁s.subset hz)
      parameter_left := hleft
      parameter_rim := ?_
      motion_affine := _hH
      region_height := hheight
      strict_signs := _hsigns
      zero_faces := _hbranchfaces
      endpoint_faces := _hBfaces
      endpoint_parameter := rfl }⟩
    intro z hz
    have hzB₀ := _hB₁s.subset hz
    rw [← hrim z hzB₀, hPs]
    exact ⟨fun h => ⟨hzB₀, h⟩, fun h => h.2⟩

end Geometry.OriginalPLTower
