import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryOldGerms
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryStep
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInitialSegment
import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms
import PoincareConjecture.Proofs.M76.Mathlib.CentralLinkSigns
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcCrossedStar
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInteriorChart









set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

set_option maxHeartbeats 1600000 in
theorem exists_moved_zero_vertex_crossing
    (K Knew Kamb : SimplicialComplex ℝ V3)
    (hK : K.faces.Finite) (hKamb : Kamb.faces.Finite) (hKN : Knew ≤ Kamb)
    (H : V3 → V3) (hH : K.AffineOnFaces H) (hHi : Function.Injective H)
    (v : V3) (hwN : H v ∈ Knew.vertices) (hwint : H v ∈ interior Kamb.space)
    (hlinknew : (Knew.link (H v)).space = H '' (K.link v).space)
    (c : V3 ≃L[ℝ] C3) (hwzero : (c (H v)).2 = 0)
    {n : ℕ} (oldP : Polygon V3 (n + 3))
    (holdP : oldP.HasSimplicialEdges) (holdPi : Function.Injective oldP)
    (holdPs : oldP.boundary ℝ = (K.link v).space)
    (hzeros : ((K.link v).space ∩ {z | (c z).2 = 0}).ncard = 2)
    (hpos : ∃ x ∈ (K.link v).space, 0 < (c x).2)
    (hneg : ∃ x ∈ (K.link v).space, (c x).2 < 0)
    (hsigns : ∀ x ∈ K.vertices, (c x).2 ≠ 0 →
      (0 < (c (H x)).2 ↔ 0 < (c x).2) ∧ ((c (H x)).2 < 0 ↔ (c x).2 < 0))
    (O : Set V3) (hO : IsOpen O) (hwO : H v ∈ O) :
    ∃ T : OpenPartialHomeomorph V3 C3,
      H v ∈ T.source ∧ T.source ⊆ O ∧ T (H v) = 0 ∧
      LocallyPiecewiseAffineOn T T.source ∧
      (∀ x ∈ T.source, (c x).2 = 0 ↔ (T x).1.1 = 0) ∧
      ∀ x ∈ T.source, x ∈ Knew.space ↔ (T x).2 = 0 := by
  classical
  have hKnew : Knew.faces.Finite := hKamb.subset hKN
  have hwA : H v ∈ Kamb.vertices := hKN hwN
  let E : V3 ≃ᴬ[ℝ] C3 :=
    c.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv.trans
      (ContinuousAffineEquiv.constVAdd ℝ C3 (-c (H v)))
  have hEv : E (H v) = 0 := by
    change -c (H v) + c (H v) = 0
    exact neg_add_cancel _
  have hEheight (x : V3) : (E x).2 = (c x).2 := by
    change -(c (H v)).2 + (c x).2 = (c x).2
    rw [hwzero, neg_zero, zero_add]
  let A : V3 →ᵃ[ℝ] ℝ := ((LinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toLinearMap).toAffineMap
  let B : C3 →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
  let f₁ : V3 → C3 := E ∘ H
  have hf₁ : (K.link v).AffineOnFaces f₁ := by
    intro face hface
    obtain ⟨a, ha⟩ := hH face hface.1
    exact ⟨E.toContinuousAffineMap.comp a, fun x hx => congrArg E (ha hx)⟩
  have hfi : Function.Injective f₁ := E.injective.comp hHi
  have hpositive (x : V3) (hx : x ∈ (K.link v).vertices) (hp : 0 < A x) :
      0 < B (f₁ x) := by
    change 0 < (E (H x)).2
    rw [hEheight]
    exact ((hsigns x hx.1 hp.ne').1).mpr hp
  have hnegative (x : V3) (hx : x ∈ (K.link v).vertices) (hn : A x < 0) :
      B (f₁ x) < 0 := by
    change (E (H x)).2 < 0
    rw [hEheight]
    exact ((hsigns x hx.1 hn.ne).2).mpr hn
  obtain ⟨m, Pnew, a₀, b₀, hPi, hP, hPimage, hab₀, hPzero, _, _, _⟩ :=
    exists_repaired_crossed_link_bands (K.link v) (finite_link_faces hK v)
      oldP holdP holdPi holdPs hf₁ hfi.injOn A B hpositive hnegative hzeros hneg hpos
  have new_positive (A : V3 →ᵃ[ℝ] ℝ) (B : C3 →ᵃ[ℝ] ℝ)
      (hsign : ∀ x ∈ (K.link v).vertices, 0 < A x → 0 < B (f₁ x))
      (hpoint : ∃ x ∈ (K.link v).space, 0 < A x) :
      ∃ y ∈ Pnew.boundary ℝ, 0 < B y := by
    obtain ⟨x, hx, hxpos⟩ := hpoint
    obtain ⟨face, hface, hxface⟩ := mem_space_iff.mp hx
    have hex : ∃ u ∈ face, 0 < A u := by
      by_contra h
      push Not at h
      have hbound : convexHull ℝ (face : Set V3) ⊆ {z | A z ≤ 0} :=
        convexHull_min h ((convex_Iic (0 : ℝ)).affine_preimage A)
      exact hxpos.not_ge (hbound hxface)
    obtain ⟨u, hu, hupos⟩ := hex
    have huK := (K.link v).face_subset_vertices hface hu
    refine ⟨f₁ u, hPimage.symm.subset ?_, hsign u huK hupos⟩
    exact mem_image_of_mem f₁ ((K.link v).vertices_subset_space huK)
  have hPpos : ∃ x ∈ Pnew.boundary ℝ, x.2 > 0 := new_positive A B hpositive hpos
  have hPneg : ∃ x ∈ Pnew.boundary ℝ, x.2 < 0 := by
    have hnegA : ∃ x ∈ (K.link v).space, A x < 0 := hneg
    obtain ⟨x, hx, hxn⟩ := new_positive (-A) (-B)
      (fun x hx hp => neg_pos.mpr (hnegative x hx (neg_pos.mp hp)))
      (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hnegA)
    refine ⟨x, hx, ?_⟩
    change 0 < -x.2 at hxn
    exact neg_pos.mp hxn
  have hEA := Kamb.affineOnFaces_affine E.toContinuousAffineMap
  have hEN := Knew.affineOnFaces_affine E.toContinuousAffineMap
  let Ambient := hEA.embeddedImage E.injective.injOn
  let Branch := hEN.embeddedImage E.injective.injOn
  have hAmbient : Ambient.faces.Finite := hEA.embeddedImage_finite E.injective.injOn hKamb
  have hBranch : Branch.faces.Finite := hEN.embeddedImage_finite E.injective.injOn hKnew
  have hAmbientS : Ambient.space = E '' Kamb.space := hEA.embeddedImage_space _
  have hBranchS : Branch.space = E '' Knew.space := hEN.embeddedImage_space _
  have hBA : Branch ≤ Ambient := by
    have hfacesN : Branch.faces = (fun face => face.image E) '' Knew.faces :=
      hEN.embeddedImage_faces E.injective.injOn
    have hfacesA : Ambient.faces = (fun face => face.image E) '' Kamb.faces :=
      hEA.embeddedImage_faces E.injective.injOn
    intro face hface
    change face ∈ Branch.faces at hface
    change face ∈ Ambient.faces
    rw [hfacesN] at hface
    rw [hfacesA]
    obtain ⟨u, hu, rfl⟩ := hface
    exact ⟨u, hKN hu, rfl⟩
  have hzeroA : (0 : C3) ∈ Ambient.vertices := by
    have heq : Ambient.vertices = E '' Kamb.vertices :=
      hEA.embeddedImage_vertices E.injective.injOn
    exact heq.symm.subset ⟨H v, hwA, hEv⟩
  have hzeroB : (0 : C3) ∈ Branch.vertices := by
    have heq : Branch.vertices = E '' Knew.vertices :=
      hEN.embeddedImage_vertices E.injective.injOn
    exact heq.symm.subset ⟨H v, hwN, hEv⟩
  have hintA : (0 : C3) ∈ interior Ambient.space := by
    rw [hAmbientS]
    change (0 : C3) ∈ interior (E.toHomeomorph '' Kamb.space)
    rw [← E.toHomeomorph.image_interior]
    exact ⟨H v, hwint, hEv⟩
  have hPlink : Pnew.boundary ℝ = (Branch.link 0).space := by
    have h := hEN.embeddedImage_link_space E.injective.injOn hwN
    change (Branch.link (E (H v))).space = E '' (Knew.link (H v)).space at h
    rw [hEv, hlinknew, image_image] at h
    exact hPimage.trans h.symm
  have hPambient : Pnew.boundary ℝ ⊆ (Ambient.link 0).space := by
    rw [hPlink]
    apply space_subset_of_le
    intro face hface
    exact ⟨hBA hface.1, hface.2.1, hBA hface.2.2⟩
  obtain ⟨C, g, h, boundary, _hC, _hcv, _hC0, hh, _hboundary,
    hhg, hgzero, _hbase, _hray, _hrim, hflat, _hside, hcone⟩ :=
    exists_original_crossed_star Ambient hAmbient hzeroA hintA Pnew hP hPi
      hPambient hab₀ hPzero hPneg hPpos
  obtain ⟨χ, hχsource, _hχtarget, hχ, _hχinv, _hχfinite, _hχifinite, hχval, _hχival⟩ :=
    hh.exists_interior_chart rfl
  have hstarint : (0 : C3) ∈ interior (Ambient.closedStar 0).space := by
    obtain ⟨d, hd, hnear⟩ := Ambient.exists_ball_inter_space_subset_closedStar hAmbient hzeroA
    apply interior_maximal (fun x hx => hnear ⟨interior_subset hx.1, hx.2⟩)
      (isOpen_interior.inter isOpen_ball)
    exact ⟨hintA, mem_ball_self hd⟩
  have hχzero : (0 : C3) ∈ χ.source := hχsource.symm.subset hstarint
  have hχcenter : χ 0 = 0 :=
    (hχval ⟨0, interior_subset hstarint⟩).trans ((hhg _).trans hgzero)
  obtain ⟨d, hd, hnear⟩ := Branch.exists_ball_inter_space_subset_closedStar hBranch hzeroB
  have hbranchCone : (Branch.closedStar 0).space = convexJoin ℝ {0} (Pnew.boundary ℝ) := by
    have hne : (Branch.link 0).space.Nonempty :=
      ⟨a₀, hPlink.subset (hPzero.symm.subset (by simp)).1⟩
    rw [hPlink, ← coneAtZero_link_eq_closedStar Branch hzeroB]
    exact (Branch.link 0).coneAtZero_space_eq_convexJoin
      (fun _ hs => linearIndependent_of_mem_link_zero hs) Branch.injOn_normalize_link hne
  let V := O
  have hV : IsOpen V := hO
  have hvV : H v ∈ V := hwO
  let O' := ball (0 : C3) d ∩ E '' V
  have hO' : IsOpen O' := isOpen_ball.inter (E.toHomeomorph.isOpenMap _ hV)
  let localChart := E.toHomeomorph.toOpenPartialHomeomorph.trans (χ.restrOpen O' hO')
  have hvLocal : H v ∈ localChart.source := by
    refine ⟨mem_univ _, ?_, ?_, mem_image_of_mem E hvV⟩
    · change E (H v) ∈ χ.source
      rw [hEv]
      exact hχzero
    · change E (H v) ∈ ball 0 d
      rw [hEv]
      exact mem_ball_self hd
  have hLocalPL : LocallyPiecewiseAffineOn localChart localChart.source :=
    (hχ.comp (locallyPiecewiseAffineOn_affine E.toContinuousAffineMap isOpen_univ)).mono
      localChart.open_source (fun _ hx => ⟨hx.1, hx.2.1⟩)
  have hlocal (x : V3) (hx : x ∈ localChart.source) :
      x ∈ V ∧ ((c x).2 = 0 ↔ (localChart x).1.1 = 0) ∧
        (x ∈ Knew.space ↔ (localChart x).2 = 0) := by
    have hxV : x ∈ V := by
      obtain ⟨y, hy, heq⟩ := hx.2.2.2
      exact E.injective heq ▸ hy
    have hxstar : E x ∈ (Ambient.closedStar 0).space :=
      interior_subset (hχsource.subset hx.2.1)
    have hvalue : localChart x = h ⟨E x, hxstar⟩ := hχval ⟨E x, hxstar⟩
    have hBmem : E x ∈ Branch.space ↔ x ∈ Knew.space := by
      rw [hBranchS]
      exact E.injective.mem_set_image
    have hBstar : E x ∈ Branch.space ↔ E x ∈ (Branch.closedStar 0).space :=
      ⟨fun h => hnear ⟨h, hx.2.2.1⟩,
        fun h => space_subset_of_le
          (show Branch.closedStar 0 ≤ Branch from fun _ hs => hs.1) h⟩
    refine ⟨hxV, ?_, ?_⟩
    · rw [← hEheight, hvalue]
      exact hflat ⟨E x, hxstar⟩
    · rw [← hBmem, hBstar, hbranchCone, hvalue]
      exact hcone ⟨E x, hxstar⟩
  refine ⟨localChart, hvLocal, fun x hx => (hlocal x hx).1, ?_, hLocalPL, ?_, ?_⟩
  · change χ (E (H v)) = 0
    rw [hEv, hχcenter]
  · exact fun x hx => (hlocal x hx).2.1
  · exact fun x hx => (hlocal x hx).2.2

end Geometry.OriginalPLTower
