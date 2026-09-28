import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereSideTriangles
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.SphereSideEdgeLinks
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexGluing












set_option autoImplicit false
set_option maxHeartbeats 1800000

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1



theorem ChartwisePLSphere.exists_original_side_products
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) :
    ∃ (t : Finset R) (F : X → (t → ℝ × V3))
      (K L N T P M : SimplicialComplex ℝ (t → ℝ × V3))
      (H : R ≃ₜ K.space) (g : (t → ℝ × V3) → R)
      (W Rpos Rneg : Set X)
      (B : N.vertices → OpenPartialHomeomorph X V3)
      (hK : K.faces.Finite) (_hT : T.faces.Finite)
      (hP : P.faces.Finite) (hM : M.faces.Finite) (hN : N.faces.Finite),
      let : Fintype K.faces := hK.fintype
      let : Fintype P.faces := hP.fintype
      let : Fintype M.faces := hM.fintype
      let : Fintype N.faces := hN.fintype
      ∃ (FP : SimplicialComplex.BoundaryTriangleFibers P N)
        (FM : SimplicialComplex.BoundaryTriangleFibers M N)
        (EP : SimplicialComplex.BoundaryEdgeFamily FP)
        (EM : SimplicialComplex.BoundaryEdgeFamily FM)
        (VP : SimplicialComplex.BoundaryVertexFamily EP)
        (VM : SimplicialComplex.BoundaryVertexFamily EM)
        (CP : (N.space ×ˢ I : Set ((t → ℝ × V3) × ℝ)) ≃ₜ
          (P.barycentricNeighborhood N).space)
        (CM : (N.space ×ˢ I : Set ((t → ℝ × V3) × ℝ)) ≃ₜ
          (M.barycentricNeighborhood N).space),
      CP.IsFinitePL ∧ CM.IsFinitePL ∧
      (∀ (x : t → ℝ × V3) (hx : x ∈ N.space),
        (CP ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : t → ℝ × V3) = x ∧
        (CM ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : t → ℝ × V3) = x) ∧
      (∀ x : (N.space ×ˢ I : Set ((t → ℝ × V3) × ℝ)),
        ((CP x : t → ℝ × V3) ∈ N.space ↔ (x : (t → ℝ × V3) × ℝ).2 = 0) ∧
        ((CM x : t → ℝ × V3) ∈ N.space ↔ (x : (t → ℝ × V3) × ℝ).2 = 0)) ∧
      (∀ (p : N.vertices)
        (x : ((N.barycentricDualBlock {(p : t → ℝ × V3)}).space ×ˢ I :
          Set ((t → ℝ × V3) × ℝ))),
        (CP ⟨x, ⟨N.barycentricSubdivision_isSubdivision.space_eq.subset
          (SimplicialComplex.space_subset_of_le
            (N.barycentricDualBlock_le {(p : t → ℝ × V3)}) x.property.1),
          x.property.2⟩⟩ : t → ℝ × V3) = VP.chart p x ∧
        (CM ⟨x, ⟨N.barycentricSubdivision_isSubdivision.space_eq.subset
          (SimplicialComplex.space_subset_of_le
            (N.barycentricDualBlock_le {(p : t → ℝ × V3)}) x.property.1),
          x.property.2⟩⟩ : t → ℝ × V3) = VM.chart p x) ∧
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      L ≤ K ∧ T ≤ K ∧ N ≤ T ∧ P ≤ T ∧ M ≤ T ∧ N ≤ P ∧ N ≤ M ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ L.vertices) → a ∈ L.faces) ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ N.vertices) → a ∈ N.faces) ∧
      (∀ a ∈ T.faces, (∀ v ∈ a, v ∈ P.vertices) → a ∈ P.faces) ∧
      (∀ a ∈ T.faces, (∀ v ∈ a, v ∈ M.vertices) → a ∈ M.faces) ∧
      (∀ Q ∈ ({T, P, M} : Set (SimplicialComplex ℝ (t → ℝ × V3))),
        ∀ a ∈ Q.faces, (∀ v ∈ a, v ∈ N.vertices) → a ∈ N.faces) ∧
      K.space = F '' R ∧ L.space = F '' frontier R ∧ N.space = F '' S ∧
      (∀ x : R, (H x : t → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      IsOpen W ∧ S ⊆ W ∧ Rpos ∪ Rneg = W ∧ Rpos ∩ Rneg = S ∧
      T.faces = ⋃ p : N.vertices, (K.closedStar p).faces ∧
      T.space = ⋃ p : N.vertices, (K.closedStar p).space ∧
      MapsTo (fun z => (g z : X)) T.space W ∧
      P.space = T.space ∩ (fun z => (g z : X)) ⁻¹' Rpos ∧
      M.space = T.space ∩ (fun z => (g z : X)) ⁻¹' Rneg ∧
      P.space ∪ M.space = T.space ∧ P.space ∩ M.space = N.space ∧
      (∀ a ∈ T.faces, a ∈ P.faces ∨ a ∈ M.faces) ∧
      P.faces ∩ M.faces = N.faces ∧
      (∀ a ∈ N.faces, ∃ b ∈ N.faces, a ⊆ b ∧ b.card = 3) ∧
      (∀ a ∈ N.faces, a.card = 2 → (N.faceLink a).vertices.ncard = 2) ∧
      (∀ a ∈ P.faces, ∃ b ∈ P.faces, a ⊆ b ∧ b.card = 4) ∧
      (∀ a ∈ M.faces, ∃ b ∈ M.faces, a ⊆ b ∧ b.card = 4) ∧
      (∀ a ∈ N.faces, a.card = 3 →
        {b : Finset (t → ℝ × V3) | b ∈ P.faces ∧ b.card = 4 ∧ a ⊆ b}.ncard = 1 ∧
        {b : Finset (t → ℝ × V3) | b ∈ M.faces ∧ b.card = 4 ∧ a ⊆ b}.ncard = 1) ∧
      ∀ p : N.vertices,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
        (B p).source ⊆ W ∧
        (∀ i, (e i).symm.trans (B p) ∈ piecewiseAffineGroupoid V3) ∧
        (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
        InjOn (fun z => B p (g z)) (K.closedStar p).space ∧
        (∃ O : Set X, IsOpen O ∧ (g p : X) ∈ O ∧ O ⊆ (B p).source ∧
          O ⊆ (fun z => (g z : X)) '' (K.closedStar p).space) ∧
        B p (g p) ∈ interior ((fun z => B p (g z)) '' (K.closedStar p).space) ∧
        (∀ z ∈ (K.closedStar p).space,
          (z ∈ N.space ↔ (B p (g z)) 0 = 0) ∧
          ((g z : X) ∈ Rpos ↔ 0 ≤ (B p (g z)) 0) ∧
          ((g z : X) ∈ Rneg ↔ (B p (g z)) 0 ≤ 0)) ∧
        T.closedStar p = K.closedStar p ∧ T.link p = K.link p ∧
        (P.closedStar p).space = (K.closedStar p).space ∩ {z | 0 ≤ (B p (g z)) 0} ∧
        (M.closedStar p).space = (K.closedStar p).space ∩ {z | (B p (g z)) 0 ≤ 0} ∧
        (N.closedStar p).space = (K.closedStar p).space ∩ {z | (B p (g z)) 0 = 0} ∧
        (P.link p).space = (K.link p).space ∩ {z | 0 ≤ (B p (g z)) 0} ∧
        (M.link p).space = (K.link p).space ∩ {z | (B p (g z)) 0 ≤ 0} ∧
        (N.link p).space = (K.link p).space ∩ {z | (B p (g z)) 0 = 0} ∧
        IsFinitePLBallPair V3 (P.closedStar p).space
          ((P.link p).space ∪ (N.closedStar p).space) ∧
        IsFinitePLBallPair V3 (M.closedStar p).space
          ((M.link p).space ∪ (N.closedStar p).space) ∧
        IsFinitePLBallPair (ℝ × ℝ) (N.closedStar p).space (N.link p).space ∧
        Nonempty (SimplicialComplex.BoundaryVertexHalfBall P N p) ∧
        Nonempty (SimplicialComplex.BoundaryVertexHalfBall M N p) := by
  classical
  obtain ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B, hK, hT, hP, hM, hN, FP, FM,
    hFc, hF, hLK, hTK, hNT, hPT, hMT, hNP, hNM,
    hLf, hNf, hPf, hMf, hNfull, hKs, hLs, hNs, hHF, hgc, hg, hgPL,
    hW, hSW, hu, hi, hTf, hTs, hTW, hPs, hMs, hPMu, hPMi, hfaces, hinter,
    hNpure, hNedge, hpureP, hpureM, hfacets, hstars⟩ :=
    s.exists_original_side_triangle_fibers hR he hSR
  let : Fintype K.faces := hK.fintype
  let : Fintype P.faces := hP.fintype
  let : Fintype M.faces := hM.fintype
  let : Fintype N.faces := hN.fintype
  have hPK : P ≤ K := fun _ ha => hTK (hPT ha)
  have hMK : M ≤ K := fun _ ha => hTK (hMT ha)
  have hfullP := hNfull P (by simp)
  have hfullM := hNfull M (by simp)
  have hcard (a : Finset (t → ℝ × V3)) (ha : a ∈ N.faces) : a.card ≤ 3 := by
    obtain ⟨b, _, hab, hbc⟩ := hNpure a ha
    simpa only [hbc] using Finset.card_le_card hab
  have hlinks : ∀ a ∈ N.faces, a.card = 2 →
      IsFinitePLBallPair ℝ (P.faceLink a).space (N.faceLink a).space ∧
      IsFinitePLBallPair ℝ (M.faceLink a).space (N.faceLink a).space := by
    intro u hu huc
    obtain ⟨p, hpu⟩ := N.nonempty_of_mem_faces hu
    let pN : N.vertices := ⟨p, N.face_subset_vertices hu hpu⟩
    obtain ⟨_, _, _, hf, hinj, _, hint, hmodel, _, _, hPstar, hMstar, _⟩ := hstars pN
    have hcover : ∀ b ∈ (K.closedStar p).faces, b ∈ P.faces ∨ b ∈ M.faces := by
      intro b hb
      exact hfaces b (hTf.symm.subset (mem_iUnion.mpr ⟨pN, hb⟩))
    have hpos := K.isFinitePLBallPair_sphere_side_edge_link N P M hK hPK hMK
      hNP hNM hfullP hpureP hcard hu huc (hNedge u hu huc) hpu
      hf hinj hint hPstar hMstar (fun z hz => (hmodel z hz).1) hcover
    let a : V3 ≃L[ℝ] V3 := ContinuousLinearEquiv.neg ℝ
    let f : (t → ℝ × V3) → V3 := fun z => a (B pN (g z))
    have hfneg : (K.closedStar p).AffineOnFaces f :=
      hf.postcomp a.toContinuousAffineEquiv.toContinuousAffineMap
    have hnegInj : InjOn f (K.closedStar p).space := fun _ hx _ hy h =>
      hinj hx hy (a.injective h)
    have hnegInt : f p ∈ interior (f '' (K.closedStar p).space) := by
      change a (B pN (g p)) ∈
        interior ((a ∘ (fun z => B pN (g z))) '' (K.closedStar p).space)
      rw [image_comp]
      change a.toHomeomorph (B pN (g p)) ∈
        interior (a.toHomeomorph '' ((fun z => B pN (g z)) '' (K.closedStar p).space))
      rw [← a.toHomeomorph.image_interior]
      exact mem_image_of_mem _ hint
    have hnegSide : (M.closedStar p).space =
        (K.closedStar p).space ∩ {z | 0 ≤ f z 0} := by
      change (M.closedStar p).space =
        (K.closedStar p).space ∩ {z | 0 ≤ -((B pN (g z)) 0)}
      simpa only [neg_nonneg] using hMstar
    have hposSide : (P.closedStar p).space =
        (K.closedStar p).space ∩ {z | f z 0 ≤ 0} := by
      change (P.closedStar p).space =
        (K.closedStar p).space ∩ {z | -((B pN (g z)) 0) ≤ 0}
      simpa only [neg_nonpos] using hPstar
    have hnegBoundary (z : t → ℝ × V3) (hz : z ∈ (K.closedStar p).space) :
        z ∈ N.space ↔ f z 0 = 0 := by
      change z ∈ N.space ↔ -((B pN (g z)) 0) = 0
      simpa only [neg_eq_zero] using (hmodel z hz).1
    have hneg := K.isFinitePLBallPair_sphere_side_edge_link N M P hK hMK hPK
      hNM hNP hfullM hpureM hcard hu huc (hNedge u hu huc) hpu
      hfneg hnegInj hnegInt hnegSide hposSide hnegBoundary (fun b hb => (hcover b hb).symm)
    exact ⟨hpos, hneg⟩
  obtain ⟨EP⟩ := FP.exists_edge_family hNP hcard hfullP hNedge
    (fun a ha hac => (hlinks a ha hac).1)
  obtain ⟨EM⟩ := FM.exists_edge_family hNM hcard hfullM hNedge
    (fun a ha hac => (hlinks a ha hac).2)
  have hblocks : ∀ p : N.vertices,
      Nonempty (SimplicialComplex.BoundaryVertexHalfBall P N p) ∧
      Nonempty (SimplicialComplex.BoundaryVertexHalfBall M N p) := by
    intro p
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbP, hbM⟩ := hstars p
    exact ⟨hbP, hbM⟩
  obtain ⟨VP⟩ := EP.exists_vertex_family hNP hcard hfullP (fun p => (hblocks p).1)
  obtain ⟨VM⟩ := EM.exists_vertex_family hNM hcard hfullM (fun p => (hblocks p).2)
  obtain ⟨CP, hCP, hCP0, hCPb, hCPv⟩ := VP.exists_whole_product hfullP
  obtain ⟨CM, hCM, hCM0, hCMb, hCMv⟩ := VM.exists_whole_product hfullM
  exact ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B, hK, hT, hP, hM, hN,
    FP, FM, EP, EM, VP, VM, CP, CM, hCP, hCM,
    (fun x hx => ⟨hCP0 x hx, hCM0 x hx⟩), (fun x => ⟨hCPb x, hCMb x⟩),
    (fun p x => ⟨hCPv p x, hCMv p x⟩),
    hFc, hF, hLK, hTK, hNT, hPT, hMT, hNP, hNM,
    hLf, hNf, hPf, hMf, hNfull, hKs, hLs, hNs, hHF, hgc, hg, hgPL,
    hW, hSW, hu, hi, hTf, hTs, hTW, hPs, hMs, hPMu, hPMi, hfaces, hinter,
    hNpure, hNedge, hpureP, hpureM, hfacets, hstars⟩

end PoincareConjecture.M76

