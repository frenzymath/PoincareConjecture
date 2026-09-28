import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PositionedCircleRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleCollarRegionIncidence
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact

set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex
namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem exists_witness_protected_sphere_system_circle_region
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target)
    (hphysicalGraph : Q.symm '' G.space = (⋃ i, S i) ∩
      (g '' convexHull ℝ (s : Set E)))
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (hcrossings : ∀ w ∈ G.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
      ∀ V : Set V3, IsOpen V → w ∈ V →
        ∃ B : OpenPartialHomeomorph V3 C3,
          w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source,
            x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {n : ℕ} (L : Polygon V3 (n + 3))
    (hL : L.HasSimplicialEdges) (hLi : Function.Injective L)
    (hLC : L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))
    (hLinter : L.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))))
    (i : κ) {m : ℕ} (R : Polygon V3 (m + 3))
    (hR : R.HasSimplicialEdges) (hRi : Function.Injective R)
    (d : Bool → Set V3) (hd : ∀ b, IsFinitePLBallPair P2 (d b) (R.boundary ℝ))
    (hdwhole : d true ∪ d false = sphere (0 : V3) 1)
    (hdinter : d true ∩ d false = R.boundary ℝ)
    (hrimage : (sS i).map '' R.boundary ℝ = Q.symm '' L.boundary ℝ)
    {O : Set X} (hO : IsOpen O) (hrO : Q.symm '' L.boundary ℝ ⊆ O)
    {D : Set V3} (hD : IsFinitePLBallPair P2 D (L.boundary ℝ))
    (hDT : D ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))))
    (hDfamily : (Q.symm '' D) ∩ (⋃ j, S j) = Q.symm '' L.boundary ℝ)
    (hDO : Q.symm '' D ⊆ O) :
    ∃ (p : Bool → V3) (U : Set X),
      IsOpen U ∧ Q.symm '' D ⊆ U ∧ U ⊆ O ∧
      (sS i).map (p true) ≠ (sS i).map (p false) ∧
      (∀ b, p b ∈ d b \ R.boundary ℝ ∧ (sS i).map (p b) ∈ S i ∧
        (sS i).map (p b) ∉ Q.symm '' D ∧ (sS i).map (p b) ∉ U) ∧
      (∀ j, j ≠ i → Disjoint U (S j)) ∧
      ∃ (H : V3 →ᴬ[ℝ] ℝ) (l : ℕ) (sigma : C3 → V3),
      H.linear ≠ 0 ∧
      (∀ x, H x = 0 ↔ x ∈ affineSpan ℝ (A '' (s : Set E))) ∧
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)) ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))
        (Q.target ∩ Q.symm ⁻¹' U) ∧
      L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        sigma x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (x : C3).1 ∈ signedTubeSheet 0) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        Q.symm (sigma x) ∈ ⋃ j, S j ↔ (x : C3).1 ∈ signedTubeSheet 1) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        Q.symm (sigma x) ∈ S i ↔ (x : C3).1 ∈ signedTubeSheet 1) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        sigma x ∈ L.boundary ℝ ↔ (x : C3).1 = (0, 0)) ∧
      (fun t : ℝ => sigma ((0, 0), t)) '' Icc (0 : ℝ) (l + 3) = L.boundary ℝ ∧
      (∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        sigma x = sigma y ↔ (x : C3).1 = (y : C3).1 ∧
          ((x : C3).2 = (y : C3).2 ∨
            ((x : C3).2 = 0 ∧ (y : C3).2 = l + 3) ∨
            ((y : C3).2 = 0 ∧ (x : C3).2 = l + 3))) ∧
      (∀ j, j ≠ i → Disjoint
        (Q.symm '' (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)))) (S j)) ∧
      (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
        H (sigma x) = 0 ↔ x.1.1 = 0) ∧
      (((∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
          0 < x.1.1 → 0 < H (sigma x)) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
          x.1.1 < 0 → H (sigma x) < 0)) ∨
       ((∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
          0 < x.1.1 → H (sigma x) < 0) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
          x.1.1 < 0 → 0 < H (sigma x)))) ∧
      ∃ caps : Bool → Set V3,
        (∀ b, IsFinitePLBallPair P2 (caps b)
          ((fun t => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) '' Icc 0 (l + 3)) ∧
          caps b ⊆ Q.target ∧ Q.symm '' caps b ⊆ U ∧
          (Q.symm '' caps b) ∩ (⋃ j, S j) =
            Q.symm '' ((fun t => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) ''
              Icc 0 (l + 3)) ∧
          Disjoint (caps b) (convexHull ℝ (A '' (s : Set E)))) ∧
        Disjoint (caps true) (caps false) ∧
        Disjoint (Q.symm '' caps true) (Q.symm '' caps false) ∧
        ∃ B bd : Set V3, IsFinitePLBallPair C3 B bd ∧ D ⊆ interior B ∧
          B ⊆ Q.target ∩ Q.symm ⁻¹' U ∧
          sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)) ⊆ interior B ∧
          (∀ b, caps b ⊆ interior B) ∧
          let band := (fun z : P2 => sigma ((z.1, 0), z.2)) ''
            (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3))
          let boundary := band ∪ (caps true ∪ caps false)
          ∃ region : Set V3, IsFinitePLBallPair C3 region boundary ∧
            region ⊆ interior B ∧ frontier region = boundary ∧
            frontier region ∩ (Q.symm ⁻¹' (⋃ j, S j)) = band ∧
            Q.symm '' region ⊆ U ∧
            (Q.symm '' region) ∩ (⋃ j, S j) = Q.symm '' band ∧
            Disjoint (interior (Q.symm '' region)) (⋃ j, S j) ∧
            ∃ (φ : P2 → V3) (k : Bool → Set V3),
              FinitePiecewiseAffineOn φ (Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) (l + 3)) ∧
              MapsTo φ (Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) (l + 3)) Sphere ∧
              (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) (l + 3),
                (sS i).map (φ z) = Q.symm (sigma ((z.1, 0), z.2))) ∧
              ((fun t : ℝ => φ (0, t)) '' Icc (0 : ℝ) (l + 3) = R.boundary ℝ) ∧
              (∀ b,
                let q := (fun t : ℝ => φ (if b then 1 / 4 else -1 / 4, t)) ''
                  Icc (0 : ℝ) (l + 3)
                IsFinitePLBallPair P2 (k b) q ∧ k b ⊆ Sphere ∧
                IsFinitePLBallPair P2 (Sphere \ (k b \ q)) q ∧
                (sS i).map '' q = (fun t => Q.symm
                  (sigma ((if b then 1 / 4 else -1 / 4, 0), t))) '' Icc 0 (l + 3) ∧
                k b ∩ (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3))) = q ∧
                Disjoint (k b) (R.boundary ℝ) ∧
                (Q.symm '' region) ∩ ((sS i).map '' k b) = (sS i).map '' q) ∧
              Disjoint (k true) (k false) ∧
              (k true ∪ k false) ∪
                (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3))) = Sphere := by
  classical
  have hdS (b : Bool) : d b ⊆ Sphere := by
    cases b
    · exact subset_union_right.trans hdwhole.subset
    · exact subset_union_left.trans hdwhole.subset
  have hrS : R.boundary ℝ ⊆ Sphere := (hd true).1.trans (hdS true)
  have hrMember : (sS i).map '' R.boundary ℝ ⊆ S i := by
    rintro _ ⟨x, hx, rfl⟩
    rw [(sS i).map_eq ⟨x, hrS hx⟩]
    exact ((sS i).parametrization ⟨x, hrS hx⟩).property
  obtain ⟨p, U₀, hU₀, hDU₀, hU₀O, hpne, hp₀⟩ :=
    (sS i).exists_circle_cut_witness_neighborhood d hd hdwhole hdinter
      (subset_iUnion S i) (hDfamily.trans hrimage.symm) hO hDO
  let others := ⋃ j : {j : κ // j ≠ i}, S j.val
  have hOthers : IsClosed others :=
    isClosed_iUnion_of_finite fun j => (sS j.val).isCompact.isClosed
  let U := U₀ \ others
  have hU : IsOpen U := hU₀.sdiff hOthers
  have hUO : U ⊆ O := sdiff_subset.trans hU₀O
  have hDU : Q.symm '' D ⊆ U := by
    intro x hx
    refine ⟨hDU₀ hx, ?_⟩
    intro hxOthers
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxOthers
    have hxrim := hDfamily.subset ⟨hx, mem_iUnion.mpr ⟨j.val, hj⟩⟩
    have hxi := hrMember (hrimage.symm.subset hxrim)
    exact disjoint_left.mp (hdis (Ne.symm j.property)) hxi hj
  have hUother (j : κ) (hji : j ≠ i) : Disjoint U (S j) := by
    apply disjoint_left.mpr
    intro x hx hxj
    exact hx.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩)
  have hp (b : Bool) : p b ∈ d b \ R.boundary ℝ ∧ (sS i).map (p b) ∈ S i ∧
      (sS i).map (p b) ∉ Q.symm '' D ∧ (sS i).map (p b) ∉ U :=
    ⟨(hp₀ b).1, (hp₀ b).2.1, (hp₀ b).2.2.1, fun hx => (hp₀ b).2.2.2 hx.1⟩
  obtain ⟨H, l, sigma, hH, hplane, hSigma, hMap, hInt, hTriangle, hSphere,
      hMember, hAxis, hImage, hFib, hOther, hzero, hsides, caps, hcaps,
      hcapsDis, hphysicalDis, B, bd, hB, hDB, hBV, hTubeB, hCapsB,
      region, hRegion, hRegionB, hFrontier, hFrontierM, hRegionU⟩ :=
    exists_positioned_sphere_system_circle_region S sS hdis K g hgi hs hs3 Q hQ A
      hmap hA G hG hGT hphysicalGraph hdim hinterior hexterior hcrossings C L hL hLi
      hLC hLinter i R hR hRi (hd true) (hdS true) hrimage hU
      ((image_mono hD.1).trans hDU) hD hDT hDfamily hDU
  let band := (fun z : P2 => sigma ((z.1, 0), z.2)) ''
    (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3))
  have hRegionQ : region ⊆ Q.target := fun x hx =>
    (hBV (interior_subset (hRegionB hx))).1
  have hPhysicalCompact : IsCompact (Q.symm '' region) :=
    hRegion.isCompact.image_of_continuousOn (Q.continuousOn_symm.mono hRegionQ)
  have hPhysicalQ : Q.symm '' region ⊆ Q.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact Q.map_target (hRegionQ hx)
  have hPhysicalFrontier : frontier (Q.symm '' region) = Q.symm '' frontier region := by
    have hh := Q.symm.image_frontier_eq_target_inter_of_closure_subset
      (D := region) (by rwa [hRegion.isCompact.isClosed.closure_eq])
    change Q.symm '' frontier region = Q.source ∩ frontier (Q.symm '' region) at hh
    rw [inter_eq_right.mpr (hPhysicalCompact.isClosed.frontier_subset.trans hPhysicalQ)] at hh
    exact hh.symm
  have hfrontFamily : frontier (Q.symm '' region) ∩ (⋃ j, S j) = Q.symm '' band := by
    rw [hPhysicalFrontier, ← image_inter_preimage, hFrontierM]
  have hbandMember : Q.symm '' band ⊆ S i := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hz' : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) (l + 3) :=
      ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
    have hdom : ((z.1, 0), z.2) ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3) := by
      simpa only [signedSheetStripMap_apply, Fin.reduceEq, if_false] using
        signedSheetStripMap_mem (1 : Fin 2) hz'
    exact (hMember ⟨_, hdom⟩).mpr ((signedTubeSheet_coordinate_iff _ hdom.1 1).mpr rfl)
  have hfrontSelected : frontier (Q.symm '' region) ∩ S i = Q.symm '' band := by
    apply Subset.antisymm
    · intro x hx
      exact hfrontFamily.subset ⟨hx.1, (subset_iUnion S i) hx.2⟩
    · intro x hx
      exact ⟨(hfrontFamily.symm.subset hx).1, hbandMember hx⟩
  have hRimAxis : (sS i).map '' R.boundary ℝ =
      (fun t => Q.symm (sigma ((0, 0), t))) '' Icc (0 : ℝ) (l + 3) := by
    rw [hrimage, ← hImage, image_image]
  obtain ⟨φ, k, hφ, hφS, hφval, hφaxis, hk, hkdis, hkwhole, hSelected, hIntSelected⟩ :=
    (sS i).exists_circle_collar_region_incidence Q hQ d hd hdwhole hdinter p
      (fun b => (hp b).1) (fun b => (hp b).2.2.2)
      (by positivity : (0 : ℝ) < l + 3) sigma hSigma hMap
      (fun z hz hz0 => (hMember ⟨z, hz⟩).mpr
        ((signedTubeSheet_coordinate_iff z.1 hz.1 1).mpr hz0))
      (by intro x hx y hy; simpa only [and_comm] using hFib ⟨x, hx⟩ ⟨y, hy⟩)
      hRimAxis hPhysicalCompact.isClosed hRegionU
      (by simpa only [band, image_image] using hfrontSelected)
  have hSelected' : (Q.symm '' region) ∩ S i = Q.symm '' band := by
    simpa only [band, image_image] using hSelected
  have hFull : (Q.symm '' region) ∩ (⋃ j, S j) = Q.symm '' band := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxS⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxS
      by_cases hji : j = i
      · exact hSelected'.subset ⟨hx, hji ▸ hxj⟩
      · exact (disjoint_left.mp (hUother j hji) (hRegionU hx) hxj).elim
    · intro x hx
      exact ⟨(hSelected'.symm.subset hx).1, (subset_iUnion S i) (hbandMember hx)⟩
  have hInterior : Disjoint (interior (Q.symm '' region)) (⋃ j, S j) := by
    apply disjoint_left.mpr
    intro x hx hxS
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxS
    by_cases hji : j = i
    · exact disjoint_left.mp hIntSelected hx (hji ▸ hxj)
    · exact disjoint_left.mp (hUother j hji) (hRegionU (interior_subset hx)) hxj
  exact ⟨p, U, hU, hDU, hUO, hpne, hp, hUother,
    H, l, sigma, hH, hplane, hSigma, hMap, hInt, hTriangle, hSphere,
    hMember, hAxis, hImage, hFib, hOther, hzero, hsides, caps, hcaps,
    hcapsDis, hphysicalDis, B, bd, hB, hDB, hBV, hTubeB, hCapsB,
    region, hRegion, hRegionB, hFrontier, hFrontierM, hRegionU, hFull, hInterior,
    φ, k, hφ, hφS, hφval, hφaxis, hk, hkdis, hkwhole⟩

end PoincareConjecture.M76
