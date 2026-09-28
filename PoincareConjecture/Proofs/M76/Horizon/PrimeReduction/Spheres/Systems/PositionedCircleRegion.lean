import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PositionedCircleBallCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.CircleSurgeryRegion










set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex
namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_positioned_sphere_system_circle_region
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
    {d : Set V3} (hd : IsFinitePLBallPair P2 d (R.boundary ℝ))
    (hdS : d ⊆ sphere (0 : V3) 1)
    (hrimage : (sS i).map '' R.boundary ℝ = Q.symm '' L.boundary ℝ)
    {O : Set X} (hO : IsOpen O) (hrO : Q.symm '' L.boundary ℝ ⊆ O)
    {D : Set V3} (hD : IsFinitePLBallPair P2 D (L.boundary ℝ))
    (hDT : D ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))))
    (hDfamily : (Q.symm '' D) ∩ (⋃ j, S j) = Q.symm '' L.boundary ℝ)
    (hDO : Q.symm '' D ⊆ O) :
    ∃ (H : V3 →ᴬ[ℝ] ℝ) (l : ℕ) (sigma : C3 → V3),
      H.linear ≠ 0 ∧
      (∀ x, H x = 0 ↔ x ∈ affineSpan ℝ (A '' (s : Set E))) ∧
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)) ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))
        (Q.target ∩ Q.symm ⁻¹' O) ∧
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
          caps b ⊆ Q.target ∧ Q.symm '' caps b ⊆ O ∧
          (Q.symm '' caps b) ∩ (⋃ j, S j) =
            Q.symm '' ((fun t => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) ''
              Icc 0 (l + 3)) ∧
          Disjoint (caps b) (convexHull ℝ (A '' (s : Set E)))) ∧
        Disjoint (caps true) (caps false) ∧
        Disjoint (Q.symm '' caps true) (Q.symm '' caps false) ∧
        ∃ B bd : Set V3, IsFinitePLBallPair C3 B bd ∧ D ⊆ interior B ∧
          B ⊆ Q.target ∩ Q.symm ⁻¹' O ∧
          sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)) ⊆ interior B ∧
          (∀ b, caps b ⊆ interior B) ∧
          let band := (fun z : P2 => sigma ((z.1, 0), z.2)) ''
            (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3))
          let boundary := band ∪ (caps true ∪ caps false)
          ∃ region : Set V3, IsFinitePLBallPair C3 region boundary ∧
            region ⊆ interior B ∧ frontier region = boundary ∧
            frontier region ∩ (Q.symm ⁻¹' (⋃ j, S j)) = band ∧
            Q.symm '' region ⊆ O := by
  obtain ⟨H, l, sigma, hH, hplane, hSigma, hMap, hInt, hTriangle, hSphere,
      hMember, hAxis, hImage, hFib, hOther, hzero, hsides, caps, hcaps,
      hcapsDis, hphysicalDis, B, bd, hB, hDB, hBV, hTubeB, hCapsB⟩ :=
    exists_positioned_sphere_system_ball_caps S sS hdis K g hgi hs hs3 Q hQ A
      hmap hA G hG hGT hphysicalGraph hdim hinterior hexterior hcrossings C L hL hLi
      hLC hLinter i R hR hRi hd hdS hrimage hO hrO hD hDT hDfamily hDO
  let M := Q.symm ⁻¹' (⋃ j, S j)
  have hsphere : ∀ z ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
      sigma z ∈ M ↔ z.1.2 = 0 := by
    intro z hz
    exact (hSphere ⟨z, hz⟩).trans (signedTubeSheet_coordinate_iff z.1 hz.1 1)
  have hcapM (b : Bool) : caps b ∩ M =
      (fun t => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) '' Icc 0 (l + 3) := by
    apply Subset.antisymm
    · intro x hx
      have hp := (hcaps b).2.2.2.1.subset ⟨⟨x, hx.1, rfl⟩, hx.2⟩
      obtain ⟨y, hy, hyx⟩ := hp
      have heq : y = x := Q.symm.injOn ((hcaps b).2.1 ((hcaps b).1.1 hy))
        ((hcaps b).2.1 hx.1) hyx
      exact heq ▸ hy
    · intro x hx
      exact ⟨(hcaps b).1.1 hx, ((hcaps b).2.2.2.1.symm.subset ⟨x, hx, rfl⟩).2⟩
  obtain ⟨_, _, region, hRegion, hRegionB, hFrontier, hFrontierM⟩ :=
    exists_circle_surgery_region (by simp : Module.finrank ℝ V3 = 3)
      (by positivity : (0 : ℝ) < l + 3) sigma hSigma
      (by intro x hx y hy; simpa only [and_comm] using hFib ⟨x, hx⟩ ⟨y, hy⟩)
      hsphere caps (fun b => (hcaps b).1) hcapM hcapsDis hB hTubeB hCapsB
  refine ⟨H, l, sigma, hH, hplane, hSigma, hMap, hInt, hTriangle, hSphere,
    hMember, hAxis, hImage, hFib, hOther, hzero, hsides, caps, hcaps,
    hcapsDis, hphysicalDis, B, bd, hB, hDB, hBV, hTubeB, hCapsB,
    region, hRegion, hRegionB, hFrontier, hFrontierM, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (hBV (interior_subset (hRegionB hx))).2

end PoincareConjecture.M76
