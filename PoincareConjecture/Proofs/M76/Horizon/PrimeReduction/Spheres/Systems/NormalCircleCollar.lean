import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PositionedCircleCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.OriginalCircleNormalNeighborhood









set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex
namespace PoincareConjecture.M76
open Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_positioned_sphere_system_normal_circle_collar
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
    {O : Set X} (hO : IsOpen O) (hrO : Q.symm '' L.boundary ℝ ⊆ O) :
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
          x.1.1 < 0 → 0 < H (sigma x)))) := by
  obtain ⟨H, U, hH, hplane, hU, hTU, hzero⟩ :=
    exists_original_triangle_normal_neighborhood K g hgi hs hs3 Q A hmap hA
  have hTQ : convexHull ℝ (A '' (s : Set E)) ⊆ Q.target := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hx
    change A u ∈ Q.target
    rw [← hA hu]
    exact Q.map_source (hmap hu)
  have hLQ := hLinter.trans (intrinsicInterior_subset.trans hTQ)
  let O' := O ∩ (Q.source ∩ Q ⁻¹' U)
  have hO' : IsOpen O' := hO.inter (Q.isOpen_inter_preimage hU)
  have hrO' : Q.symm '' L.boundary ℝ ⊆ O' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hrO ⟨x, hx, rfl⟩, Q.map_target (hLQ hx), ?_⟩
    change Q (Q.symm x) ∈ U
    rw [Q.right_inv (hLQ hx)]
    exact hTU (hLinter hx)
  obtain ⟨l, sigma, hSigma, hMap, hInt, hTriangle, hSphere, hMember, hAxis,
      hImage, hFib, hOther⟩ :=
    exists_positioned_sphere_system_circle_collar S sS hdis K g hgi hs hs3 Q hQ A
      hmap hA G hG hGT hphysicalGraph hdim hinterior hexterior hcrossings C L hL hLi
      hLC hLinter i R hR hRi hd hdS hrimage hO' hrO'
  have hSigmaU : MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)) U := by
    intro x hx
    have h := (hMap hx).2.2.2
    change Q (Q.symm (sigma x)) ∈ U at h
    rwa [Q.right_inv (hMap hx).1] at h
  have hSigmaZero : ∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
      H (sigma x) = 0 ↔ x.1.1 = 0 := by
    intro x hx
    exact (hzero _ (hSigmaU hx)).trans
      ((hTriangle ⟨x, hx⟩).trans (by
        simpa using signedTubeSheet_coordinate_iff x.1 hx.1 (0 : Fin 2)))
  have ha : ((0, 0), (0 : ℝ)) ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3) :=
    ⟨(signedTubeDiamond_coordinate_iff _).mpr (by norm_num), le_rfl, by positivity⟩
  have hAxisInt : sigma ((0, 0), 0) ∈
      interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))) :=
    hInt (hImage.subset ⟨0, ⟨le_rfl, by positivity⟩, rfl⟩)
  refine ⟨H, l, sigma, hH, hplane, hSigma, ?_, hInt, hTriangle, hSphere,
    hMember, hAxis, hImage, hFib, hOther, hSigmaZero, ?_⟩
  · exact fun x hx => ⟨(hMap hx).1, (hMap hx).2.1⟩
  · exact circle_tube_affine_height_sides (by positivity) sigma hSigma.continuousOn
      H hH hSigmaZero hAxisInt

end PoincareConjecture.M76

