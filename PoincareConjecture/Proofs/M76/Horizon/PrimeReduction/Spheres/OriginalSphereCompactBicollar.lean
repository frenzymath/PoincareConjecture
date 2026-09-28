import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereSideProducts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Barycentric.TwoSideNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Products.TwoSideProduct

set_option autoImplicit false
set_option maxHeartbeats 1800000

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem ChartwisePLSphere.exists_original_compact_bicollar
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
          (M.barycentricNeighborhood N).space)
        (C : (N.space ×ˢ Icc (-1 : ℝ) 1 : Set ((t → ℝ × V3) × ℝ)) ≃ₜ
          (K.barycentricNeighborhood N).space),
      C.IsFinitePL ∧
      ((K.barycentricNeighborhood N).space =
        (P.barycentricNeighborhood N).space ∪ (M.barycentricNeighborhood N).space) ∧
      ((P.barycentricNeighborhood N).space ∩ (M.barycentricNeighborhood N).space =
        N.space) ∧
      (∀ z : (N.space ×ˢ I : Set ((t → ℝ × V3) × ℝ)),
        (C ⟨z, ⟨z.property.1, by linarith [z.property.2.1], z.property.2.2⟩⟩ :
          t → ℝ × V3) = CP z) ∧
      (∀ z : (N.space ×ˢ Icc (-1 : ℝ) 0 : Set ((t → ℝ × V3) × ℝ)),
        (C ⟨z, ⟨z.property.1, z.property.2.1, by linarith [z.property.2.2]⟩⟩ :
          t → ℝ × V3) =
          CM ⟨((z : (t → ℝ × V3) × ℝ).1, -(z : (t → ℝ × V3) × ℝ).2),
            ⟨z.property.1, by constructor <;> linarith [z.property.2.1, z.property.2.2]⟩⟩) ∧
      (∀ (x : t → ℝ × V3) (hx : x ∈ N.space),
        (C ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : t → ℝ × V3) = x) ∧
      (∀ z, (C z : t → ℝ × V3) ∈ N.space ↔ (z : (t → ℝ × V3) × ℝ).2 = 0) ∧
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
  obtain ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B, hK, hT, hP, hM, hN,
    FP, FM, EP, EM, VP, VM, CP, CM, hCP, hCM, hbase, hzero, hlocal, hdata⟩ :=
    s.exists_original_side_products hR he hSR
  let : Fintype K.faces := hK.fintype
  let : Fintype P.faces := hP.fintype
  let : Fintype M.faces := hM.fintype
  let : Fintype N.faces := hN.fintype
  have hretained := hdata
  obtain ⟨_, _, _, hTK, _, hPT, hMT, hNP, hNM,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTf, hTs,
    _, _, _, hPMu, hPMi, _⟩ := hdata
  have hPK : P ≤ K := fun _ ha => hTK (hPT ha)
  have hMK : M ≤ K := fun _ ha => hTK (hMT ha)
  have hcover : ∀ p ∈ N.vertices, (K.closedStar p).space ⊆ P.space ∪ M.space := by
    intro p hp x hx
    exact hPMu.symm.subset (hTs.symm.subset (mem_iUnion.mpr ⟨⟨p, hp⟩, hx⟩))
  obtain ⟨hunion, hinter⟩ :=
    K.barycentricNeighborhood_two_sides N P M hPK hMK hNP hNM hcover hPMi
  let U : Bool → Set (t → ℝ × V3) := fun b =>
    if b then (P.barycentricNeighborhood N).space else (M.barycentricNeighborhood N).space
  let D : ∀ b, (N.space ×ˢ I : Set ((t → ℝ × V3) × ℝ)) ≃ₜ U b :=
    fun b => Bool.rec CM CP b
  have hD : ∀ b, (D b).IsFinitePL := by
    intro b
    cases b
    · exact hCM
    · exact hCP
  have hDbase : ∀ b (x : t → ℝ × V3) (hx : x ∈ N.space),
      (D b ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : t → ℝ × V3) = x := by
    intro b x hx
    cases b
    · exact (hbase x hx).2
    · exact (hbase x hx).1
  have hDzero : ∀ b z, (D b z : t → ℝ × V3) ∈ N.space ↔
      (z : (t → ℝ × V3) × ℝ).2 = 0 := by
    intro b z
    cases b
    · exact (hzero z).2
    · exact (hzero z).1
  obtain ⟨C0, hC0, hpos, hneg, hCbase, hCzero⟩ :=
    Homeomorph.exists_two_side_product N.space U D hD hDbase hDzero hinter
  let C := C0.trans (Homeomorph.setCongr hunion.symm)
  have hC : C.IsFinitePL := hC0.setCongr rfl hunion.symm
  exact ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B, hK, hT, hP, hM, hN,
    FP, FM, EP, EM, VP, VM, CP, CM, C, hC, hunion, hinter,
    hpos, hneg, hCbase, hCzero, hCP, hCM, hbase, hzero, hlocal, hretained⟩

end PoincareConjecture.M76
