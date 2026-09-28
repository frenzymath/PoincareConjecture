import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedBoundaryVertexModel
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexGluing

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

open Classical in

theorem exists_protected_boundary_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (b : ChartwisePLBall e D (frontier D)) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : R ≃ₜ K.space) (g : (s → ℝ × V3) → R)
      (HB : (A 0).space ≃ₜ frontier R) (hK : K.faces.Finite)
      (hL : (A 0).faces.Finite),
      let : Fintype K.faces := hK.fintype
      let : Fintype (A 0).faces := hL.fintype
      ∃ C : ((A 0).space ×ˢ I : Set ((s → ℝ × V3) × ℝ)) ≃ₜ
          (K.barycentricNeighborhood (A 0)).space,
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      (∀ a, A a ≤ K ∧ (A a).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A a).vertices) → t ∈ (A a).faces) ∧
      K.space = F '' R ∧ (A 0).space = F '' frontier R ∧
      (A 1).space = F '' D ∧ (A 2).space = F '' frontier D ∧
      (∀ x : R, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      (∀ z : (A 0).space, (HB z : X) = (g z : X)) ∧
      C.IsFinitePL ∧
      (∀ (x : s → ℝ × V3) (hx : x ∈ (A 0).space),
        (C ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : s → ℝ × V3) = x) ∧
      ∀ x : ((A 0).space ×ˢ I : Set ((s → ℝ × V3) × ℝ)),
        (C x : s → ℝ × V3) ∈ (A 0).space ↔ (x : (s → ℝ × V3) × ℝ).2 = 0 := by
  classical
  obtain ⟨s, F, K, A, H, g, HB, hK, hL, T, hFc, hF, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, _, _, _, hHB, hBpure, hBedge, _, hedge, _, hvertex⟩ :=
    exists_protected_boundary_vertex_model hR he hDR b
  let : Fintype K.faces := hK.fintype
  let : Fintype (A 0).faces := hL.fintype
  have hcard (u : Finset (s → ℝ × V3)) (hu : u ∈ (A 0).faces) : u.card ≤ 3 := by
    obtain ⟨v, _, huv, hvc⟩ := hBpure u hu
    have hle := Finset.card_le_card huv
    rwa [hvc] at hle
  obtain ⟨P⟩ := T.exists_edge_family (hA 0).1 hcard (hA 0).2.2 hBedge hedge
  obtain ⟨V⟩ := P.exists_vertex_family (hA 0).1 hcard (hA 0).2.2
    (fun p => hvertex p p.property)
  obtain ⟨C, hC, hC0, hCb, _⟩ := V.exists_whole_product (hA 0).2.2
  exact ⟨s, F, K, A, H, g, HB, hK, hL, C, hFc, hF, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, hHB, hC, hC0, hCb⟩

end PoincareConjecture.M76
