import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel
import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierComponents
import PoincareConjecture.Proofs.M76.Wall.OriginalComponentSphere

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3}

open Classical in

theorem PLDomain.exists_new_frontier_component_models
    {N B F : Set X} (he : PLDomain e N) (hN : IsCompact N) (hNne : N.Nonempty)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier N = B ∪ F) (hFne : F.Nonempty) :
    ∃ (s : Finset N) (phi : X → (s → ℝ × V3))
      (K A : SimplicialComplex ℝ (s → ℝ × V3))
      (H : N ≃ₜ K.space) (g : (s → ℝ × V3) → N)
      (HB : A.space ≃ₜ frontier N)
      (n : ℕ) (pick : Fin n ↪ A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (S : Fin n → Set X),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ A ≤ K ∧ A.faces.Finite ∧
      (∀ t ∈ K.faces, (∀ p ∈ t, p ∈ A.vertices) → t ∈ A.faces) ∧
      K.space = phi '' N ∧ A.space = phi '' frontier N ∧
      (∀ x : N, (H x : s → ℝ × V3) = phi x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      (∀ z : A.space, (HB z : X) = (g z : X)) ∧
      (∀ x : frontier N, (HB.symm x : s → ℝ × V3) =
        (H ⟨x, he.closed.frontier_subset x.property⟩ : s → ℝ × V3)) ∧
      (∀ z ∈ K.space, (g z : X) ∈ frontier N ↔ z ∈ A.space) ∧
      (∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph X V3,
        (∀ i, (e i).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
        MapsTo (fun z => (g z : X)) (K.closedStar p).space C.source ∧
        (K.closedStar p).AffineOnFaces (fun z => C (g z)) ∧
        (C.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y))) ∧
      (∀ t ∈ A.faces, ∃ u ∈ A.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ A.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ A.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space) ∧
      0 < n ∧
      (∀ i, S i = (fun z => (g z : X)) '' (A.edgeComponentComplex (pick i)).space) ∧
      (⋃ i, S i) = F ∧ (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, IsCompact (S i) ∧ IsConnected (S i) ∧ S i ⊆ F ∧
        (∀ x ∈ S i, connectedComponentIn F x = S i) ∧
        PolyhedralPLInCharts e (fun z => (g z : X))
          (A.edgeComponentComplex (pick i)).space ∧
        ∃ HC : (A.edgeComponentComplex (pick i)).space ≃ₜ S i,
          ∀ z, (HC z : X) = (g z : X)) ∧
      ∀ i, Nat.card (A.edgeComponentComplex (pick i)).vertices +
        Nat.card (Triangle
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) =
        Nat.card (Edge
          (A.edgeComponentComplex (pick i)).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
            2 →
        Nonempty (ChartwisePLSphere e (S i)) := by
  classical
  obtain ⟨s, phi, K, A, H, g, HB, hphi, hphiPL, hK, hAK, hA, hfull, hKs,
    hAs, hH, hgc, hg, hgPL, hHB, hHBinv, hboundary, hstars, hpure, hcofaces, hlinks⟩ :=
    he.exists_original_frontier_surface_model hN hNne
  obtain ⟨n, pick, S, hn, hS, hunion, hdisjoint, hcomponents⟩ :=
    exists_original_frontier_components K A hK hAK H g hg hgPL HB hHB
      hB hF hBF hfront hFne
  have hgi : InjOn (fun z => (g z : X)) K.space := by
    intro x hx y hy hxy
    have hinv : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ :=
      Subtype.ext ((hg ⟨x, hx⟩).symm.trans (hxy.trans (hg ⟨y, hy⟩)))
    exact congrArg Subtype.val (H.symm.injective hinv)
  refine ⟨s, phi, K, A, H, g, HB, n, pick, S, hphi, hphiPL, hK, hAK, hA,
    hfull, hKs, hAs, hH, hgc, hg, hgPL, hHB, hHBinv, hboundary, hstars,
    hpure, hcofaces, hlinks, hn, hS, hunion, hdisjoint, hcomponents, ?_⟩
  intro i hcount
  rw [hS i]
  exact exists_original_component_sphere_of_count K A hK hAK hgPL hgi
    hpure hcofaces hlinks (pick i) hcount

end PoincareConjecture.M76
