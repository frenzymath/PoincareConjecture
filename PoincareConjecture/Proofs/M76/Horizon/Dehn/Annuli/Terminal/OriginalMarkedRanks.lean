import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.RimRefinement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.GeometricRestriction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.MarkedRims
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts

set_option autoImplicit false

universe v w z

open Set Metric Geometry
open PoincareConjecture.M76.Dehn
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {M : Type w} {ι : Type z} [TopologicalSpace M]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq E]
  {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {f : (V1 × V2) → M}
  {r : M → ℝ} {C : Set M}

theorem Stage.exists_marked_terminal_rank_refinement (st : Stage e S f r C)
    (hS : S.space = ProtectedAnnulus.source)
    (hinj : Function.Injective (fun u : Q2 => f (ProtectedAnnulus.endpoint false, u)))
    {N : Set st.Carrier} (hDN : st.sourceMap '' S.space ⊆ N)
    {a : C(N, N)}
    (H : (ContinuousMap.id N).HomotopyRel a
      (Subtype.val ⁻¹' (st.sourceMap '' S.space)))
    (ha : ∀ y, (a y : st.Carrier) ∈ st.sourceMap '' S.space)
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    (J : N ≃ₜ K.space) (F : st.Carrier → E) (g : E → N)
    (hJF : ∀ x : N, (J x : E) = F x)
    (hg : ∀ z : K.space, (g z : st.Carrier) = (J.symm z : st.Carrier))
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (st.charts i).symm) (st.charts i).target)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z => (g z : st.Carrier)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (∀ k, (st.charts k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)))
    (hterminal : ∀ (Y : Type (max w v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → st.Carrier),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
      ∀ negative : C(Q2, Y),
        (∀ u, p (negative u) = st.sourceMap (ProtectedAnnulus.endpoint false, u)) → False) :
    ∃ (R B : SimplicialComplex ℝ E) (hR : R.faces.Finite) (JR : N ≃ₜ R.space),
      R.IsSubdivision K ∧ B ≤ R ∧ B.space = A.space ∧
      (∀ s ∈ R.faces, (∀ p ∈ s, p ∈ B.vertices) → s ∈ B.faces) ∧
      (∀ x : N, (JR x : E) = F x) ∧
      (∀ z : R.space, (g z : st.Carrier) = (JR.symm z : st.Carrier)) ∧
      (∀ p ∈ R.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
        MapsTo (fun z => (g z : st.Carrier)) (R.closedStar p).space B.source ∧
        (R.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
        (∀ k, (st.charts k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y))) ∧
      (letI : Fintype R.vertices := (R.finite_vertices_of_finite_faces hR).fintype
       Module.finrank (ZMod 2)
           (LinearMap.ker (edgeCoboundary R.vertexAbstractComplex.toPreAbstractSimplicialComplex)) ≤
         Module.finrank (ZMod 2) (LinearMap.range
           (vertexCoboundary R.vertexAbstractComplex.toPreAbstractSimplicialComplex)) + 1) := by
  classical
  let γ := st.annulusRim hS false
  have hγD (u : Q2) : γ u ∈ st.sourceMap '' S.space :=
    st.annulusRim_range_subset hS false (mem_range_self u)
  let Q := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hQ := squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hQs : Q.space = Q2 :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  have hγPL : FinitePiecewiseAffineOn (F ∘ st.annulusRimMap false) Q2 := by
    have h := (st.annulusRim_polyhedral hS false)
    rw [← hQs] at h
    simpa only [hQs] using h.finitePiecewiseAffineOn_comp Q hQ hFPL
  have hγN (u : Q2) : γ u ∈ N := hDN (hγD u)
  have hγinj : InjOn (F ∘ st.annulusRimMap false) Q2 := by
    intro u hu v hv huv
    have hJu : J ⟨γ ⟨u, hu⟩, hγN _⟩ = J ⟨γ ⟨v, hv⟩, hγN _⟩ := by
      apply Subtype.ext
      rw [hJF, hJF]
      change F (st.annulusRimMap false u) = F (st.annulusRimMap false v)
      exact huv
    have hγuv := congrArg Subtype.val (J.injective hJu)
    exact congrArg Subtype.val
      ((st.annulusRim_isClosedEmbedding hS false hinj).injective hγuv)
  have hγK : MapsTo (F ∘ st.annulusRimMap false) Q2 K.space := by
    intro u hu
    have h := (J ⟨γ ⟨u, hu⟩, hγN _⟩).property
    rw [hJF] at h
    exact h
  obtain ⟨R, B, L, n, P, hR, hRK, hBR, hBs, hBfull, hLR, hLs, hLfull, hP, hPi, hPL⟩ :=
    K.exists_refinement_with_embedded_rim A hK hAK
      (F ∘ st.annulusRimMap false) hγPL hγinj hγK
  let JR : N ≃ₜ R.space := J.trans (Homeomorph.setCongr hRK.space_eq.symm)
  have hJR (x : N) : (JR x : E) = F x := hJF x
  have hgR (z : R.space) : (g z : st.Carrier) = (JR.symm z : st.Carrier) :=
    hg ⟨z, hRK.space_eq.subset z.property⟩
  refine ⟨R, B, hR, JR, hRK, hBR, hBs, hBfull, hJR, hgR, ?_, ?_⟩
  · intro p hp
    obtain ⟨v, hv, hsub, hAff⟩ := hRK.exists_original_affine_vertex_star (F := V3) hK hp
    obtain ⟨T, hT, hTPL, hTcompat, hTregion⟩ := hstars v hv
    exact ⟨T, hT.mono_left hsub, hAff _ hTPL, hTcompat, hTregion⟩
  · let : Fintype R.vertices := (R.finite_vertices_of_finite_faces hR).fintype
    let : Fintype L.vertices := (L.finite_vertices_of_finite_faces (hR.subset hLR)).fintype
    have hend (x : st.Carrier) : st.endpoint x ∈ st.sourceMap '' S.space :=
      st.endpoint_range.subset (mem_range_self x)
    apply R.finrank_closed_le_coboundaries_add_one_of_marked_polygon L (hR.subset hLR)
      hLR P hP hPi hPL hDN st.deformation hend H ha JR γ hγD ?_ hterminal
    intro u
    rw [hJR, hLs]
    exact ⟨u, u.property, rfl⟩

end Geometry.OriginalPLTower
