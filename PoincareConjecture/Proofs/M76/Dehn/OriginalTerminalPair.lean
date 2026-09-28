import PoincareConjecture.Proofs.M76.Dehn.OriginalFinitePLTower
import PoincareConjecture.Proofs.M76.Dehn.OriginalStageNeighborhood
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TerminalModTwoChains












set_option autoImplicit false

universe u v w z

open Set Topology Geometry unitInterval
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.OriginalPLTower

variable {U : Type u} {E : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]





theorem exists_original_terminal_pair
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (S : SimplicialComplex ℝ U) (hS : S.faces.Finite)
    [SimplyConnectedSpace S.space] [LocallyPathConnectedSpace S.space]
    {f : U → M} (hf : PolyhedralPLInCharts e f S.space) (v0 : S.space)
    {R : Set M} (hfR : MapsTo f S.space R) (hR : IsClosed R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (r : M → ℝ) (C : Set M) (s0 st : Stage e S f r C),
      IsOpenEmbedding s0.projection ∧ Reaches s0 st ∧
      (∀ (Y : Type (max w v)) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
        (p : Y → st.Carrier), IsCoveringMap p →
          (∀ x, (p ⁻¹' {x}).ncard = 2) → False) ∧
      ∃ (z : st.Carrier → ℝ) (c : ℝ) (N : Set st.Carrier),
        c ∈ Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) ∧ Continuous z ∧
        N = {x | st.projection x ∈ R ∧ c ≤ z x} ∧
        IsCompact N ∧ IsCompact {x | c ≤ z x} ∧
        st.sourceMap '' S.space ⊆ interior {x | c ≤ z x} ∧
        st.sourceMap '' S.space ⊆ N ∧
        (∀ x ∈ frontier N,
          ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph st.Carrier E),
            ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
            (∀ k, (st.charts k).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
            ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) ∧
        (∀ x ∈ frontier (st.projection ⁻¹' R), z x = c →
          ∃ (ell eta : E →ᴬ[ℝ] ℝ) (u v : E) (B : OpenPartialHomeomorph st.Carrier E),
            ell.contLinear u = 1 ∧ ell.contLinear v = 0 ∧ eta.contLinear v = 1 ∧
            x ∈ B.source ∧ ell (B x) = 0 ∧ eta (B x) = 0 ∧
            (∀ k, (st.charts k).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
            (∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) ∧
            (∀ y ∈ B.source,
              (y ∈ frontier (st.projection ⁻¹' R) ∧ c ≤ z y) ↔
                (ell (B y) = 0 ∧ 0 ≤ eta (B y))) ∧
            ∀ y ∈ B.source,
              (z y = c ∧ st.projection y ∈ R) ↔ (ell (B y) = 0 ∧ eta (B y) ≤ 0)) ∧
        ∃ (a : C(N, N))
          (H : (ContinuousMap.id N).HomotopyRel a
            (Subtype.val ⁻¹' (st.sourceMap '' S.space))),
          range a = Subtype.val ⁻¹' (st.sourceMap '' S.space) ∧
          (∀ (tau : I) (x : N), (x : st.Carrier) ∈ frontier (st.projection ⁻¹' R) →
            (H (tau, x) : st.Carrier) ∈ frontier (st.projection ⁻¹' R)) ∧
          ∃ (p : Finset N) (F : st.Carrier → (p → ℝ × E))
            (K L : SimplicialComplex ℝ (p → ℝ × E)) (J : N ≃ₜ K.space),
            Continuous F ∧
            (∀ k, LocallyPiecewiseAffineOn (F ∘ (st.charts k).symm) (st.charts k).target) ∧
            K.faces.Finite ∧ L ≤ K ∧ L.faces.Finite ∧
            K.space = F '' N ∧ L.space = F '' frontier N ∧
            (∀ x : N, (J x : (p → ℝ × E)) = F x) ∧
            (∀ x : N, (J x : (p → ℝ × E)) ∈ L.space ↔ (x : st.Carrier) ∈ frontier N) ∧
            (∀ x ∈ N, ∃ (k : st.Index) (V : Set st.Carrier) (b : (p → ℝ × E) →ᴬ[ℝ] E),
              IsOpen V ∧ x ∈ V ∧ V ⊆ (st.charts k).source ∧
                EqOn (b ∘ F) (st.charts k) V) ∧
            ∀ [Fintype K.vertices],
              let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
              LinearMap.ker (edgeCoboundary A) = LinearMap.range (vertexCoboundary A) ∧
                LinearMap.range (edgeCoboundary A).dualMap =
                  LinearMap.ker (vertexCoboundary A).dualMap := by
  obtain ⟨r, W, _, q, C, s0, _, _, _, hCW, hr, hrPL, _, _,
    hqinj, hF, hs0, hcut⟩ :=
    exists_original_graph_stage e hcompat hcover S hS hf v0 hfR hboundary
  have hterminalExists : ∃ st : Stage e S f r C, Reaches s0 st ∧
      ∀ (Y : Type (max w v)) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
        (p : Y → st.Carrier), IsCoveringMap p →
          (∀ x, (p ⁻¹' {x}).ncard = 2) → False :=
    exists_terminal_reachable q hqinj hF hS v0 hr hrPL s0
  obtain ⟨st, hreach, hterm⟩ := hterminalExists
  obtain ⟨z, c, hc, hz, _, hP, hN, hAP, hAN, hdeform, hfront, hcorner⟩ :=
    st.exists_compact_relative_neighborhood hS hfR hR hr hrPL
      (fun x hx => (hcut x (hCW hx)).1)
      (fun x hx => (hcut x (hCW hx)).2.1) hboundary
  let N : Set st.Carrier := {x | st.projection x ∈ R ∧ c ≤ z x}
  obtain ⟨a, H, ha, hHfront⟩ := hdeform
  obtain ⟨p, F, K, L, J, hFc, hFPL, hK, hLK, hL, hKs, hLs, hJF, hbound, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair
      st.charts st.compatible st.cover hN hfront
  refine ⟨r, C, s0, st, hs0, hreach, hterm, z, c, N, hc, hz, rfl,
    hN, hP, hAP, hAN, hfront, hcorner, a, H, ha, hHfront,
    p, F, K, L, J, hFc, hFPL, hK, hLK, hL, hKs, hLs, hJF, hbound, hproj, ?_⟩
  intro instK
  have hend (x : st.Carrier) : st.endpoint x ∈ st.sourceMap '' S.space := by
    rw [← st.endpoint_range]
    exact mem_range_self x
  have haend (x : N) : (a x : st.Carrier) ∈ st.sourceMap '' S.space :=
    ha.subset (mem_range_self x)
  let B := K.finiteBarycentricHomeomorph.trans J.symm
  exact ⟨ker_edgeCoboundary_eq_range_vertexCoboundary
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex
    K.vertexAbstractComplex.singleton_mem hAN st.deformation hend H haend B hterm,
    range_boundary2_eq_ker_boundary1 K.vertexAbstractComplex.toPreAbstractSimplicialComplex
      K.vertexAbstractComplex.singleton_mem hAN st.deformation hend H haend B hterm⟩

end Geometry.OriginalPLTower
