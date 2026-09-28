import PoincareConjecture.Proofs.M76.Dehn.OriginalTerminalPair
import PoincareConjecture.Proofs.M76.Dehn.FullMarkedTerminalStars
import PoincareConjecture.Proofs.M76.Dehn.OriginalRimFrontier

set_option autoImplicit false

universe u w z

open Set Topology Geometry unitInterval
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U : Type u} {M : Type w} {ι : Type z}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]

theorem exists_original_terminal_chart_stars
    (e : ι → OpenPartialHomeomorph M V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (S : SimplicialComplex ℝ U) (hS : S.faces.Finite)
    [SimplyConnectedSpace S.space] [LocallyPathConnectedSpace S.space]
    {f : U → M} (hf : PolyhedralPLInCharts e f S.space) (v0 : S.space)
    {R : Set M} (hfR : MapsTo f S.space R) (hR : IsClosed R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph M V3),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (r : M → ℝ) (C : Set M) (s0 st : Stage e S f r C),
      IsOpenEmbedding s0.projection ∧ Reaches s0 st ∧
      (∀ (Y : Type w) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
        (p : Y → st.Carrier), IsCoveringMap p →
          (∀ x, (p ⁻¹' {x}).ncard = 2) → False) ∧
      ∃ (z : st.Carrier → ℝ) (c : ℝ) (N : Set st.Carrier),
        c ∈ Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) ∧ Continuous z ∧
        N = {x | st.projection x ∈ R ∧ c ≤ z x} ∧
        IsCompact N ∧ IsCompact {x | c ≤ z x} ∧
        st.sourceMap '' S.space ⊆ interior {x | c ≤ z x} ∧
        st.sourceMap '' S.space ⊆ N ∧
        (∀ x ∈ frontier N,
          ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph st.Carrier V3),
            ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
            (∀ k, (st.charts k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
            ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) ∧
        (∀ x ∈ frontier (st.projection ⁻¹' R), z x = c →
          ∃ (ell eta : V3 →ᴬ[ℝ] ℝ) (u v : V3)
            (B : OpenPartialHomeomorph st.Carrier V3),
            ell.contLinear u = 1 ∧ ell.contLinear v = 0 ∧ eta.contLinear v = 1 ∧
            x ∈ B.source ∧ ell (B x) = 0 ∧ eta (B x) = 0 ∧
            (∀ k, (st.charts k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
            (∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) ∧
            (∀ y ∈ B.source,
              (y ∈ frontier (st.projection ⁻¹' R) ∧ c ≤ z y) ↔
                (ell (B y) = 0 ∧ 0 ≤ eta (B y))) ∧
            ∀ y ∈ B.source,
              (z y = c ∧ st.projection y ∈ R) ↔ (ell (B y) = 0 ∧ eta (B y) ≤ 0)) ∧
        (∀ u ∈ S.space, f u ∈ frontier R → st.sourceMap u ∈ frontier N) ∧
        ∃ (a : C(N, N))
          (H : (ContinuousMap.id N).HomotopyRel a
            (Subtype.val ⁻¹' (st.sourceMap '' S.space))),
          range a = Subtype.val ⁻¹' (st.sourceMap '' S.space) ∧
          (∀ (tau : I) (x : N), (x : st.Carrier) ∈ frontier (st.projection ⁻¹' R) →
            (H (tau, x) : st.Carrier) ∈ frontier (st.projection ⁻¹' R)) ∧
          ∃ (p : Finset N) (F : st.Carrier → (p → ℝ × V3))
            (K : SimplicialComplex ℝ (p → ℝ × V3))
            (A : Fin 2 → SimplicialComplex ℝ (p → ℝ × V3))
            (J : N ≃ₜ K.space) (g : (p → ℝ × V3) → N),
            Continuous F ∧
            (∀ k, LocallyPiecewiseAffineOn (F ∘ (st.charts k).symm) (st.charts k).target) ∧
            K.faces.Finite ∧
            (∀ a, A a ≤ K ∧ (A a).faces.Finite ∧
              ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A a).vertices) → t ∈ (A a).faces) ∧
            K.space = F '' N ∧ (A 0).space = F '' frontier N ∧
            (A 1).space = F '' (st.sourceMap '' S.space) ∧
            (∀ x : N, (J x : (p → ℝ × V3)) = F x) ∧
            (∀ x : N, (J x : (p → ℝ × V3)) ∈ (A 0).space ↔
              (x : st.Carrier) ∈ frontier N) ∧
            (∀ x : N, (J x : (p → ℝ × V3)) ∈ (A 1).space ↔
              (x : st.Carrier) ∈ st.sourceMap '' S.space) ∧
            (∀ x ∈ N, ∃ (k : st.Index) (V : Set st.Carrier)
              (b : (p → ℝ × V3) →ᴬ[ℝ] V3),
              IsOpen V ∧ x ∈ V ∧ V ⊆ (st.charts k).source ∧
                EqOn (b ∘ F) (st.charts k) V) ∧
            ContinuousOn g K.space ∧
            (∀ z : K.space, (g z : st.Carrier) = (J.symm z : st.Carrier)) ∧
            PolyhedralPLInCharts st.charts (fun z => (g z : st.Carrier)) K.space ∧
            (∀ v ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
              MapsTo (fun z => (g z : st.Carrier)) (K.closedStar v).space B.source ∧
              (∀ k, (st.charts k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
              (K.closedStar v).AffineOnFaces (fun z => B (g z)) ∧
              (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
                ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y))) ∧
            (∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4) ∧
            ∀ [Fintype K.vertices],
              let B := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
              LinearMap.ker (edgeCoboundary B) = LinearMap.range (vertexCoboundary B) ∧
                LinearMap.range (edgeCoboundary B).dualMap =
                  LinearMap.ker (vertexCoboundary B).dualMap := by
  classical
  obtain ⟨r, C, s0, st, hs0, hreach, hterm, z, c, N, hc, hz, hNeq,
    hN, hP, hDP, hDN, hfront, hcorner, a, H, ha, hHfront,
    p, F, K0, L0, J0, hFc, hFPL, hK0, hL0K, _, hK0s, hL0s,
    hJF, _, hproj, _⟩ :=
    exists_original_terminal_pair e hcompat hcover S hS hf v0 hfR hR hboundary
  have heN : PoincareConjecture.M76.PLDomain st.charts N :=
    ⟨st.cover, st.compatible, hN.isClosed, hfront⟩
  obtain ⟨K, A, J, g, hK, _, hA, hKs, hA0s, hA1s, hJF', hgc, hgval, hgPL,
    hstars, hpure⟩ :=
    exists_full_marked_pair_chart_stars heN S hS st.sourcePL v0
      (image_subset_iff.mp hDN) F hFPL K0 L0 hK0 hL0K hK0s hL0s J0 hJF hproj
  have hFinj : InjOn F N := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (J.injective
      (Subtype.ext ((hJF' ⟨x, hx⟩).trans (hxy.trans (hJF' ⟨y, hy⟩).symm))))
  have hmarked (D : Set st.Carrier) (hD : D ⊆ N) (x : N) :
      (J x : (p → ℝ × V3)) ∈ F '' D ↔ (x : st.Carrier) ∈ D := by
    rw [hJF']
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact hFinj (hD hy) x.property hyx ▸ hy
    · exact mem_image_of_mem F
  have hNR : N ⊆ st.projection ⁻¹' R := by
    rw [hNeq]
    exact fun _ hx => hx.1
  refine ⟨r, C, s0, st, hs0, hreach, hterm, z, c, N, hc, hz, hNeq,
    hN, hP, hDP, hDN, hfront, hcorner,
    fun u hu hfu => st.source_mem_frontier_of_original_rim hN.isClosed hDN hNR hu hfu,
    a, H, ha, hHfront, p, F, K, A, J, g, hFc, hFPL, hK, hA,
    hKs, hA0s, hA1s, hJF', ?_, ?_, hproj, hgc, hgval, hgPL, hstars, hpure, ?_⟩
  · intro x
    rw [hA0s]
    exact hmarked _ hN.isClosed.frontier_subset x
  · intro x
    rw [hA1s]
    exact hmarked _ hDN x
  · intro instK
    have hend (x : st.Carrier) : st.endpoint x ∈ st.sourceMap '' S.space := by
      rw [← st.endpoint_range]
      exact mem_range_self x
    have haend (x : N) : (a x : st.Carrier) ∈ st.sourceMap '' S.space :=
      ha.subset (mem_range_self x)
    let B := K.finiteBarycentricHomeomorph.trans J.symm
    exact ⟨ker_edgeCoboundary_eq_range_vertexCoboundary
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex
      K.vertexAbstractComplex.singleton_mem hDN st.deformation hend H haend B hterm,
      range_boundary2_eq_ker_boundary1 K.vertexAbstractComplex.toPreAbstractSimplicialComplex
        K.vertexAbstractComplex.singleton_mem hDN st.deformation hend H haend B hterm⟩

end Geometry.OriginalPLTower
