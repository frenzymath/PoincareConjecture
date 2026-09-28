import PoincareConjecture.Proofs.M76.Dehn.OriginalStageProperDisk
import PoincareConjecture.Proofs.M76.Dehn.OriginalTerminalChartStars
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex












set_option autoImplicit false

open Set Metric Geometry
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1






theorem exists_original_terminal_proper_disk
    {M ι : Type*} [TopologicalSpace M] [T2Space M]
    {e : ι → OpenPartialHomeomorph M V3} {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hFmark : Fmark ⊆ frontier R)
    {f : V2 → M} (hf : PolyhedralPLInCharts e f D) (hfR : MapsTo f D R)
    (gamma : C(Q, Fmark)) (hpair : ∀ x : Q, f x.val = (gamma x : M))
    {base : Fmark} (p : Path base (gamma squareRimBase))
    (J : Subgroup (FundamentalGroup Fmark base))
    (houtside : p.whiskeredLoopClass (squareRimLoop.map gamma.continuous) ∉ J) :
    ∃ (S : SimplicialComplex ℝ V2) (r : M → ℝ) (C : Set M)
      (s0 st : Stage e S f r C), S.space = D ∧
      Topology.IsOpenEmbedding s0.projection ∧ Reaches s0 st ∧
      ∃ (j : V2 → st.Carrier) (rim : C(Q, Fmark)) (q : Path base (rim squareRimBase)),
        PolyhedralPLInCharts st.charts j D ∧
        Topology.IsEmbedding (fun x : D => j x) ∧ MapsTo j D (st.projection ⁻¹' R) ∧
        (∀ x : Q, st.projection (j x) = (rim x : M)) ∧
        (∀ x : D, j x ∈ frontier (st.projection ⁻¹' R) ↔ (x : V2) ∈ Q) ∧
        q.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J := by
  classical
  let := ChartedSpace.ofChartCover e he.cover
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace V3 M
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨S, hS, hSD, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  have hcv : Convex ℝ S.space := hSD.symm ▸ convex_closedBall (0 : V2) 1
  let v0 : S.space := ⟨0, hSD.symm.subset (mem_closedBall_self zero_le_one)⟩
  let : ContractibleSpace S.space := hcv.contractibleSpace ⟨v0, v0.property⟩
  let : LocallyPathConnectedSpace S.space := hcv.locallyPathConnectedSpace
  obtain ⟨r, C, s0, st, hs0, hreach, hterminal, z, c, N, _, _, hNeq, hN, _, _, hDN,
    hfront, _, _, a, H, ha, _, s, F, K, A, Jmodel, g, _, hFPL, hK, hA,
    _, hAs, _, hJF, _, _, _, _, hg, hgPL, hstars, _, _⟩ :=
    exists_original_terminal_chart_stars e he.compatible he.cover S hS
      (hSD.symm ▸ hf) v0 (hSD.symm ▸ hfR) he.closed he.halfspace
  have heN : PoincareConjecture.M76.PLDomain st.charts N :=
    ⟨st.cover, st.compatible, hN.isClosed, hfront⟩
  have hNR : N ⊆ st.projection ⁻¹' R := by
    rw [hNeq]
    exact fun _ hx => hx.1
  have hstars' : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z => (g z : st.Carrier)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) := by
    intro p hp
    obtain ⟨B, hmap, _, hPL, hcase⟩ := hstars p hp
    exact ⟨B, hmap, hPL, hcase⟩
  obtain ⟨j, rim, q, hj, hji, hjR, hrim, hproper, hout⟩ :=
    st.exists_marked_terminal_proper_disk hSD hN heN hDN hNR Fmark hFmark gamma hpair
      a H ha F hFPL K (A 0) hK (hA 0).1 (hA 0).2.2 Jmodel g hJF hg hgPL hAs
      hstars' hterminal p J houtside
  exact ⟨S, r, C, s0, st, hSD, hs0, hreach, j, rim, q, hj, hji, hjR, hrim,
    hproper, hout⟩

end Geometry.OriginalPLTower
