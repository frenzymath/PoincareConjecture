import PoincareConjecture.Proofs.M76.Dehn.OriginalStageBoundaryDisk
import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryDiskPush

set_option autoImplicit false

universe v w z

open Set Metric Geometry
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {G : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [DecidableEq G] [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [DecidableEq G] in

theorem Stage.exists_pushed_marked_disk (st : Stage e S f r C)
    {R : Set M} {N : Set st.Carrier} (hN : IsCompact N)
    (heN : PoincareConjecture.M76.PLDomain st.charts N) (hNR : N ⊆ st.projection ⁻¹' R)
    {Fmark : Set M} (hFmark : Fmark ⊆ frontier R) {j : V2 → st.Carrier}
    (hj : PolyhedralPLInCharts st.charts j D)
    (hjemb : Topology.IsEmbedding (fun x : D => j x))
    (hjB : MapsTo j D (frontier N)) (rim : C(Q, Fmark))
    (hrim : ∀ x : Q, st.projection (j x) = (rim x : M)) :
    ∃ k : V2 → st.Carrier, PolyhedralPLInCharts st.charts k D ∧
      Topology.IsEmbedding (fun x : D => k x) ∧
      MapsTo k D (st.projection ⁻¹' R) ∧ EqOn k j Q ∧
      (∀ x : Q, st.projection (k x) = (rim x : M)) ∧
      ∀ x : D, k x ∈ frontier (st.projection ⁻¹' R) ↔ (x : V2) ∈ Q := by
  obtain ⟨k, hk, hki, hkN, hfix, hproper⟩ :=
    exists_original_boundary_disk_push hN heN hj hjemb hjB
  have hkrim (x : Q) : st.projection (k x) = (rim x : M) := by
    rw [hfix x.property]
    exact hrim x
  refine ⟨k, hk, hki, fun x hx => hNR (hkN hx), hfix, hkrim, ?_⟩
  intro x
  constructor
  · intro hfront
    by_contra hxQ
    have hxN : k x ∈ interior N :=
      (mem_interior_iff_notMem_frontier (hkN x.property)).mpr
        (fun h => hxQ ((hproper x).mp h))
    exact hfront.2 (interior_mono hNR hxN)
  · intro hxQ
    rw [st.frontier_region R]
    change st.projection (k x) ∈ frontier R
    rw [hkrim ⟨x, hxQ⟩]
    exact hFmark (rim ⟨x, hxQ⟩).property

theorem Stage.exists_marked_terminal_proper_disk (st : Stage e S f r C)
    (hSD : S.space = D) {R : Set M} {N : Set st.Carrier} (hN : IsCompact N)
    (heN : PoincareConjecture.M76.PLDomain st.charts N)
    (hDN : st.sourceMap '' S.space ⊆ N) (hNR : N ⊆ st.projection ⁻¹' R)
    (Fmark : Set M) (hFmark : Fmark ⊆ frontier R) (gamma : C(Q, Fmark))
    (hpair : ∀ x : Q, f x.val = (gamma x : M))
    (a : C(N, N))
    (H : (ContinuousMap.id N).HomotopyRel a (Subtype.val ⁻¹' (st.sourceMap '' S.space)))
    (ha : range a = Subtype.val ⁻¹' (st.sourceMap '' S.space))
    (F : st.Carrier → G)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (st.charts i).symm) (st.charts i).target)
    (K A : SimplicialComplex ℝ G) (hK : K.faces.Finite) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    (Jmodel : N ≃ₜ K.space) (g : G → N)
    (hJF : ∀ x : N, (Jmodel x : G) = F x)
    (hg : ∀ z : K.space, (g z : st.Carrier) = (Jmodel.symm z : st.Carrier))
    (hgPL : PolyhedralPLInCharts st.charts (fun z => (g z : st.Carrier)) K.space)
    (hAs : A.space = F '' frontier N)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z => (g z : st.Carrier)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)))
    (hterminal : ∀ (Y : Type (max w v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → st.Carrier),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) → False)
    {base : Fmark} (p : Path base (gamma squareRimBase))
    (J : Subgroup (FundamentalGroup Fmark base))
    (houtside : p.whiskeredLoopClass (squareRimLoop.map gamma.continuous) ∉ J) :
    ∃ (j : V2 → st.Carrier) (rim : C(Q, Fmark)) (q : Path base (rim squareRimBase)),
      PolyhedralPLInCharts st.charts j D ∧
      Topology.IsEmbedding (fun x : D => j x) ∧ MapsTo j D (st.projection ⁻¹' R) ∧
      (∀ x : Q, st.projection (j x) = (rim x : M)) ∧
      (∀ x : D, j x ∈ frontier (st.projection ⁻¹' R) ↔ (x : V2) ∈ Q) ∧
      q.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J := by
  obtain ⟨j, rim, q, hj, hji, hjB, hrim, _, hout⟩ :=
    st.exists_marked_terminal_boundary_disk hSD hN.isClosed hDN hNR
      Fmark hFmark gamma hpair a H ha F hFPL K A hK hAK hfull Jmodel g hJF hg hgPL
      hAs hstars hterminal p J houtside
  obtain ⟨k, hk, hki, hkR, _, hkrim, hkproper⟩ :=
    st.exists_pushed_marked_disk hN heN hNR hFmark hj hji hjB rim hrim
  exact ⟨k, rim, q, hk, hki, hkR, hkrim, hkproper, hout⟩

end Geometry.OriginalPLTower
