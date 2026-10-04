import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.OriginalStageRimModel
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Graphs.Mathlib.MarkedSquareImageCycle
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Topology.Mathlib.ConnectedSubsetComponent

/-!
# The marked cycle in one whole original terminal boundary component

The original stage supplies the finite PL rim and its literal map
back to the marked boundary. The entire rim image lies in one whole
component of the unchanged boundary complex. The actual simple cycle
retains the original subgroup and basepoint path. See Stallings p. 11
and Dehn derivation 024.
-/

set_option autoImplicit false

open Set Metric Geometry
open PoincareMT.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {G M ι : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [DecidableEq G] [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- The same original source lift constructs an excluded simple
cycle in one whole boundary component. Every marked value is the
literal original projection of the unchanged inverse model.
See Stallings p. 11 and Dehn024, sections 1--4. -/
theorem Stage.exists_original_marked_cycle (st : Stage e S f r C)
    (hSD : S.space = D) {R : Set M} {N : Set st.Carrier} (hN : IsClosed N)
    (hDN : st.sourceMap '' S.space ⊆ N) (hNR : N ⊆ st.projection ⁻¹' R)
    (Fmark : Set M) (hFmark : Fmark ⊆ frontier R) (gamma : C(Q, Fmark))
    (hpair : ∀ x : Q, f x.val = (gamma x : M))
    (F : st.Carrier → G)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (st.charts i).symm) (st.charts i).target)
    (K A : SimplicialComplex ℝ G) (hK : K.faces.Finite) (hAK : A ≤ K)
    (H : N ≃ₜ K.space) (hHF : ∀ x : N, (H x : G) = F x)
    (hAs : A.space = F '' frontier N) {base : Fmark}
    (p : Path base (gamma squareRimBase))
    (J : Subgroup (FundamentalGroup Fmark base))
    (houtside : p.whiskeredLoopClass (squareRimLoop.map gamma.continuous) ∉ J) :
    ∃ (L : SimplicialComplex ℝ G) (hLA : L.space ⊆ A.space) (mark : C(L.space, Fmark)),
      L.space = ((F ∘ st.sourceMap) ∘ squareRimParameter) '' Icc (0 : ℝ) 1 ∧
      (∀ x : L.space, (mark x : M) = st.projection
        (H.symm ⟨x, SimplicialComplex.space_subset_of_le hAK (hLA x.property)⟩)) ∧
      L.faces.Finite ∧ (∀ s ∈ L.faces, s.card ≤ 2) ∧
      ∃ (B : A.vertexAbstractComplex.edgeGraph.ConnectedComponent),
        L.space ⊆ (A.edgeComponentComplex B).space ∧
        ∃ (v : L.vertices) (c : L.vertexAbstractComplex.edgeGraph.Walk v v)
          (q : Path base (mark ⟨v, L.vertices_subset_space v.property⟩)),
          c.IsCycle ∧ q.whiskeredLoopClass
            ((L.geometricWalkPath c).map mark.continuous) ∉ J := by
  classical
  obtain ⟨hPL, hA, j, hj⟩ := st.exists_original_marked_rim_model
    hSD hN hDN hNR Fmark hFmark gamma hpair F hFPL K A H hHF hAs
  obtain ⟨L, himage, mark, hspace, hmark, hL, hdim, v, c, q, hc, hout⟩ :=
    exists_marked_square_image_cycle hPL gamma j hj p J houtside
  have hLA : L.space ⊆ A.space := himage.trans hA
  have hconnected : IsConnected L.space := by
    rw [hspace]
    exact (isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num)).image _
      (finitePL_squareRim_composition hPL).1.continuousOn
  obtain ⟨B, hB⟩ := A.exists_edgeComponentComplex_of_isConnected
    (hK.subset hAK) hconnected hLA
  refine ⟨L, hLA, mark, hspace, ?_, hL, hdim, B, hB, v, c, q, hc, hout⟩
  intro x
  obtain ⟨y, hy, hyx⟩ := himage x.property
  have hyS : y ∈ S.space := hSD.symm.subset (sphere_subset_closedBall hy)
  have hyN : st.sourceMap y ∈ N := hDN (mem_image_of_mem st.sourceMap hyS)
  have heq : (⟨(x : G), himage x.property⟩ : (F ∘ st.sourceMap) '' Q) =
      ⟨F (st.sourceMap y), mem_image_of_mem (F ∘ st.sourceMap) hy⟩ :=
    Subtype.ext hyx.symm
  have hback : H.symm
      ⟨(x : G), SimplicialComplex.space_subset_of_le hAK (hLA x.property)⟩ =
        ⟨st.sourceMap y, hyN⟩ := by
    apply H.injective
    rw [H.apply_symm_apply]
    apply Subtype.ext
    rw [hHF]
    exact hyx.symm
  rw [hmark x, heq, hj ⟨y, hy⟩, hback]
  exact ((st.source_eq y hyS).trans (hpair ⟨y, hy⟩)).symm

end Geometry.OriginalPLTower
