import PoincareConjecture.Proofs.M76.Dehn.OriginalPLStage
import PoincareConjecture.Proofs.M76.Dehn.MarkedBoundaryPLLoopDisk
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLChartHomeomorph
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.WhiskeredHomotopyClass
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

theorem Stage.exists_moved_marked_disk (st : Stage e S f r C)
    (G : I → st.Carrier ≃ₜ st.Carrier)
    (hG : Continuous (fun z : I × st.Carrier => G z.1 z.2))
    (hzero : ∀ x, G 0 x = x)
    (hGPL : ∀ i j, (st.charts i).symm.trans
      ((G 1).toOpenPartialHomeomorph.trans (st.charts j)) ∈ piecewiseAffineGroupoid V3)
    {R Fmark : Set M}
    (hR : ∀ t, (G t) ⁻¹' (st.projection ⁻¹' R) = st.projection ⁻¹' R)
    (hF : ∀ t, (G t) ⁻¹' (st.projection ⁻¹' Fmark) = st.projection ⁻¹' Fmark)
    {j : V2 → st.Carrier} (hj : PolyhedralPLInCharts st.charts j D)
    (hji : IsEmbedding (fun x : D => j x))
    (hjR : MapsTo j D (st.projection ⁻¹' R))
    (hproper : ∀ x : D, j x ∈ frontier (st.projection ⁻¹' R) ↔ (x : V2) ∈ Q)
    (rim : C(Q, Fmark)) (hrim : ∀ x : Q, st.projection (j x) = (rim x : M))
    {base : Fmark} (q : Path base (rim squareRimBase))
    (J : Subgroup (FundamentalGroup Fmark base))
    (hout : q.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J) :
    ∃ (rim' : C(Q, Fmark)) (eta : rim.Homotopy rim'),
      PolyhedralPLInCharts st.charts ((G 1) ∘ j) D ∧
      IsEmbedding (fun x : D => G 1 (j x)) ∧
      MapsTo ((G 1) ∘ j) D (st.projection ⁻¹' R) ∧
      (∀ x : D, G 1 (j x) ∈ frontier (st.projection ⁻¹' R) ↔ (x : V2) ∈ Q) ∧
      (∀ x : Q, st.projection (G 1 (j x)) = (rim' x : M)) ∧
      (q.trans (eta.evalAt squareRimBase)).whiskeredLoopClass
        (squareRimLoop.map rim'.continuous) ∉ J := by
  obtain ⟨_, _, _, _, _, _, hmodel, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨K, hK, hKD, _⟩, _⟩ := hmodel
  have hjK : PolyhedralPLInCharts st.charts j K.space := by
    rw [hKD]
    exact hj
  have hPL : PolyhedralPLInCharts st.charts ((G 1) ∘ j) D := by
    rw [← hKD]
    exact hjK.comp_chart_homeomorph K hK (G 1) st.cover hGPL
  have hjQ : Continuous (fun x : Q => j x) :=
    hj.continuousOn.comp_continuous continuous_subtype_val
      (fun x => sphere_subset_closedBall x.property)
  have hmark (t : I) (x : Q) : st.projection (G t (j x)) ∈ Fmark := by
    change j x ∈ (G t) ⁻¹' (st.projection ⁻¹' Fmark)
    rw [hF t]
    change st.projection (j x) ∈ Fmark
    rw [hrim x]
    exact (rim x).property
  let rim' : C(Q, Fmark) :=
    ⟨fun x => ⟨st.projection (G 1 (j x)), hmark 1 x⟩,
      (st.projection.continuous.comp ((G 1).continuous.comp hjQ)).subtype_mk _⟩
  let eta : rim.Homotopy rim' :=
    { toFun := fun z => ⟨st.projection (G z.1 (j z.2)), hmark z.1 z.2⟩
      continuous_toFun := (st.projection.continuous.comp
        (hG.comp (continuous_fst.prodMk (hjQ.comp continuous_snd)))).subtype_mk _
      map_zero_left := by
        intro x
        apply Subtype.ext
        change st.projection (G 0 (j x)) = (rim x : M)
        rw [hzero, hrim x]
      map_one_left := fun _ => rfl }
  refine ⟨rim', eta, hPL, (G 1).isEmbedding.comp hji, ?_, ?_, fun _ => rfl, ?_⟩
  · intro x hx
    change j x ∈ (G 1) ⁻¹' (st.projection ⁻¹' R)
    rw [hR 1]
    exact hjR hx
  · intro x
    have hfront : (G 1) ⁻¹' frontier (st.projection ⁻¹' R) =
        frontier (st.projection ⁻¹' R) := by
      rw [(G 1).preimage_frontier, hR 1]
    have heq := Set.ext_iff.mp hfront (j x)
    exact heq.trans (hproper x)
  · rw [← eta.whiskeredLoopClass_eq q squareRimLoop]
    exact hout

end Geometry.OriginalPLTower
