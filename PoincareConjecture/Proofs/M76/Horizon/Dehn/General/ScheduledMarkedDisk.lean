import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTowerDescent
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.DisjointSupportedMotions
import PoincareConjecture.Proofs.M76.Dehn.OriginalStageDiskMotion

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {M ι α : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}
  {st : Stage e S f r C} {R Fmark : Set M}
  {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}

theorem StageMarkedDisk.exists_finite_moved_marked_disk
    (old : StageMarkedDisk st R Fmark base Jgroup)
    (F : α → I → st.Carrier ≃ₜ st.Carrier)
    (hF : ∀ a, Continuous (fun z : I × st.Carrier ↦ F a z.1 z.2))
    (hzero : ∀ a x, F a 0 x = x)
    (hPL : ∀ a i j, (st.charts i).symm.trans
      ((F a 1).toOpenPartialHomeomorph.trans (st.charts j)) ∈ piecewiseAffineGroupoid V3)
    (hregion : ∀ a u, (F a u) ⁻¹' (st.projection ⁻¹' R) = st.projection ⁻¹' R)
    (hmark : ∀ a u, (F a u) ⁻¹' (st.projection ⁻¹' Fmark) = st.projection ⁻¹' Fmark)
    (l : List α) :
    ∃ (new : StageMarkedDisk st R Fmark base Jgroup) (eta : old.rim.Homotopy new.rim),
      new.map = composeSupportedMotions F l 1 ∘ old.map ∧
      (∀ u x, (eta (u, x) : M) =
        st.projection (composeSupportedMotions F l u (old.map x))) ∧
      new.basepath = old.basepath.trans (eta.evalAt squareRimBase) := by
  let H := composeSupportedMotions F l
  have hH : Continuous (fun z : I × st.Carrier ↦ H z.1 z.2) :=
    composeSupportedMotions_continuous F hF l
  have hH0 : ∀ x, H 0 x = x := composeSupportedMotions_initial F 0 hzero l
  have hpre (A : Set st.Carrier) (hA : ∀ a u, (F a u) ⁻¹' A = A)
      (u : I) : (H u) ⁻¹' A = A := by
    change (composeSupportedMotions F l u) ⁻¹' A = A
    clear hH hH0 H
    induction l with
    | nil => rfl
    | cons a l ih =>
      change (composeSupportedMotions F l u) ⁻¹' ((F a u) ⁻¹' A) = A
      rw [hA a u, ih]
  obtain ⟨_, _, _, _, _, _, hmodel, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨K, hK, hKD, _⟩, _⟩ := hmodel
  have hnewPL : PolyhedralPLInCharts st.charts (H 1 ∘ old.map) D2 := by
    have holdPL : PolyhedralPLInCharts st.charts old.map K.space := hKD.symm ▸ old.piecewiseAffine
    rw [← hKD]
    change PolyhedralPLInCharts st.charts
      (composeSupportedMotions F l 1 ∘ old.map) K.space
    clear hH hH0 hpre H
    induction l with
    | nil => exact holdPL
    | cons a l ih =>
      exact ih.comp_chart_homeomorph K hK (F a 1) st.cover (hPL a)
  have hQcont : Continuous (fun x : Q2 ↦ old.map x) :=
    old.piecewiseAffine.continuousOn.comp_continuous continuous_subtype_val
      (fun x ↦ sphere_subset_closedBall x.property)
  have hmarked (u : I) (x : Q2) : st.projection (H u (old.map x)) ∈ Fmark := by
    change old.map x ∈ (H u) ⁻¹' (st.projection ⁻¹' Fmark)
    rw [hpre _ hmark u]
    change st.projection (old.map x) ∈ Fmark
    rw [old.boundary_values x]
    exact (old.rim x).property
  let rim : C(Q2, Fmark) :=
    ⟨fun x ↦ ⟨st.projection (H 1 (old.map x)), hmarked 1 x⟩,
      (st.projection.continuous.comp ((H 1).continuous.comp hQcont)).subtype_mk _⟩
  let eta : old.rim.Homotopy rim := {
    toFun := fun z ↦ ⟨st.projection (H z.1 (old.map z.2)), hmarked z.1 z.2⟩
    continuous_toFun := (st.projection.continuous.comp
      (hH.comp (continuous_fst.prodMk (hQcont.comp continuous_snd)))).subtype_mk _
    map_zero_left := by
      intro x
      apply Subtype.ext
      change st.projection (H 0 (old.map x)) = (old.rim x : M)
      rw [hH0, old.boundary_values x]
    map_one_left := fun _ ↦ rfl }
  let new : StageMarkedDisk st R Fmark base Jgroup := {
    map := H 1 ∘ old.map
    rim := rim
    piecewiseAffine := hnewPL
    embedding := (H 1).isEmbedding.comp old.embedding
    inside := by
      intro x hx
      change old.map x ∈ (H 1) ⁻¹' (st.projection ⁻¹' R)
      rw [hpre _ hregion 1]
      exact old.inside hx
    boundary_values := fun _ ↦ rfl
    whole_boundary_iff := by
      intro x
      have hfront : (H 1) ⁻¹' frontier (st.projection ⁻¹' R) =
          frontier (st.projection ⁻¹' R) := by
        rw [(H 1).preimage_frontier, hpre _ hregion 1]
      exact (Set.ext_iff.mp hfront (old.map x)).trans (old.whole_boundary_iff x)
    basepath := old.basepath.trans (eta.evalAt squareRimBase)
    outside := by
      rw [← eta.whiskeredLoopClass_eq old.basepath squareRimLoop]
      exact old.outside }
  exact ⟨new, eta, rfl, fun _ _ ↦ rfl, rfl⟩

end Geometry.OriginalPLTower
