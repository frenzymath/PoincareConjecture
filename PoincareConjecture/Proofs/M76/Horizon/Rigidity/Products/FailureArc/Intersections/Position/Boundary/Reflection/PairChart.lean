import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Reflection.OpenChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Frontier

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private def collarPairCoordinates : C3 ≃L[ℝ] C3 where
  toFun z := ((z.1.1, z.2), z.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem exists_original_boundary_pair_chart_of_halfbox
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S T R : Set X} {y : X}
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (L : V3 ≃ᴬ[ℝ] C3) (hL0 : L 0 = 0) (hy : y ∈ B.source) (hzero : B y = 0)
    (hSR : S ⊆ R) (hTR : T ⊆ R)
    (hR : ∀ z ∈ B.target, B.symm z ∈ R ↔ 0 ≤ (L z).2)
    {A : Set P2} {r : ℝ} (hr : 0 < r) (hA : (0 : P2) ∈ interior A)
    (f : C3 → C3) (hf : FinitePiecewiseAffineOn f (A ×ˢ Icc (0 : ℝ) r))
    (hfi : InjOn f (A ×ˢ Icc (0 : ℝ) r)) (hf0 : f 0 = 0)
    (hfpos : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, 0 ≤ (f z).2)
    (hfzero : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, (f z).2 = 0 ↔ z.2 = 0)
    (hfS : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, B.symm (L.symm (f z)) ∈ S ↔ z.1.2 = 0)
    (hfT : ∀ z ∈ A ×ˢ Icc (0 : ℝ) r, B.symm (L.symm (f z)) ∈ T ↔ z.1.1 = 0) :
    ∃ C : OriginalSurfacePairChart e S T y true,
      (∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
      ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0 := by
  obtain ⟨D, hDs, hD0, hDz, _, hDi, _, hDhalf, hDpos⟩ :=
    exists_doubled_halfspace_open_chart hr hA hf hfi hf0 hfpos hfzero
  let Q := (L.toHomeomorph.toOpenPartialHomeomorph.trans D.symm).trans
    collarPairCoordinates.toHomeomorph.toOpenPartialHomeomorph
  let H := Q.restrOpen B.target B.open_target
  have hHt (z : V3) (hz : z ∈ H.source) : L z ∈ D.target := hz.1.1.2
  have hHw (z : V3) (hz : z ∈ H.source) : D.symm (L z) ∈ D.source := D.map_target (hHt z hz)
  have hvalue (z : V3) : H z =
      (((D.symm (L z)).1.1, (D.symm (L z)).2), (D.symm (L z)).1.2) := rfl
  have hhalf (z : V3) (hz : z ∈ H.source) : B.symm z ∈ R ↔ 0 ≤ (H z).1.2 := by
    have hh := hDhalf (D.symm (L z)) (hHw z hz)
    rw [D.right_inv (hHt z hz)] at hh
    exact (hR z hz.2).trans hh
  have hparam (z : V3) (hz : z ∈ H.source) (hn : 0 ≤ (H z).1.2) :
      D.symm (L z) ∈ A ×ˢ Icc (0 : ℝ) r ∧ f (D.symm (L z)) = L z := by
    have hm := interior_subset (hDs.subset (hHw z hz))
    refine ⟨⟨hm.1, hn, hm.2.2⟩, ?_⟩
    exact (hDpos _ (hHw z hz) hn).symm.trans (D.right_inv (hHt z hz))
  have hS (z : V3) (hz : z ∈ H.source) :
      B.symm z ∈ S ↔ (H z).2 = 0 ∧ 0 ≤ (H z).1.2 := by
    constructor
    · intro hs
      have hn := (hhalf z hz).mp (hSR hs)
      obtain ⟨hm, hfv⟩ := hparam z hz hn
      have hs' := hfS _ hm
      rw [hfv, L.symm_apply_apply] at hs'
      exact ⟨hs'.mp hs, hn⟩
    · rintro ⟨hs, hn⟩
      obtain ⟨hm, hfv⟩ := hparam z hz hn
      have hs' := (hfS _ hm).mpr hs
      simpa only [hfv, L.symm_apply_apply] using hs'
  have hT (z : V3) (hz : z ∈ H.source) :
      B.symm z ∈ T ↔ (H z).1.1 = 0 ∧ 0 ≤ (H z).1.2 := by
    constructor
    · intro ht
      have hn := (hhalf z hz).mp (hTR ht)
      obtain ⟨hm, hfv⟩ := hparam z hz hn
      have ht' := hfT _ hm
      rw [hfv, L.symm_apply_apply] at ht'
      exact ⟨ht'.mp ht, hn⟩
    · rintro ⟨ht, hn⟩
      obtain ⟨hm, hfv⟩ := hparam z hz hn
      have ht' := (hfT _ hm).mpr ht
      simpa only [hfv, L.symm_apply_apply] using ht'
  have hHPL : LocallyPiecewiseAffineOn H H.source := by
    have h0 := hDi.comp (locallyPiecewiseAffineOn_affine L.toContinuousAffineMap isOpen_univ)
    have h1 := (locallyPiecewiseAffineOn_affine
      collarPairCoordinates.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp h0
    exact h1.mono H.open_source (fun _ hz => hz.1)
  have hcenter : B y ∈ H.source := by
    refine ⟨⟨⟨mem_univ _, ?_⟩, mem_univ _⟩, B.map_source hy⟩
    change L (B y) ∈ D.target
    rw [hzero, hL0, ← hDz]
    exact D.map_source hD0
  have hcenter0 : H (B y) = 0 := by
    have hi0 : D.symm 0 = 0 := (congrArg D.symm hDz.symm).trans (D.left_inv hD0)
    rw [hvalue, hzero, hL0, hi0]
    rfl
  let C : OriginalSurfacePairChart e S T y true := {
    chart := B
    coordinates := H
    compatible := hB
    center_source := hy
    center_coordinates := hcenter
    center_zero := hcenter0
    source_subset := fun _ hz => hz.2
    forwardPL := hHPL
    inversePL := H.locallyPiecewiseAffineOn_symm hHPL
    first_surface := by simpa only [true_implies] using hS
    second_surface := by simpa only [true_implies] using hT }
  exact ⟨C, hhalf, C.frontier_iff_of_region_halfspace hhalf⟩

end PoincareConjecture.M76
