import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.UnionDisk.Halves
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.ArcExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.Seam

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryUnionDisk

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_half_charts
    {X ι E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (D U W : Bool → Set E) (a b : Bool → E) (f : Bool → E → X)
    (hD : ∀ i, IsFinitePLBallPair P2 (D i) (U i ∪ W i))
    (hU : ∀ i, IsFinitePLBallPair ℝ (U i) {a i, b i})
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {a i, b i})
    (hUW : ∀ i, U i ∩ W i = {a i, b i}) (hab : ∀ i, a i ≠ b i)
    (hf : ∀ i, PolyhedralPLInCharts e (f i) (D i)) (hfi : ∀ i, InjOn (f i) (D i))
    (himage : f false '' W false = f true '' W true)
    (ha : f false (a false) = f true (a true))
    (hb : f false (b false) = f true (b true)) :
    ∃ C : ∀ i, half i ≃ₜ D i, (∀ i, (C i).IsFinitePL) ∧
      (∀ x : seam,
        f false (C false ⟨x, (half_ball false).1 (seam_subset_frontier false x.property)⟩) =
        f true (C true ⟨x, (half_ball true).1 (seam_subset_frontier true x.property)⟩)) ∧
      (∀ i (x : half i), (C i x : E) ∈ U i ↔ (x : P2) ∈ frontier whole) ∧
      ∀ i (x : half i), (C i x : E) ∈ W i ↔ (x : P2) ∈ seam := by
  have hWD (i : Bool) : W i ⊆ D i := subset_union_right.trans (hD i).1
  have hfW (i : Bool) : PolyhedralPLInCharts e (f i) (W i) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJW, _⟩, _⟩, _⟩ := hW i
    exact hJW ▸ (hf i).restrict_finite J hJ (hJW.subset.trans (hWD i))
  obtain ⟨r, hr, hrv⟩ := exists_original_interval_identification he (hW false) (hW true)
    (hfW false) (hfW true) ((hfi false).mono (hWD false))
    ((hfi true).mono (hWD true)) himage
  obtain ⟨w₀, hw₀, hw₀a, hw₀b⟩ := (hW false).exists_unitInterval_chart_with_endpoints (hab false)
  let w : ∀ i, unitInterval ≃ₜ W i := Bool.rec w₀ (w₀.trans r)
  have hw (i : Bool) : (w i).IsFinitePL := by
    cases i
    · exact hw₀
    · exact hw₀.trans hr
  have hwa (i : Bool) : (w i 0 : E) = a i := by
    cases i
    · exact hw₀a
    · apply hfi true (hWD true (w true 0).property) (hWD true ((hW true).1 (by simp)))
      exact (hrv (w₀ 0)).symm.trans ((congrArg (f false) hw₀a).trans ha)
  have hwb (i : Bool) : (w i 1 : E) = b i := by
    cases i
    · exact hw₀b
    · apply hfi true (hWD true (w true 1).property) (hWD true ((hW true).1 (by simp)))
      exact (hrv (w₀ 1)).symm.trans ((congrArg (f false) hw₀b).trans hb)
  obtain ⟨v, hv, hv0, hv1⟩ := seam_ball.exists_unitInterval_chart_with_endpoints
    (show ((0, 1) : P2) ≠ (0, 0) by norm_num)
  obtain ⟨V, hV⟩ := exists_half_outer_intervals
  let q (i : Bool) : seam ≃ₜ W i := v.symm.trans (w i)
  have hq (i : Bool) : (q i).IsFinitePL := hv.symm.trans (hw i)
  have hq0 (i : Bool) : (q i ⟨(0, 1), seam_ball.1 (by simp)⟩ : E) = a i := by
    have h0 : (⟨(0, 1), seam_ball.1 (by simp)⟩ : seam) = v 0 := Subtype.ext hv0.symm
    simp only [h0, q, Homeomorph.trans_apply, v.symm_apply_apply, hwa]
  have hq1 (i : Bool) : (q i ⟨(0, 0), seam_ball.1 (by simp)⟩ : E) = b i := by
    have h1 : (⟨(0, 0), seam_ball.1 (by simp)⟩ : seam) = v 1 := Subtype.ext hv1.symm
    simp only [h1, q, Homeomorph.trans_apply, v.symm_apply_apply, hwb]
  have hex (i : Bool) := exists_disk_homeomorph_prescribed_arc
    ((hV i).2.1.symm ▸ half_ball i) (hD i) (hV i).1 seam_ball (hU i)
    (hV i).2.2.1 (hUW i) (q i) (hq i) (hq0 i) (hq1 i)
  choose C hC hCseam hCU hCW using hex
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · intro x
    rw [hCseam false x, hCseam true x]
    exact hrv (w₀ (v.symm x))
  · intro i x
    exact (hCU i x).symm.trans ((hV i).2.2.2 x x.property).symm
  · exact fun i x ↦ (hCW i x).symm

end PoincareConjecture.M76.Dehn.Annuli.BoundaryUnionDisk
