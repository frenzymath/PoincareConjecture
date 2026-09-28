import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.OpenPartialHomeomorph.Basic












set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]


noncomputable def chartPushforward (e : OpenPartialHomeomorph E F) (V : E → E) (y : F) : F :=
  fderiv ℝ e (e.symm y) (V (e.symm y))


theorem chartPushforward_contDiffOn (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (V : E → E) (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (chartPushforward e V) e.target := by
  have hVc : ContDiffOn ℝ ∞ (fun y => V (e.symm y)) e.target :=
    (hV.contDiffOn : ContDiffOn ℝ ∞ V e.source).comp hi (fun _ hy => e.map_target hy)
  exact ((he.fderiv_of_isOpen e.open_source (by simp)).comp hi
    (fun _ hy => e.map_target hy)).clm_apply hVc



theorem exists_chart_field_extension [FiniteDimensional ℝ F]
    (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (V : E → E) (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVs : tsupport V ⊆ e.source) :
    ∃ W : F → F, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      tsupport W ⊆ e '' tsupport V ∧
      ∀ x ∈ e.source, W (e x) = fderiv ℝ e x (V x) := by
  have hC : IsCompact (e '' tsupport V) :=
    hVc.isCompact.image_of_continuousOn (e.continuousOn.mono hVs)
  have hCt : e '' tsupport V ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hVs hx)
  obtain ⟨ρ, hρ, hρc, hρs, hnear, _⟩ := exists_compact_smooth_cutoff hC e.open_target hCt
  let W : F → F := fun y => ρ y • chartPushforward e V y
  have hWs : Function.support W ⊆ e '' tsupport V := by
    intro y hy
    have hρy : ρ y ≠ 0 := by
      intro hzero
      exact hy (by simp only [W, hzero, zero_smul])
    have hyt : y ∈ e.target := hρs (subset_tsupport ρ hρy)
    have hVy : V (e.symm y) ≠ 0 := by
      intro hzero
      exact hy (by simp only [W, chartPushforward, hzero, map_zero, smul_zero])
    exact ⟨e.symm y, subset_tsupport V hVy, e.right_inv hyt⟩
  refine ⟨W, contDiff_cutoff_smul e.open_target ρ hρ hρs
    (chartPushforward e V) (chartPushforward_contDiffOn e he hi V hV),
    hρc.smul_right, closure_minimal hWs hC.isClosed, ?_⟩
  intro x hx
  by_cases hxV : x ∈ tsupport V
  · have hρx : ρ (e x) = 1 :=
      (eventually_nhdsSet_iff_forall.mp hnear (e x) ⟨x, hxV, rfl⟩).self_of_nhds
    simp only [W, hρx, one_smul, chartPushforward, e.left_inv hx]
  · have hzero := image_eq_zero_of_notMem_tsupport hxV
    simp only [W, chartPushforward, e.left_inv hx, hzero, map_zero, smul_zero]

end PoincareConjecture.M25.Topology3D
