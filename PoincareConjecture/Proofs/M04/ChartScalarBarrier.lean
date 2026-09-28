import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas





set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter Metric

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffOn_chart_radial (p : M) (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x ↦ r ^ 2 - ‖extChartAt (𝓡 n) p x - c‖ ^ 2)
      (extChartAt (𝓡 n) p).source := by
  have he : ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (extChartAt (𝓡 n) p) (extChartAt (𝓡 n) p).source := by
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := p) (n := ∞))
  have hφ : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) ↦ r ^ 2 - ‖z - c‖ ^ 2) :=
    contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  exact hφ.contMDiff.comp_contMDiffOn he

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_chart_radial_ne_zero (p : M) (c : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    {x : M} (hx : x ∈ (extChartAt (𝓡 n) p).source)
    (hne : extChartAt (𝓡 n) p x ≠ c) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ r ^ 2 - ‖extChartAt (𝓡 n) p y - c‖ ^ 2) x ≠ 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := extChartAt (𝓡 n) p
  let φ : E → ℝ := fun z ↦ r ^ 2 - ‖z - c‖ ^ 2
  let L : TangentSpace (𝓡 n) x →L[ℝ] E := mfderiv (𝓡 n) 𝓘(ℝ, E) e x
  let z : E := e x - c
  let v := L.inverse z
  have hL : L.IsInvertible := isInvertible_mfderiv_extChartAt hx
  have hv : L v = z := hL.self_apply_inverse z
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  have he : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) e x :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hφ : ContDiff ℝ ∞ φ :=
    contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  have hc : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ φ (e y)) x =
      (fderiv ℝ φ (e x)).comp L := by
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (φ ∘ e) x = _
    rw [mfderiv_comp x ((hφ.differentiable (by simp)) (e x)).mdifferentiableAt he,
      mfderiv_eq_fderiv]
  have hs := ((hasFDerivAt_id (e x)).sub_const c).norm_sq
  have hφd : HasFDerivAt φ (0 - 2 • (innerSL ℝ) z) (e x) := by
    simpa only [φ, z, Pi.sub_apply, id_eq, ContinuousLinearMap.comp_id] using!
      (hasFDerivAt_const (r ^ 2) (e x)).sub hs
  have hvalue : fderiv ℝ φ (e x) z = -2 * ‖z‖ ^ 2 := by
    rw [hφd.fderiv]
    simp only [sub_apply, zero_apply, two_smul, add_apply, innerSL_apply_apply]
    rw [real_inner_self_eq_norm_sq]
    ring
  intro hzero
  have h := congrArg (fun K : TangentSpace (𝓡 n) x →L[ℝ] ℝ ↦ K v) hzero
  change (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ φ (e y)) x) v = 0 at h
  rw [hc] at h
  change fderiv ℝ φ (e x) (L v) = 0 at h
  rw [hv, hvalue] at h
  have hpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  linarith

theorem chart_closedBall_properties [T2Space M]
    (p : M) (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (_hR : 0 < R)
    (hball : closedBall c R ⊆ (extChartAt (𝓡 n) p).target) :
    let e := extChartAt (𝓡 n) p
    let C := e.symm '' closedBall c R
    IsCompact C ∧ C ⊆ e.source ∧
      (∀ x ∈ e.source, x ∈ C ↔ ‖e x - c‖ ≤ R) ∧
      (∀ x ∈ e.source, ‖e x - c‖ < R → x ∈ interior C) := by
  let e := extChartAt (𝓡 n) p
  let C := e.symm '' closedBall c R
  have hC : IsCompact C := (isCompact_closedBall c R).image_of_continuousOn
    ((continuousOn_extChartAt_symm p).mono hball)
  have hCs : C ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hball hz)
  have hmem (x : M) (hx : x ∈ e.source) : x ∈ C ↔ ‖e x - c‖ ≤ R := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [e.right_inv (hball hz)]
      exact mem_closedBall_iff_norm.mp hz
    · intro hnorm
      exact ⟨e x, mem_closedBall_iff_norm.mpr hnorm, e.left_inv hx⟩
  refine ⟨hC, hCs, hmem, ?_⟩
  intro x hx hnorm
  have hO : IsOpen (e.source ∩ e ⁻¹' ball c R) :=
    (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) isOpen_ball
  have hOC : e.source ∩ e ⁻¹' ball c R ⊆ C := by
    intro y hy
    exact (hmem y hy.1).2 (mem_ball_iff_norm.mp hy.2).le
  exact mem_interior.mpr ⟨e.source ∩ e ⁻¹' ball c R, hOC, hO,
    hx, mem_ball_iff_norm.mpr hnorm⟩

end PoincareConjecture.M04

