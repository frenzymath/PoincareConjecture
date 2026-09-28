import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.FlowNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Flow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow.Splitting

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem round_surface_inner_backward
    (F : RicciFlow 2 M (Iic 0))
    (hround : ∀ s ≤ 0,
      ConstantPositiveSectionalCurvature (F.metric s) (F.connection s))
    {t : ℝ} (ht : t ≤ 0) (p : M) {u : ℝ} (hu : u ≤ 0)
    (x : M) (v w : TangentSpace (𝓡 2) x) :
    (F.metric (t + u / (F.connection t).scalarCurvature p)).inner x v w =
      (1 - u) * (F.metric t).inner x v w := by
  let Q := (F.connection t).scalarCurvature p
  obtain ⟨R, hR, hscalar⟩ :=
    (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp (hround t ht)
  have hQ : 0 < Q := by simpa only [Q, hscalar] using hR
  have htime : MapsTo (fun s : ℝ => t + s / Q) (Iic 0) (Iic 0) := by
    intro s hs
    exact add_nonpos ht (div_nonpos_of_nonpos_of_nonneg hs hQ.le)
  let G := F.parabolicRescale Q hQ t htime F.interval F.nontrivial
  have hGround (s : ℝ) (hs : s ≤ 0) :
      ConstantPositiveSectionalCurvature (G.metric s) (G.connection s) := by
    obtain ⟨r, hr, hrscalar⟩ :=
      (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
        (hround (t + s / Q) (htime hs))
    apply (constantPositiveSectionalCurvature_iff_scalarCurvature _).mpr
    refine ⟨Q⁻¹ * r, mul_pos (inv_pos.mpr hQ) hr, ?_⟩
    intro y
    change (rescaledMetric_connection _ _ Q hQ).scalarCurvature y = _
    rw [rescaledMetric_scalarCurvature, hrscalar]
  have hGzero (y : M) : (G.connection 0).scalarCurvature y = 1 := by
    change (rescaledMetric_connection _ _ Q hQ).scalarCurvature y = 1
    rw [rescaledMetric_scalarCurvature]
    have ht0 : t + 0 / Q = t := by simp
    rw [ht0, hscalar]
    rw [show Q = R from hscalar p]
    exact inv_mul_cancel₀ hR.ne'
  have he := roundAncient_inner_eq_one_sub_time_mul G hGround hGzero u hu x v w
  change Q * (F.metric (t + u / Q)).inner x v w =
    (1 - u) * (Q * (F.metric (t + 0 / Q)).inner x v w) at he
  simp only [zero_div, add_zero] at he
  apply (mul_left_cancel₀ hQ.ne')
  calc
    Q * (F.metric (t + u / Q)).inner x v w =
        (1 - u) * (Q * (F.metric t).inner x v w) := he
    _ = Q * ((1 - u) * (F.metric t).inner x v w) := by ring

theorem normalized_round_surface_inner_relative
    (F : RicciFlow 2 M (Iic 0))
    (hround : ∀ u ≤ 0,
      ConstantPositiveSectionalCurvature (F.metric u) (F.connection u))
    (hzero : ∀ x, (F.connection 0).scalarCurvature x = 1)
    (t s : ℝ) (ht : t ≤ 0) (hs : s ≤ 0)
    (x : M) (v w : TangentSpace (𝓡 2) x) :
    (F.metric s).inner x v w =
      (1 - (s - t) * (F.connection t).scalarCurvature x) *
        (F.metric t).inner x v w := by
  have hslice := roundAncient_inner_eq_one_sub_time_mul F hround hzero s hs x v w
  have htslice := roundAncient_inner_eq_one_sub_time_mul F hround hzero t ht x v w
  have hRt := roundAncient_scalarCurvature_eq_one_div_one_sub_time F hround hzero t ht x
  have hden : 1 - t ≠ 0 := by linarith
  rw [hslice, htslice, hRt]
  field_simp [hden]
  ring

end PoincareConjecture.RicciFlow.Splitting
