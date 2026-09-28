import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionMinimizer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.ChartComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.FrozenMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ENNReal NNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_constrained_minimizer_local_chord_bounds
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    {gamma : ℝ → AnnulusCoordinates} {L : ℝ}
    (hc : ContinuousOn gamma (Icc 0 L)) (hconf : MapsTo gamma (Icc 0 L) K)
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma a → tau 1 = gamma b → MapsTo tau (Icc 0 1) K →
        ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation G tau 0 1)
    (H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (h0 : (0 : AnnulusCoordinates) ∈ H.source)
    (hH : ContMDiffOn (𝓡 2) (𝓡 2) ∞ H H.source)
    (hHi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ H.symm H.target)
    {C : Set AnnulusCoordinates} (hC : Convex ℝ C)
    (hregion : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ K ↔ z ∈ C)
    (A : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates)
    (hA : ∀ v, ‖A v‖ = G.tangentNorm (H 0) (mfderiv (𝓡 2) (𝓡 2) H 0 v))
    {u : ℝ} (hu : u ∈ Ioo 0 L) (hpoint : gamma u = H 0)
    {theta : ℝ} (htheta : 1 < theta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ r : ℝ, 0 < r → r < epsilon →
      let x := H.symm (gamma (u - r))
      let y := H.symm (gamma (u + r))
      x ∈ C ∧ y ∈ C ∧ ‖A x‖ ≤ theta * r ∧ ‖A y‖ ≤ theta * r ∧
        2 * r ≤ theta * ‖A (y - x)‖ := by
  have hthetaPos : 0 < theta := zero_lt_one.trans htheta
  let T : ℝ≥0 := ⟨theta, hthetaPos.le⟩
  obtain ⟨U, hU, h0U, hUH, hdist⟩ := G.exists_open_distortion_of_tangentNorm_comparison
    H hH hHi h0 A (show 1 < T from htheta)
    (G.eventually_pullbackNorm_comparison (hH.contMDiffAt (H.open_source.mem_nhds h0))
      A hA (show 1 < T from htheta))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds h0U) hregion)
  have hgc : ContinuousAt gamma u := hc.continuousAt (Icc_mem_nhds hu.1 hu.2)
  have htarget : gamma u ∈ H.target := by rw [hpoint]; exact H.map_source h0
  let q := fun s : ℝ => H.symm (gamma s)
  have hqc : ContinuousAt q u := (H.continuousAt_symm htarget).comp hgc
  have hq0 : q u = 0 := by dsimp only [q]; rw [hpoint, H.left_inv h0]
  have hnear : {s : ℝ | q s ∈ ball 0 R ∧ gamma s ∈ H.target} ∈ 𝓝 u := by
    apply inter_mem
    · change q ⁻¹' (ball (0 : AnnulusCoordinates) R) ∈ 𝓝 u
      apply hqc.preimage_mem_nhds
      rw [hq0]
      exact ball_mem_nhds _ hR
    · exact hgc.preimage_mem_nhds (H.open_target.mem_nhds htarget)
  obtain ⟨eta, heta, hetanear⟩ := Metric.mem_nhds_iff.mp hnear
  let epsilon := min eta (min u (L - u))
  refine ⟨epsilon, lt_min heta (lt_min hu.1 (sub_pos.mpr hu.2)), ?_⟩
  intro r hr hrsmall
  have hre : r < eta := hrsmall.trans_le (min_le_left _ _)
  have hru : r < u := hrsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrL : r < L - u := hrsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hclose (s : ℝ) (hs : |s - u| ≤ r) : q s ∈ ball 0 R ∧ gamma s ∈ H.target :=
    hetanear (by rw [mem_ball, Real.dist_eq]; exact hs.trans_lt hre)
  have hminus : u - r ∈ Icc 0 L := ⟨by linarith, by linarith [hu.2]⟩
  have hplus : u + r ∈ Icc 0 L := ⟨by linarith [hu.1], by linarith⟩
  have hminusAbs : |u - r - u| ≤ r := by rw [sub_right_comm, sub_self, zero_sub, abs_neg,
    abs_of_pos hr]
  have hplusAbs : |u + r - u| ≤ r := by rw [add_sub_cancel_left, abs_of_pos hr]
  let x := q (u - r)
  let y := q (u + r)
  have hx : x ∈ ball 0 R := (hclose _ hminusAbs).1
  have hy : y ∈ ball 0 R := (hclose _ hplusAbs).1
  have hHx : H x = gamma (u - r) := H.right_inv (hclose _ hminusAbs).2
  have hHy : H y = gamma (u + r) := H.right_inv (hclose _ hplusAbs).2
  have hxC : x ∈ C := (hball hx).2.mp (by rw [hHx]; exact hconf hminus)
  have hyC : y ∈ C := (hball hy).2.mp (by rw [hHy]; exact hconf hplus)
  have hnorm (s : ℝ) (hs : s ∈ Icc 0 L) (habs : |s - u| ≤ r) :
      ‖A (q s)‖ ≤ theta * r := by
    have hn := (hdist (q s) (hball (hclose s habs).1).1 0 h0U).2
    rw [map_zero, edist_dist, dist_zero_right, H.right_inv (hclose s habs).2,
      ← hpoint] at hn
    have hh := hn.trans (mul_le_mul_right ((hlip s hs u ⟨hu.1.le, hu.2.le⟩).trans
      (ENNReal.ofReal_le_ofReal habs)) (T : ℝ≥0∞))
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul T.coe_nonneg] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hthetaPos.le hr.le)).mp hh
  let line : ℝ → AnnulusCoordinates := AffineMap.lineMap x y
  have hline (s : ℝ) (hs : s ∈ Icc 0 1) : line s ∈ ball 0 R :=
    (convex_ball (0 : AnnulusCoordinates) R).lineMap_mem hx hy hs
  have hlineC (s : ℝ) (hs : s ∈ Icc 0 1) : line s ∈ C :=
    hC.lineMap_mem hxC hyC hs
  have hsource : MapsTo line (Icc 0 1) H.source := fun s hs => hUH (hball (hline s hs)).1
  have hlineSmooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ line :=
    contMDiff_iff_contDiff.mpr (by dsimp only [line]; fun_prop)
  have hsmooth := hH.comp hlineSmooth.contMDiffOn hsource
  have hlength : m64IntrinsicCurveVariation G (H ∘ line) 0 1 ≤
      ENNReal.ofReal (theta * ‖A (y - x)‖) := by
    apply m64Intrinsic_curveVariation_le_of_edist_le G (mul_nonneg hthetaPos.le (norm_nonneg _))
    intro s hs t ht
    have hh := (hdist (line s) (hball (hline s hs)).1 (line t) (hball (hline t ht)).1).1
    rw [edist_dist, dist_eq_norm, ← map_sub,
      show line s - line t = (s - t) • (y - x) by
        dsimp only [line]
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
        module,
      map_smul, norm_smul, Real.norm_eq_abs, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul T.coe_nonneg] at hh
    have halg : theta * ‖A (y - x)‖ * |s - t| =
        (T : ℝ) * (|s - t| * ‖A (y - x)‖) := by
      change theta * ‖A (y - x)‖ * |s - t| = theta * (|s - t| * ‖A (y - x)‖)
      ring
    rw [halg]
    exact hh
  refine ⟨hxC, hyC, hnorm _ hminus hminusAbs, hnorm _ hplus hplusAbs, ?_⟩
  have hminimum := hmin (u - r) hminus (u + r) hplus (by linarith)
    (H ∘ line) hsmooth.continuousOn (by simpa [line] using hHx)
    (by simpa [line] using hHy) (fun s hs => (hball (hline s hs)).2.mpr (hlineC s hs))
  rw [show (u + r) - (u - r) = 2 * r by ring] at hminimum
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hthetaPos.le (norm_nonneg _))).mp
    (hminimum.trans hlength)

end PoincareConjecture
