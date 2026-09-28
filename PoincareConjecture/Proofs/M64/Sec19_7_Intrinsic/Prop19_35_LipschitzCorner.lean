import PoincareConjecture.Proofs.M64.Mathlib.ClosedConeChord
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LocalChordBounds










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ENNReal NNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_constrained_minimizer_avoids_salient_corner
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
    (C : ConvexCone ℝ AnnulusCoordinates) (hC : IsClosed (C : Set AnnulusCoordinates))
    (hzero : (0 : AnnulusCoordinates) ∈ C) (hsalient : C.Salient)
    (hregion : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ K ↔ z ∈ C)
    {u : ℝ} (hu : u ∈ Ioo 0 L) : gamma u ≠ H 0 := by
  intro hpoint
  have hD : H.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hH.mdifferentiableOn (by simp), hHi.mdifferentiableOn (by simp)⟩
  obtain ⟨A, hA, _⟩ := G.exists_frozenPullbackEquiv (hD.mfderiv h0).injective
  let Q := C.map A.toLinearEquiv.toLinearMap
  have hQ : IsClosed (Q : Set AnnulusCoordinates) :=
    A.toHomeomorph.isClosedMap _ hC
  have hQzero : (0 : AnnulusCoordinates) ∈ Q := ⟨0, hzero, map_zero A⟩
  have hQsalient : Q.Salient := by
    rintro v ⟨x, hx, rfl⟩ hne ⟨y, hy, hyx⟩
    have hy' : y = -x := A.injective (by rw [map_neg]; exact hyx)
    apply hsalient x hx
    · intro hx0
      exact hne (by rw [hx0, map_zero])
    · exact hy' ▸ hy
  obtain ⟨d, hd, hd2, hchord⟩ :=
    m64ClosedCone_exists_scaled_strict_chord_bound Q hQ hQzero hQsalient
  have hthetaNear : ∀ᶠ theta : ℝ in 𝓝[>] 1, theta ^ 2 * d < 2 := by
    have hf : ContinuousAt (fun theta : ℝ => theta ^ 2 * d) 1 := by fun_prop
    exact (hf.eventually (gt_mem_nhds (by simpa using hd2))).filter_mono nhdsWithin_le_nhds
  obtain ⟨theta, htheta2, htheta⟩ := (hthetaNear.and self_mem_nhdsWithin).exists
  have hthetaPos : 0 < theta := zero_lt_one.trans htheta
  obtain ⟨epsilon, hepsilon, hdata⟩ :=
    m64Intrinsic_constrained_minimizer_local_chord_bounds G hc hconf hlip hmin
      H h0 hH hHi C.convex hregion A hA hu hpoint htheta
  let r := epsilon / 2
  have hr : 0 < r := half_pos hepsilon
  obtain ⟨hxC, hyC, hxNorm, hyNorm, hlower⟩ := hdata r hr (half_lt_self hepsilon)
  let x := H.symm (gamma (u - r))
  let y := H.symm (gamma (u + r))
  have hxy : ‖A (y - x)‖ ≤ (theta * r) * d := by
    rw [map_sub]
    exact hchord (theta * r) (mul_pos hthetaPos hr) (A x) ⟨x, hxC, rfl⟩
      (A y) ⟨y, hyC, rfl⟩ hxNorm hyNorm
  have hstrict : theta * ‖A (y - x)‖ < 2 * r := calc
    theta * ‖A (y - x)‖ ≤ theta * ((theta * r) * d) :=
      mul_le_mul_of_nonneg_left hxy hthetaPos.le
    _ = r * (theta ^ 2 * d) := by ring
    _ < r * 2 := mul_lt_mul_of_pos_left htheta2 hr
    _ = 2 * r := mul_comm _ _
  exact (not_lt_of_ge hlower) hstrict

end PoincareConjecture
