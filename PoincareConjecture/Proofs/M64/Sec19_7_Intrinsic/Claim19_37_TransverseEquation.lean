import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalFrame

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_inverse_parallel_jacobi_vector
    (N : IntrinsicAnnulus) {q : ℝ → AnnulusCoordinates} {I : Set ℝ} {b t : ℝ}
    (hb : 0 < b) (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ q I)
    (hsub : Icc (0 : ℝ) b ⊆ I)
    {P : ℝ → AnnulusCoordinates →L[ℝ] AnnulusCoordinates}
    (hPi : ∀ s ∈ Icc (0 : ℝ) b, (P s).IsInvertible)
    (hP : ∀ s ∈ Icc (0 : ℝ) b, ∀ u,
      ContDiffAt ℝ ∞ (chartField q (q s) (fun r => P r u)) s ∧
      manifoldCovDerivAlong N.metric q (fun r => P r u) 1 s = 0)
    {X : ℝ → AnnulusCoordinates}
    (hX : ∀ s ∈ I, ContDiffAt ℝ ∞ (chartField q (q s) X) s)
    (hjac : ∀ s ∈ Icc (0 : ℝ) b,
      manifoldCovDerivAlong N.metric q (manifoldCovDerivAlong N.metric q X 1) 1 s =
        -N.connection.curvature (q s) (X s) (curveVelocity (n := 2) q s)
          (curveVelocity (n := 2) q s))
    (ht : t ∈ Icc (0 : ℝ) b) :
    let Y := fun s => (P s).inverse (X s)
    HasDerivAt (deriv Y)
      (-(P t).inverse (N.connection.curvature (q t) (X t)
        (curveVelocity (n := 2) q t) (curveVelocity (n := 2) q t))) t := by
  let Y : ℝ → AnnulusCoordinates := fun s => (P s).inverse (X s)
  have hqt (s : ℝ) (hs : s ∈ I) := hq.contMDiffAt (hI.mem_nhds hs)
  have hY (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) : ContDiffAt ℝ ∞ Y s :=
    RiemannianMetric.contDiffAt_inverse_frame_field (hqt s (hsub hs)) (hPi s hs)
      (fun u => (hP s hs u).1) (hX s (hsub hs))
  have hval (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      deriv Y s = (P s).inverse (manifoldCovDerivAlong N.metric q X 1 s) :=
    (inverse_manifold_parallel_hasDerivAt N.metric hb hs hPi
      (hqt s (hsub hs)) (hP s hs) ((hX s (hsub hs)).differentiableAt (by simp))).deriv
  have hDX := contDiffAt_chartField_covDeriv N.metric hI hq hX (hsub ht)
    (mem_extChartAt_source _)
  have hd := inverse_manifold_parallel_hasDerivAt N.metric hb ht hPi
    (hqt t (hsub ht)) (hP t ht) (hDX.differentiableAt (by simp))
  rw [hjac t ht, map_neg] at hd
  have hwithin := hd.hasDerivWithinAt.congr (fun s hs => hval s hs) (hval t ht)
  have hV : ContDiffAt ℝ ∞ (deriv Y) t := (hY t ht).derivWithin (by simp)
  have heq := ((hV.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc hb t ht)).symm.trans
      (hwithin.derivWithin (uniqueDiffOn_Icc hb t ht))
  exact heq ▸ (hV.differentiableAt (by simp)).hasDerivAt

theorem m64Intrinsic_transverse_jacobi_equation
    (N : IntrinsicAnnulus) {q : ℝ → AnnulusCoordinates} {I : Set ℝ} {b t : ℝ}
    (hb : 0 < b) (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ q I)
    (hsub : Icc (0 : ℝ) b ⊆ I)
    {P : ℝ → AnnulusCoordinates →L[ℝ] AnnulusCoordinates}
    (hPi : ∀ s ∈ Icc (0 : ℝ) b, (P s).IsInvertible)
    (hP : ∀ s ∈ Icc (0 : ℝ) b, ∀ u,
      ContDiffAt ℝ ∞ (chartField q (q s) (fun r => P r u)) s ∧
      manifoldCovDerivAlong N.metric q (fun r => P r u) 1 s = 0)
    (hpair : ∀ s ∈ Icc (0 : ℝ) b, ∀ u v,
      N.metric.inner (q s) (P s u) (P s v) = inner ℝ u v)
    (theta nu : AnnulusCoordinates) (htheta : inner ℝ theta theta = 1)
    (horth : inner ℝ theta nu = 0)
    (hvelocity : ∀ s ∈ Icc (0 : ℝ) b, P s theta = curveVelocity (n := 2) q s)
    {X : ℝ → AnnulusCoordinates}
    (hX : ∀ s ∈ I, ContDiffAt ℝ ∞ (chartField q (q s) X) s)
    (hjac : ∀ s ∈ Icc (0 : ℝ) b,
      manifoldCovDerivAlong N.metric q (manifoldCovDerivAlong N.metric q X 1) 1 s =
        -N.connection.curvature (q s) (X s) (curveVelocity (n := 2) q s)
          (curveVelocity (n := 2) q s))
    (ht : t ∈ Icc (0 : ℝ) b) :
    let Y := fun s => (P s).inverse (X s)
    HasDerivAt (fun s => inner ℝ nu (deriv Y s))
      (-(N.connection.scalarCurvature (q t) / 2) * inner ℝ nu (Y t)) t := by
  have hd := m64Intrinsic_inverse_parallel_jacobi_vector N hb hI hq hsub hPi hP hX hjac ht
  have h := (hasDerivAt_const t nu).inner ℝ hd
  simp only [inner_zero_left, add_zero, inner_neg_right] at h
  rw [← hvelocity t ht] at h
  have hcurv := m64Intrinsic_radialCurvature_transverse_pairing N (q t) (P t)
    (hPi t ht) (hpair t ht) theta nu ((P t).inverse (X t)) htheta horth
  rw [(hPi t ht).self_apply_inverse, N.metric.radialCurvatureOperator_apply N.connection]
    at hcurv
  rw [hcurv, ← neg_mul] at h
  exact h

end PoincareConjecture
