import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_IntrinsicJacobi

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_chartField_eq
    (q V : ℝ → AnnulusCoordinates) (p : AnnulusCoordinates) :
    chartField q p V = V := by
  funext t
  simp [chartField]

theorem m64Intrinsic_exists_normal_scalar_jacobi
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0)
    {u : ℝ × ℝ → AnnulusCoordinates} {S I : Set ℝ}
    (hS : IsOpen S) (hI : IsOpen I)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (S ×ˢ I))
    (hgeo : ∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I)
    (hboundary : ∀ s ∈ S, u (s, 0) = intrinsicAnnulusBoundary radius s)
    {a b : ℝ} (ha : a ∈ S) (hb : 0 < b) (hsub : Icc (0 : ℝ) b ⊆ I)
    {normal : AnnulusCoordinates}
    (hunit : N.metric.inner (intrinsicAnnulusBoundary radius a) normal normal = 1)
    (horth : N.metric.inner (intrinsicAnnulusBoundary radius a) normal
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a) = 0)
    (hvelocity : HasDerivAt (fun t => u (a, t)) normal 0) :
    let q : ℝ → AnnulusCoordinates := fun t => u (a, t)
    let X : ℝ → AnnulusCoordinates := fun t => curveVelocity (n := 2) (fun s => u (s, t)) a
    ∃ (W : ℝ → AnnulusCoordinates) (j v : ℝ → ℝ),
      W 0 = intrinsicBoundaryUnitTangent N.metric radius a ∧ j 0 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) b,
        ContDiffAt ℝ ∞ W t ∧ N.metric.inner (q t) (W t) (W t) = 1 ∧
        N.metric.inner (q t) (W t) (curveVelocity (n := 2) q t) = 0 ∧
        manifoldCovDerivAlong N.metric q W 1 t = 0 ∧
        j t = N.metric.inner (q t) (X t) (W t) / intrinsicBoundarySpeed N.metric radius a ∧
        v t = N.metric.inner (q t) (manifoldCovDerivAlong N.metric q X 1 t) (W t) /
          intrinsicBoundarySpeed N.metric radius a ∧
        HasDerivAt j (v t) t ∧
        HasDerivAt v (-(N.connection.scalarCurvature (q t) / 2) * j t) t ∧
        ContDiffAt ℝ ∞ j t := by
  let q : ℝ → AnnulusCoordinates := fun t => u (a, t)
  let X : ℝ → AnnulusCoordinates := fun t => curveVelocity (n := 2) (fun s => u (s, t)) a
  let speed := intrinsicBoundarySpeed N.metric radius a
  have hs : 0 < speed := m64Intrinsic_boundarySpeed_pos N hradius a
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ q I := by
    intro t ht
    exact ((hu.contMDiffAt ((hS.prod hI).mem_nhds ⟨ha, ht⟩)).comp t
      (show ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun r => (a, r)) t from
        contMDiffAt_iff_contDiffAt.mpr (by fun_prop))).contMDiffWithinAt
  have hX (t : ℝ) (ht : t ∈ I) : ContDiffAt ℝ ∞ (chartField q (q t) X) t := by
    rw [m64Intrinsic_chartField_eq]
    exact m64Intrinsic_contDiff_variation_field hS hI hu.contDiffOn ha ht
  have hjac (t : ℝ) (ht : t ∈ Icc (0 : ℝ) b) :
      manifoldCovDerivAlong N.metric q (manifoldCovDerivAlong N.metric q X 1) 1 t =
        -N.connection.curvature (q t) (X t) (curveVelocity (n := 2) q t)
          (curveVelocity (n := 2) q t) :=
    m64Intrinsic_variation_intrinsic_jacobi N hS hI hu hgeo ha (hsub ht)
  obtain ⟨P, hPnormal, hPtangent, hPi, hP, hpair, hPvelocity⟩ :=
    m64Intrinsic_exists_normal_parallel_frame N hradius a hunit horth hb hI hq hsub
      (hgeo a ha) (hboundary a ha) hvelocity
  let nu : AnnulusCoordinates := !₂[0, 1]
  let Y : ℝ → AnnulusCoordinates := fun t => (P t).inverse (X t)
  let W : ℝ → AnnulusCoordinates := fun t => P t nu
  let j : ℝ → ℝ := fun t => inner ℝ nu (Y t) / speed
  let v : ℝ → ℝ := fun t => inner ℝ nu (deriv Y t) / speed
  have hY (t : ℝ) (ht : t ∈ Icc (0 : ℝ) b) : ContDiffAt ℝ ∞ Y t :=
    RiemannianMetric.contDiffAt_inverse_frame_field (hq.contMDiffAt (hI.mem_nhds (hsub ht)))
      (hPi t ht) (fun w => (hP t ht w).1) (hX t (hsub ht))
  have hpairV (t : ℝ) (ht : t ∈ Icc (0 : ℝ) b) (Z : AnnulusCoordinates) :
      inner ℝ nu ((P t).inverse Z) = N.metric.inner (q t) Z (W t) := by
    rw [← hpair t ht nu ((P t).inverse Z), (hPi t ht).self_apply_inverse, N.metric.symm]
  have hjeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) b) :
      j t = N.metric.inner (q t) (X t) (W t) / speed := by
    exact congrArg (fun r => r / speed) (hpairV t ht (X t))
  have hXzero : X 0 = curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a := by
    have heq : (fun s => u (s, 0)) =ᶠ[𝓝 a] intrinsicAnnulusBoundary radius := by
      filter_upwards [hS.mem_nhds ha] with s hs
      exact hboundary s hs
    change curveVelocity (n := 2) (fun s => u (s, 0)) a = _
    rw [m64Intrinsic_curveVelocity_eq_deriv, m64Intrinsic_curveVelocity_eq_deriv]
    exact heq.deriv_eq
  have hWzero : W 0 = intrinsicBoundaryUnitTangent N.metric radius a := hPtangent
  have hjzero : j 0 = 1 := by
    rw [hjeq 0 hzero, hWzero, hXzero]
    change N.metric.inner (u (a, 0))
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a)
      (intrinsicBoundaryUnitTangent N.metric radius a) / speed = 1
    rw [hboundary a ha]
    have hsq : speed ^ 2 = N.metric.inner (intrinsicAnnulusBoundary radius a)
        (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a)
        (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a) :=
      Real.sq_sqrt (Real.sqrt_pos.mp hs).le
    simp only [intrinsicBoundaryUnitTangent, map_smul, smul_eq_mul, ← hsq]
    change (speed⁻¹ * speed ^ 2) / speed = 1
    field_simp
  refine ⟨W, j, v, hWzero, hjzero, ?_⟩
  intro t ht
  have hW := (hP t ht nu).1
  rw [m64Intrinsic_chartField_eq] at hW
  have hWunit : N.metric.inner (q t) (W t) (W t) = 1 := by
    change N.metric.inner (q t) (P t nu) (P t nu) = 1
    rw [hpair t ht]
    simp only [nu, PiLp.inner_apply, Fin.sum_univ_two]
    norm_num
  have hWorth : N.metric.inner (q t) (W t) (curveVelocity (n := 2) q t) = 0 := by
    rw [← hPvelocity t ht]
    change N.metric.inner (q t) (P t nu) (P t !₂[1, 0]) = 0
    rw [hpair t ht]
    simp only [nu, PiLp.inner_apply, Fin.sum_univ_two]
    norm_num
  have hDY := inverse_manifold_parallel_hasDerivAt N.metric hb ht hPi
    (hq.contMDiffAt (hI.mem_nhds (hsub ht))) (hP t ht) ((hX t (hsub ht)).differentiableAt
      (by simp))
  have hveq : v t = N.metric.inner (q t)
      (manifoldCovDerivAlong N.metric q X 1 t) (W t) / speed := by
    change inner ℝ nu (deriv Y t) / speed = _
    rw [hDY.deriv, hpairV t ht]
  have hdj : HasDerivAt j (v t) t := by
    simpa only [inner_zero_left, add_zero] using
      ((hasDerivAt_const t nu).inner ℝ
        ((hY t ht).differentiableAt (by simp)).hasDerivAt).div_const speed
  have hdv := m64Intrinsic_transverse_jacobi_equation N hb hI hq hsub hPi hP hpair
    !₂[1, 0] nu (by simp only [PiLp.inner_apply, Fin.sum_univ_two]; norm_num)
    (by simp only [nu, PiLp.inner_apply, Fin.sum_univ_two]; norm_num) hPvelocity hX hjac ht
  have hdv' : HasDerivAt v (-(N.connection.scalarCurvature (q t) / 2) * j t) t := by
    simpa only [j, v, Y, div_eq_mul_inv, mul_assoc] using! hdv.div_const speed
  refine ⟨hW, hWunit, hWorth, (hP t ht nu).2, hjeq t ht, hveq, hdj, hdv', ?_⟩
  exact (contDiffAt_const.inner ℝ (hY t ht)).div_const speed

end PoincareConjecture
