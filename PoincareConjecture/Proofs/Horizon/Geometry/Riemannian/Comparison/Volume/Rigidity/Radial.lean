import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.RadialComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]


theorem deriv2_polarDensityRoot_le_radialRicci
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ U)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1)
    {b t : ℝ} (hb : 0 < b) (hsub : ∀ s ∈ Icc 0 b, s • θ ∈ U)
    (ht : t ∈ Ioo 0 b)
    (hi : Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • θ))) :
    deriv (deriv (fun s : ℝ =>
      s * g.pullbackVolumeDensity e (s • θ) ^ (1 / (m : ℝ)))) t ≤
      (-D.ricci (e (t • θ)) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • θ) θ)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • θ) θ) / (m : ℝ)) *
        (t * g.pullbackVolumeDensity e (t • θ) ^ (1 / (m : ℝ))) := by
  obtain ⟨basis, hθbasis⟩ := exists_orthonormalBasis_radial θ hθ
  subst θ
  obtain ⟨P, hP0, hPi, hpair, hrad, hJ0, hJ, hV⟩ :=
    g.exists_radial_parallel_jacobi D hU h0 he hgeo hmetric (basis 0) hb hsub
  let J : ℝ → EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    fun s => (P s).inverse.comp (s • mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • basis 0))
  let K : ℝ → EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    fun s => (P s).inverse.comp
      ((g.radialCurvatureOperator (e (s • basis 0)) (P s (basis 0))).comp (P s))
  have hK (s : ℝ) (hs : s ∈ Icc 0 b) : LinearMap.IsSymmetric (K s).toLinearMap := by
    intro u v
    change inner ℝ ((P s).inverse (g.radialCurvatureOperator (e (s • basis 0))
      (P s (basis 0)) (P s u))) v =
        inner ℝ u ((P s).inverse (g.radialCurvatureOperator (e (s • basis 0))
          (P s (basis 0)) (P s v)))
    rw [← hpair s hs, ← hpair s hs, (hPi s hs).self_apply_inverse,
      (hPi s hs).self_apply_inverse, g.radialCurvatureOperator_apply D,
      g.radialCurvatureOperator_apply D]
    exact D.inner_radial_curvature_symm _ _ _ _
  have hKr (s : ℝ) (_hs : s ∈ Icc 0 b) : K s (basis 0) = 0 := by
    change (P s).inverse (g.radialCurvatureOperator (e (s • basis 0))
      (P s (basis 0)) (P s (basis 0))) = 0
    rw [g.radialCurvatureOperator_self D, map_zero]
  have hdet (s : ℝ) (hs : s ∈ Icc 0 b) (hs0 : 0 < s) :
      |((LinearMap.toMatrix basis.toBasis basis.toBasis (J s).toLinearMap).submatrix
        Fin.succ Fin.succ).det| = s ^ m * g.pullbackVolumeDensity e (s • basis 0) :=
    g.abs_det_transverse_radialDifferential_of_isInvertible e basis hs0
      (P s) (hPi s hs) (hpair s hs) (hrad s hs).symm
  have ht' : t ∈ Icc 0 b := ⟨ht.1.le, ht.2.le⟩
  have hρ := (g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (hU.mem_nhds (hsub t ht'))) hi).2
  have hne : ((LinearMap.toMatrix basis.toBasis basis.toBasis (J t).toLinearMap).submatrix
      Fin.succ Fin.succ).det ≠ 0 := by
    apply abs_pos.mp
    rw [hdet t ht' ht.1]
    exact mul_pos (pow_pos ht.1 _) hρ
  let κ := -D.ricci (e (t • basis 0)) (P t (basis 0)) (P t (basis 0)) / (m : ℝ)
  have htrace : -(m : ℝ) * κ ≤
      ((LinearMap.toMatrix basis.toBasis basis.toBasis (K t).toLinearMap).submatrix
        Fin.succ Fin.succ).trace := by
    have htr : ((LinearMap.toMatrix basis.toBasis basis.toBasis
        (K t).toLinearMap).submatrix Fin.succ Fin.succ).trace =
        D.ricci (e (t • basis 0)) (P t (basis 0)) (P t (basis 0)) :=
      g.trace_transverse_frame_radialCurvatureOperator_of_isInvertible
        D (e (t • basis 0)) basis (P t) (hPi t ht') (hpair t ht')
    rw [htr]
    dsimp [κ]
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    field_simp
    exact le_rfl
  have hcomp := deriv2_abs_transverse_determinantRoot_le_of_jacobi basis
    (J := J) (V := deriv J) (K := K) hm
    (fun s hs => ((hJ s hs).differentiableAt (by simp)).hasDerivAt)
    hV hK hKr hJ0 ht hne htrace
  have heq : (fun s =>
      |((LinearMap.toMatrix basis.toBasis basis.toBasis (J s).toLinearMap).submatrix
        Fin.succ Fin.succ).det| ^ (1 / (m : ℝ))) =ᶠ[𝓝 t]
      (fun s => s * g.pullbackVolumeDensity e (s • basis 0) ^ (1 / (m : ℝ))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hρ0 : 0 ≤ g.pullbackVolumeDensity e (s • basis 0) := Real.sqrt_nonneg _
    rw [hdet s ⟨hs.1.le, hs.2.le⟩ hs.1,
      Real.mul_rpow (pow_nonneg hs.1.le _) hρ0, one_div,
      Real.pow_rpow_inv_natCast hs.1.le hm.ne']
  rw [heq.deriv.deriv_eq] at hcomp
  have hval := heq.self_of_nhds
  dsimp only at hval
  rw [hval] at hcomp
  simpa only [κ, hrad t ht'] using hcomp


theorem radialRicci_le_zero_of_pullbackVolumeDensity_eq_one
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ U)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1)
    {b t : ℝ} (hb : 0 < b) (hsub : ∀ s ∈ Icc 0 b, s • θ ∈ U)
    (ht : t ∈ Ioo 0 b)
    (hi : Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • θ)))
    (hρ : ∀ s ∈ Ioo 0 b, g.pullbackVolumeDensity e (s • θ) = 1) :
    D.ricci (e (t • θ)) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • θ) θ)
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (t • θ) θ) ≤ 0 := by
  have hcomp := g.deriv2_polarDensityRoot_le_radialRicci D hm hU h0 he hgeo hmetric
    θ hθ hb hsub ht hi
  have heq : (fun s : ℝ =>
      s * g.pullbackVolumeDensity e (s • θ) ^ (1 / (m : ℝ))) =ᶠ[𝓝 t] id := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    simp only [hρ s hs, Real.one_rpow, mul_one, id_eq]
  rw [heq.deriv.deriv_eq] at hcomp
  change deriv (deriv (fun s : ℝ => s)) t ≤ _ at hcomp
  simp only [deriv_id'', deriv_const, hρ t ht, Real.one_rpow, mul_one] at hcomp
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hcoef := (mul_nonneg_iff_of_pos_right ht.1).mp hcomp
  exact neg_nonneg.mp (by simpa only [zero_mul] using (le_div_iff₀ hmR).mp hcoef)

private theorem continuousAt_ricci_curve
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {g : RiemannianMetric n N} (D : LeviCivitaData g)
    {q : ℝ → N} {V : (s : ℝ) → TangentSpace (𝓡 n) (q s)} {t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hV : ContDiffAt ℝ ∞ (ConnectionAlongCurve.chartField q (q t) V) t) :
    ContinuousAt (fun s => D.ricci (q s) (V s) (V s)) t := by
  let c := extChartAt (𝓡 n) (q t)
  let S := fun s => LeviCivitaData.tensorCoordinateSection
    D.ricciEvaluation_isSmooth_manifold (q t) (c.symm (c (q s)))
  have hcoord := ConnectionAlongCurve.contDiffAt_chart_curve hq (mem_extChartAt_source _)
  have hS : ContDiffAt ℝ ∞ S t := by
    have hSt := LeviCivitaData.contDiffAt_tensorCoordinateSection
      D.ricciEvaluation_isSmooth_manifold (q t) (c.map_source (mem_extChartAt_source _))
    have hSc := hSt.comp t hcoord
    exact hSc
  have hVs : ContDiffAt ℝ ∞ (fun s => fun _ : Fin 2 =>
      ConnectionAlongCurve.chartField q (q t) V s) t := contDiffAt_pi.mpr (fun _ => hV)
  have heval := (TensorFiber.continuousMultilinear
    (E := EuclideanSpace ℝ (Fin n)) (k := 2)).analyticOnNhd_uncurry_of_multilinear
    (s := Set.univ) |>.contDiff (n := ∞)
  have hc := (heval.contDiffAt.comp t (hS.prodMk hVs)).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [hq.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 n) (q t)).mem_nhds
      (mem_extChartAt_source (I := 𝓡 n) _))] with s hs
  have hrec : LeviCivitaData.constantCoordinateField (q t)
      (ConnectionAlongCurve.chartField q (q t) V s) (q s) = V s := by
    unfold LeviCivitaData.constantCoordinateField ConnectionAlongCurve.chartField
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [Set.mem_preimage, extChartAt_source] using hs)]
    exact Bundle.Trivialization.symmL_continuousLinearMapAt _
      (by simpa only [Set.mem_preimage, TangentBundle.trivializationAt_baseSet,
        extChartAt_source] using hs) _
  simp only [Function.comp_apply, TensorFiber.continuousMultilinear_apply, S,
    c.left_inv hs, LeviCivitaData.tensorCoordinateSection_apply,
    LeviCivitaData.tensorCoordinateEvaluation, LeviCivitaData.ricciEvaluation, hrec]


theorem ricci_center_unit_eq_zero_of_pullbackVolumeDensity_eq_one
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    {U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ U)
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 v) = inner ℝ u v)
    (hi : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin (m + 1))),
      Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e v))
    (hρ : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin (m + 1))),
      g.pullbackVolumeDensity e v = 1)
    (hRic : ∀ v : TangentSpace (𝓡 (m + 1)) (e 0), 0 ≤ D.ricci (e 0) v v)
    (θ : EuclideanSpace ℝ (Fin (m + 1))) (hθ : ‖θ‖ = 1) :
    D.ricci (e 0) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 θ)
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e 0 θ) = 0 := by
  have hnear : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin (m + 1))),
      v ∈ U ∧ Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e v) ∧
        g.pullbackVolumeDensity e v = 1 := by
    filter_upwards [hU.mem_nhds h0, hi, hρ] with v hv hvi hvρ
    exact ⟨hv, hvi, hvρ⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hb : 0 < r / 2 := half_pos hr
  have hrad (s : ℝ) (hs : s ∈ Icc 0 (r / 2)) : s • θ ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1, hθ, mul_one]
    linarith [hs.2]
  have hsub (s : ℝ) (hs : s ∈ Icc 0 (r / 2)) : s • θ ∈ U := (hball (hrad s hs)).1
  let q : ℝ → M := fun s => e (s • θ)
  let I : Set ℝ := {s | s • θ ∈ U}
  have hI : IsOpen I := hU.preimage (by fun_prop)
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (m + 1)) ∞ q I := by
    intro t ht
    exact ((he.contMDiffAt (hU.mem_nhds ht)).comp t
      (show ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 (m + 1)) ∞ (fun s : ℝ => s • θ) t from
        contMDiffAt_iff_contDiffAt.mpr (by fun_prop))).contMDiffWithinAt
  have hI0 : (0 : ℝ) ∈ I := by simpa [I] using h0
  have hcont := continuousAt_ricci_curve D (hq.contMDiffAt (hI.mem_nhds hI0))
    (contDiffAt_chartField_velocity hI hq hI0 (mem_extChartAt_source _))
  have heq : (fun s => D.ricci (q s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) q s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) q s 1)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => D.ricci (e (s • θ))
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ) θ)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ) θ)) := by
    filter_upwards [hI.mem_nhds hI0] with s hs
    rw [show mfderiv 𝓘(ℝ, ℝ) (𝓡 (m + 1)) q s 1 =
      mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ) θ from
      radial_velocity_eq_differential θ ((he.contMDiffAt (hU.mem_nhds hs)).mdifferentiableAt
        (by simp))]
  have hc := hcont.congr_of_eventuallyEq heq.symm
  have hle : ∀ᶠ s in 𝓝[>] (0 : ℝ), D.ricci (e (s • θ))
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ) θ)
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ) θ) ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT hb] with s hs
    exact g.radialRicci_le_zero_of_pullbackVolumeDensity_eq_one D hm hU h0 he hgeo
      hmetric θ hθ hb hsub hs (hball (hrad s ⟨hs.1.le, hs.2.le⟩)).2.1
      (fun u hu => (hball (hrad u ⟨hu.1.le, hu.2.le⟩)).2.2)
  apply le_antisymm _ (hRic _)
  have hlim := le_of_tendsto hc.continuousWithinAt hle
  change D.ricci (e ((0 : ℝ) • θ)) _ _ ≤ 0 at hlim
  erw [zero_smul] at hlim
  exact hlim

end PoincareConjecture.RiemannianMetric
