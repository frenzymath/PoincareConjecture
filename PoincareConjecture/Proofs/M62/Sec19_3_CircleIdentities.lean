import PoincareConjecture.Proofs.M62.Sec19_3_CircleMetric
import PoincareConjecture.Proofs.M01.NormalizationScaling
import PoincareConjecture.Proofs.M04.KoszulPairing
import PoincareConjecture.Proofs.M04.RiemannRegularity
import PoincareConjecture.Proofs.M04.CurvatureAlgebra
import PoincareConjecture.Statements.M62Geometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M62

set_option maxHeartbeats 800000 in

theorem circle_identities {p : ℝ} (C : CircleGeometry p) : CircleIdentities C := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (AddCircle p) := C.chartedSpace
  let : IsManifold (𝓡 1) ∞ (AddCircle p) := C.isManifold
  have hframe : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
      (fun q : C.Point => (⟨q, C.frame q⟩ : TangentBundle (𝓡 1) C.Point)) := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hlocal := C.quotient_local_diffeomorph s
    have hconst : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞
        (fun r : ℝ => (⟨r, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    have hlift := hconst.contMDiffAt.comp (s : C.Point) hlocal.localInverse_contMDiffAt
    have h := (C.quotient_smooth.contMDiff_tangentMap (m := ∞) (by simp)).contMDiffAt.comp
      (s : C.Point) hlift
    apply h.congr_of_eventuallyEq
    filter_upwards [hlocal.localInverse_open_source.mem_nhds hlocal.localInverse_mem_source]
      with q hq
    change (⟨q, C.frame q⟩ : TangentBundle (𝓡 1) C.Point) =
      ⟨((hlocal.localInverse q : ℝ) : AddCircle p),
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun r : ℝ => (r : AddCircle p))
          (hlocal.localInverse q) 1⟩
    rw [← C.frame_quotient (hlocal.localInverse q), hlocal.localInverse_right_inv hq]
  have hunit (q : C.Point) : C.metricOnPoints.inner q (C.frame q) (C.frame q) = 1 := by
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [C.frame_quotient, C.metric_quotient]
    norm_num
  have hnonzero (q : C.Point) : C.frame q ≠ 0 := by
    intro hq
    have h := hunit q
    simp only [hq, map_zero] at h
    norm_num at h
  have hspan (q : C.Point) (V : TangentSpace (𝓡 1) q) : ∃ r : ℝ, r • C.frame q = V :=
    exists_smul_eq_of_finrank_eq_one (by simp [TangentSpace]) (hnonzero q) V
  refine {
    frame_smooth := hframe
    frame_unit := hunit
    frame_parallel := ?_
    curvature_zero := ?_
    circumference_eq := ?_ }
  · intro q V
    have hpair := M04.metric_derivative_pairing C.connectionOnPoints (fun _ => V)
      ((hframe q).mdifferentiableAt (by simp)) ((hframe q).mdifferentiableAt (by simp))
    have heq : (fun y => C.metricOnPoints.inner y (C.frame y) (C.frame y)) = fun _ => (1 : ℝ) :=
      funext hunit
    rw [heq, mvfderiv_const] at hpair
    rw [C.metricOnPoints.symm q (C.frame q)] at hpair
    obtain ⟨r, hr⟩ := hspan q (C.connectionOnPoints.connection C.frame q V)
    rw [← hr] at hpair
    simp only [map_smul, smul_apply, smul_eq_mul, hunit, mul_one] at hpair
    change 0 = r + r at hpair
    have hr0 : r = 0 := by linarith
    rw [← hr, hr0, zero_smul]
  · intro q V W Z T
    obtain ⟨A, hA⟩ := (M04.isSmoothCovariantTensor_riemannEvaluation C.connectionOnPoints).1 q
    have hzero : A (fun _ => C.frame q) = 0 := by
      have hs := M04.curvatureTensor_swap_first C.connectionOnPoints q
        (C.frame q) (C.frame q) (C.frame q) (C.frame q)
      have he : C.connectionOnPoints.curvatureTensor q
          (C.frame q) (C.frame q) (C.frame q) (C.frame q) = A (fun _ => C.frame q) :=
        hA (fun _ => C.frame q)
      rw [he] at hs
      linarith
    choose r hr using fun i : Fin 4 => hspan q (![V, W, Z, T] i)
    have heq : ![V, W, Z, T] = fun i => r i • C.frame q := funext fun i => (hr i).symm
    change C.connectionOnPoints.riemannEvaluation q ![V, W, Z, T] = 0
    rw [hA, heq, A.map_smul_univ, hzero, smul_zero]
  · unfold RiemannianMetric.pathELength
    simp only [pathELength_eq_lintegral_mfderiv_Icc, m01_tangentEnorm_eq]
    have hnorm (s : ℝ) : C.metricOnPoints.tangentNorm (C.quotient s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) C.quotient s 1) = 1 := by
      change Real.sqrt (C.metric.inner (s : AddCircle p)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun r : ℝ => (r : AddCircle p)) s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun r : ℝ => (r : AddCircle p)) s 1)) = 1
      rw [C.metric_quotient]
      norm_num
    simp_rw [hnorm]
    simp [Real.volume_Icc]

end PoincareConjecture.M62
