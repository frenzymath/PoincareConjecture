import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityConformalGreen
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCutoff











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap ENNReal

namespace PoincareConjecture.M65Boundary

private theorem inverse_memLp {p : ℂ} (hp : ‖p‖ = 1)
    {K : Set LoopPlane} (hK : IsCompact K)
    (hleft : ∀ z ∈ K, diskBoundaryInverse p (diskBoundaryCoordinate p z) = z)
    (hQ : ContinuousOn (diskBoundaryInverse p) (diskBoundaryCoordinate p '' K))
    (u : Lp ℝ 2 (volume.restrict K)) :
    MemLp (fun w => u (diskBoundaryInverse p w)) 2
      (volume.restrict (diskBoundaryCoordinate p '' K)) := by
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  have hP := contDiff_diskBoundaryCoordinate p
  have hZ : IsCompact (P '' K) := hK.image hP.continuous
  have hinj : InjOn P K := fun x hx y hy hxy => by
    have hh := congrArg Q hxy
    dsimp only [Q, P] at hh
    rwa [hleft x hx, hleft y hy] at hh
  have hm : AEStronglyMeasurable (fun w => u (Q w)) (volume.restrict (P '' K)) :=
    (Lp.stronglyMeasurable u).aestronglyMeasurable.comp_aemeasurable
      (hQ.aemeasurable hZ.measurableSet)
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hK.measurableSet
    (fun z _ => (hP.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt) hinj _).mpr
  have hJ : ContinuousOn (fun z : LoopPlane => Real.exp (-z 1) ^ 2) K := by fun_prop
  have huI : IntegrableOn (fun z => u z ^ 2) K := (Lp.memLp u).integrable_sq
  apply (IntegrableOn.continuousOn_mul hJ huI hK).congr
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  dsimp only [Q]
  rw [diskBoundaryCoordinate_det hp, abs_of_nonneg (sq_nonneg _), hleft z hz]
  rfl

private theorem memLp_continuousOn_mul {K : Set LoopPlane} (hK : IsCompact K)
    {a f : LoopPlane → ℝ} (ha : ContinuousOn a K)
    (hf : MemLp f 2 (volume.restrict K)) :
    MemLp (fun z => a z * f z) 2 (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ha
  apply hf.of_le_mul (c := C) ((ha.aestronglyMeasurable hK.measurableSet).mul hf.1)
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  simpa only [Pi.mul_apply, norm_mul] using
    mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg (f z))







theorem exists_boundary_halfDisk_pushforward_uniform :
    ∃ R : ℝ, 0 < R ∧ ∀ {p : ℂ}, ‖p‖ = 1 → ∀ r : ℝ, 0 < r → r ≤ R →
      let K := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      let Q := diskBoundaryInverse p
      P '' K ⊆ loopDiskSet ∧
      (∀ z ∈ K, Q (P z) = z) ∧
      ∀ (u : Lp ℝ 2 (volume.restrict K))
        (d : Fin 2 → Lp ℝ 2 (volume.restrict K)) (b : ℝ → ℝ),
        (∀ (test : 𝓢(LoopPlane, ℝ)) (k : Fin 2),
          (∫ z in K, d k z * test z +
            u z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ k)) =
            -(EuclideanSpace.basisFun (Fin 2) ℝ 1) k *
              ∫ s in (-r)..r, b s * test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) →
        let D := fun i w => ∑ k : Fin 2,
          ((fderiv ℝ P (Q w) (EuclideanSpace.basisFun (Fin 2) ℝ k)) i /
            Real.exp (-(Q w) 1) ^ 2) * d k (Q w)
        MemLp (fun w => u (Q w)) 2 (volume.restrict (P '' K)) ∧
        (∀ i, MemLp (D i) 2 (volume.restrict (P '' K))) ∧
        ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
          (∫ w in P '' K, D i w * test w +
            u (Q w) * fderiv ℝ test w (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
            ∫ s in (-r)..r, b s *
              test (P (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) *
                P (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) i := by
  obtain ⟨R, hR, hgeometry⟩ := exists_uniform_boundary_halfDisk_pullback
  refine ⟨R, hR, ?_⟩
  intro p hp r hr hrR
  obtain ⟨hleftR, hcapR, hinvR, _C, _hC, _hmap⟩ := hgeometry p hp
  dsimp only
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  let K := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let Z := P '' K
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let J := fun z : LoopPlane => Real.exp (-z 1) ^ 2
  have hP := contDiff_diskBoundaryCoordinate p
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hZ : IsCompact Z := hK.image hP.continuous
  have hKR : K ⊆ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1} :=
    inter_subset_inter (closedBall_subset_closedBall hrR) Subset.rfl
  have hleft (z : LoopPlane) (hz : z ∈ K) : Q (P z) = z := hleftR z (hKR hz).1
  have hQ : ContinuousOn Q Z := by
    intro w hw
    exact (hinvR w (image_mono hKR hw)).continuousAt.continuousWithinAt
  have hinj : InjOn P K := fun x hx y hy hxy => by
    have hh := congrArg Q hxy
    rwa [hleft x hx, hleft y hy] at hh
  have hJ : Continuous J := by fun_prop
  have hJpos (z : LoopPlane) : 0 < J z := sq_pos_of_pos (Real.exp_pos _)
  refine ⟨?_, hleft, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hcapR (hKR hz)
  intro u d b hgreen
  let D := fun i w => ∑ k : Fin 2, ((fderiv ℝ P (Q w) (e k)) i / J (Q w)) * d k (Q w)
  have huL := inverse_memLp hp hK hleft hQ u
  have hdL (k : Fin 2) := inverse_memLp hp hK hleft hQ (d k)
  have hcoef (i k : Fin 2) : ContinuousOn
      (fun w => (fderiv ℝ P (Q w) (e k)) i / J (Q w)) Z := by
    have hc : Continuous (fun z => (fderiv ℝ P z (e k)) i) :=
      (EuclideanSpace.proj i).continuous.comp
        ((hP.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact (hc.comp_continuousOn hQ).div (hJ.comp_continuousOn hQ)
      (fun w _ => (hJpos (Q w)).ne')
  have hDL (i : Fin 2) : MemLp (D i) 2 (volume.restrict Z) := by
    have h0 := memLp_continuousOn_mul hZ (hcoef i 0) (hdL 0)
    have h1 := memLp_continuousOn_mul hZ (hcoef i 1) (hdL 1)
    simpa +instances only [D, Fin.sum_univ_two, Pi.add_apply, Q] using! h0.add h1
  refine ⟨huL, hDL, ?_⟩
  intro test i
  obtain ⟨chi, hchi, _hschi, hchiOne⟩ :=
    M65Interior.exists_disk_cutoff isOpen_univ (0 : LoopPlane) hr.le (subset_univ _)
  let f (k : Fin 2) := fun z => test (P z) * (fderiv ℝ P z (e k)) i
  have hfD (k : Fin 2) : ContDiff ℝ ∞ (fun z => fderiv ℝ P z (e k)) :=
    (hP.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply
      contDiff_const
  have hf (k : Fin 2) : ContDiff ℝ ∞ (f k) :=
    ((test.smooth (⊤ : ℕ∞)).comp hP).mul
      ((EuclideanSpace.proj i : LoopPlane →L[ℝ] ℝ).contDiff.comp (hfD k))
  have hprod (k : Fin 2) : HasCompactSupport (fun z => chi z * f k z) := hchi.mul_right
  let T (k : Fin 2) : 𝓢(LoopPlane, ℝ) :=
    (hprod k).toSchwartzMap ((chi.smooth (⊤ : ℕ∞)).mul (hf k))
  have hT (k : Fin 2) (z : LoopPlane) (hz : z ∈ closedBall (0 : LoopPlane) r) :
      (T k) =ᶠ[𝓝 z] f k := by
    filter_upwards [(hchiOne z hz).1] with w hw
    change chi w * f k w = f k w
    rw [hw, one_mul]
  let term (k : Fin 2) := fun z => d k z * T k z + u z * fderiv ℝ (T k) z (e k)
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hterm (k : Fin 2) : IntegrableOn (term k) K := by
    have hdt : Continuous (fun z => fderiv ℝ (T k) z (e k)) :=
      ((T k).smooth 1).continuous_fderiv one_ne_zero |>.clm_apply continuous_const
    have h1 := (memLp_continuousOn_mul hK (T k).continuous.continuousOn
      (Lp.memLp (d k))).integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have h2 := (memLp_continuousOn_mul hK hdt.continuousOn
      (Lp.memLp u)).integrable (by norm_num : (1 : ENNReal) ≤ 2)
    simpa +instances only [term, Pi.add_apply, mul_comm, IntegrableOn] using! h1.add h2
  have hpoint (z : LoopPlane) (hz : z ∈ K) :
      J z * (D i (P z) * test (P z) +
        u (Q (P z)) * fderiv ℝ test (P z) (e i)) = ∑ k : Fin 2, term k z := by
    have hsum := diskBoundaryCoordinate_test_divergence hp test (test.smooth 1) z i
    have hTval (k : Fin 2) : T k z = f k z := (hT k z hz.1).self_of_nhds
    have hTD (k : Fin 2) : fderiv ℝ (T k) z = fderiv ℝ (f k) z := (hT k z hz.1).fderiv_eq
    change (∑ k : Fin 2, fderiv ℝ (f k) z (e k)) = J z * fderiv ℝ test (P z) (e i) at hsum
    simp only [term, hTval, hTD, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum, hleft z hz]
    dsimp only [D]
    rw [hleft z hz]
    simp only [Fin.sum_univ_two, f]
    field_simp [(hJpos z).ne']
  have hvol : (∫ w in Z, D i w * test w + u (Q w) * fderiv ℝ test w (e i)) =
      ∫ z in K, ∑ k : Fin 2, term k z := by
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume hK.measurableSet
      (fun z _ => (hP.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt) hinj]
    apply setIntegral_congr_fun hK.measurableSet
    intro z hz
    dsimp only
    rw [diskBoundaryCoordinate_det hp, abs_of_nonneg (sq_nonneg _)]
    exact hpoint z hz
  rw [hvol]
  simp_rw [Fin.sum_univ_two]
  rw [integral_add (hterm 0) (hterm 1)]
  change (∫ z in K, d 0 z * T 0 z + u z * fderiv ℝ (T 0) z (e 0)) +
    (∫ z in K, d 1 z * T 1 z + u z * fderiv ℝ (T 1) z (e 1)) = _
  rw [hgreen (T 0) 0, hgreen (T 1) 1]
  norm_num [EuclideanSpace.basisFun_apply]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s hs
  have hsI : s ∈ Icc (-r) r := by simpa only [uIcc_of_le (by linarith : -r ≤ r)] using hs
  have hsball : s • e 0 ∈ closedBall (0 : LoopPlane) r := by
    rw [mem_closedBall_zero_iff, norm_smul, e.norm_eq_one, mul_one, Real.norm_eq_abs]
    exact abs_le.mpr hsI
  have hfinish : -(b s * T 1 (s • e 0)) =
      b s * test (P (s • e 0)) * P (s • e 0) i := by
    rw [(hT 1 (s • e 0) hsball).self_of_nhds]
    dsimp only [f]
    have hc := congrArg (fun w : LoopPlane => w i)
      (diskBoundaryCoordinate_columns p (s • e 0)).2
    have hi : (fderiv ℝ P (s • e 0) (e 1)) i = -P (s • e 0) i := by
      fin_cases i <;> simpa [e, EuclideanSpace.basisFun_apply] using hc
    rw [hi]
    ring
  simpa only [P, e, EuclideanSpace.basisFun_apply] using hfinish



theorem exists_boundary_halfDisk_pushforward {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      let K := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      let Q := diskBoundaryInverse p
      P '' K ⊆ loopDiskSet ∧
      (∀ z ∈ K, Q (P z) = z) ∧
      ∀ (u : Lp ℝ 2 (volume.restrict K))
        (d : Fin 2 → Lp ℝ 2 (volume.restrict K)) (b : ℝ → ℝ),
        (∀ (test : 𝓢(LoopPlane, ℝ)) (k : Fin 2),
          (∫ z in K, d k z * test z +
            u z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ k)) =
            -(EuclideanSpace.basisFun (Fin 2) ℝ 1) k *
              ∫ s in (-r)..r, b s * test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) →
        let D := fun i w => ∑ k : Fin 2,
          ((fderiv ℝ P (Q w) (EuclideanSpace.basisFun (Fin 2) ℝ k)) i /
            Real.exp (-(Q w) 1) ^ 2) * d k (Q w)
        MemLp (fun w => u (Q w)) 2 (volume.restrict (P '' K)) ∧
        (∀ i, MemLp (D i) 2 (volume.restrict (P '' K))) ∧
        ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
          (∫ w in P '' K, D i w * test w +
            u (Q w) * fderiv ℝ test w (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
            ∫ s in (-r)..r, b s *
              test (P (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) *
                P (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) i := by
  obtain ⟨R, hR, h⟩ := exists_boundary_halfDisk_pushforward_uniform
  exact ⟨R, hR, h hp⟩

end PoincareConjecture.M65Boundary
