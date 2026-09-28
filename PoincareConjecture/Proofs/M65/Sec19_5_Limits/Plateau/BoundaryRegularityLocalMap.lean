import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityRadialEnergy
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityWeakMap










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap ENNReal LineDeriv

namespace PoincareConjecture.M65Boundary





theorem halfDisk_localMap_of_green {M : Type*} {N : ℕ}
    (e : M → EuclideanSpace ℝ (Fin N)) (value : LoopPlane → M)
    (D : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N)) {r : ℝ} (hr : 0 < r)
    (hu : MemLp (fun z => e (value z)) 2
      (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (hd : ∀ i, MemLp (D i) 2
      (volume.restrict (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1})))
    (v b : ℝ → EuclideanSpace ℝ (Fin N))
    (hgreen : ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        D i z j * test z + e (value z) j *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
        r * (∫ θ in (0 : ℝ)..Real.pi,
          v θ j * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i) -
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
          ∫ s in (-r)..r, b s j * test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) :
    ∃ G : M65LocalWeakMap e (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}),
      G.value = value ∧ G.derivative = D := by
  let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let U := ball (0 : LoopPlane) r ∩ {z | 0 < z 1}
  have hUS : U ⊆ S := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  have hweak (test : 𝓢(LoopPlane, ℝ)) (hs : tsupport test ⊆ U) (i : Fin 2) (j : Fin N) :
      (∫ z in U, test z * D i z j) =
        -(∫ z in U, fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (value z) j) := by
    let basis := EuclideanSpace.basisFun (Fin 2) ℝ
    have hcircle (θ : ℝ) : test (r • Proofs.M58.angularPoint θ) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hn := mem_ball_zero_iff.mp (hs hm).1
      rw [norm_smul, Proofs.M58.norm_angularPoint, mul_one,
        Real.norm_eq_abs, abs_of_pos hr] at hn
      exact (lt_irrefl r) hn
    have hdiameter (s : ℝ) : test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hn := (hs hm).2
      change 0 < (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) 1 at hn
      norm_num [EuclideanSpace.basisFun_apply] at hn
    have hg := hgreen test i j
    change (∫ z in S, D i z j * test z + e (value z) j * fderiv ℝ test z (basis i)) = _ at hg
    simp only [hcircle, hdiameter, mul_zero, zero_mul, intervalIntegral.integral_zero,
      sub_zero] at hg
    have hDI : IntegrableOn (fun z => D i z j * test z) S := by
      simpa +instances only [Pi.mul_apply, IntegrableOn, S] using!
        (hd i).eval_piLp j |>.integrable_mul ((test.memLp 2 volume).restrict S)
    have hVI : IntegrableOn (fun z => e (value z) j * fderiv ℝ test z (basis i)) S := by
      simpa +instances only [Pi.mul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
        IntegrableOn, S, basis] using!
        (hu.eval_piLp j).integrable_mul
          (((∂_{basis i} test).memLp 2 volume).restrict S)
    rw [integral_add hDI hVI] at hg
    have hL (T : Set LoopPlane) (hT : tsupport test ⊆ T) :
        (∫ z in T, D i z j * test z) = ∫ z, D i z j * test z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (hT hm)), mul_zero]
    have hV (T : Set LoopPlane) (hT : tsupport test ⊆ T) :
        (∫ z in T, e (value z) j * fderiv ℝ test z (basis i)) =
          ∫ z, e (value z) j * fderiv ℝ test z (basis i) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [fderiv_of_notMem_tsupport ℝ (fun hm => hz (hT hm)), zero_apply, mul_zero]
    rw [hL S (hs.trans hUS), hV S (hs.trans hUS)] at hg
    simp_rw [mul_comm (test _) _, mul_comm (fderiv ℝ test _ _) _]
    rw [hL U hs, hV U hs]
    linarith only [hg]
  refine ⟨{
    value := value
    derivative := D
    value_memLp := fun K _hK hKU => hu.mono_measure
      (Measure.restrict_mono_set volume (hKU.trans hUS))
    derivative_memLp := fun i K _hK hKU => (hd i).mono_measure
      (Measure.restrict_mono_set volume (hKU.trans hUS))
    weak_derivative := fun test _hc hs i j => hweak test hs i j
  }, rfl, rfl⟩




theorem weakDisk_exists_boundary_localMap {M : Type*} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (he : Continuous e) (hγ : Continuous γ)
    (hclosed : IsClosed (range e)) {p : ℂ} (hp : ‖p‖ = 1)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      ∃ G : M65LocalWeakMap e (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}),
        G.value = (fun z => F.value (diskBoundaryCoordinate p z)) ∧
        G.derivative = weakDiskBoundaryField F p := by
  obtain ⟨R0, hR0, hsemicircle⟩ := weakDisk_boundary_semicircle F he hγ hclosed hp
  obtain ⟨R1, hR1, hvalue, hfield⟩ := weakDisk_boundary_memLp F hp
  let R := min R0 (min R1 Rmax)
  have hR : 0 < R := lt_min hR0 (lt_min hR1 hRmax)
  have hRR0 : R ≤ R0 := min_le_left _ _
  have hRR1 : R ≤ R1 := (min_le_right _ _).trans (min_le_left _ _)
  have hRRmax : R ≤ Rmax := (min_le_right _ _).trans (min_le_right _ _)
  have hAE := ae_restrict_of_ae_restrict_of_subset
    (Icc_subset_Icc le_rfl hRR0) (hsemicircle (R / 2) (half_pos hR))
  have hvol : volume (Icc (R / 2) R) ≠ 0 := by
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  obtain ⟨r, hrI, hrG⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol hAE
  have hr : 0 < r := (half_pos hR).trans_le hrI.1
  obtain ⟨_hW, V, _hV, _hVAE, _hTarget, _hV0, _hVπ, _hinc, hgreen⟩ := hrG
  have hsub : closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1} ⊆
      closedBall (0 : LoopPlane) R1 ∩ {z | 0 ≤ z 1} :=
    inter_subset_inter_left _ (closedBall_subset_closedBall (hrI.2.trans hRR1))
  obtain ⟨G, hGv, hGD⟩ := halfDisk_localMap_of_green e
    (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p) hr
    (hvalue.mono_measure (Measure.restrict_mono_set volume hsub))
    (fun i => (hfield i).mono_measure (Measure.restrict_mono_set volume hsub))
    V (fun s => e (γ (F.parameter (boundaryCirclePoint hp s)))) hgreen
  exact ⟨r, hr, hrI.2.trans hRRmax, G, hGv, hGD⟩

end PoincareConjecture.M65Boundary
