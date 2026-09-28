import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityCircleGreen
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHalfConeReplacement
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityPushforward
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeakReplacement
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeVectorGreen











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap ENNReal LineDeriv

namespace PoincareConjecture.M65Boundary

open M65Interior M65StrictTrace

private theorem inverse_ae {E : Type*} {p : ℂ} {K : Set LoopPlane}
    (hK : IsCompact K)
    (hleft : ∀ z ∈ K, diskBoundaryInverse p (diskBoundaryCoordinate p z) = z)
    {f g : LoopPlane → E} (hfg : f =ᵐ[volume.restrict K] g) :
    (fun w => f (diskBoundaryInverse p w)) =ᵐ[
      volume.restrict (diskBoundaryCoordinate p '' K)]
        fun w => g (diskBoundaryInverse p w) := by
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  have hP := contDiff_diskBoundaryCoordinate p
  have hZ : IsCompact (P '' K) := hK.image hP.continuous
  have hnull : volume ({z | f z ≠ g z} ∩ K) = 0 := by
    rw [← Measure.restrict_apply' hK.measurableSet]
    exact hfg
  have himage : volume (P '' ({z | f z ≠ g z} ∩ K)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hP.differentiable (by simp)).differentiableOn hnull
  change (volume.restrict (P '' K)) {w | f (Q w) ≠ g (Q w)} = 0
  rw [Measure.restrict_apply' hZ.measurableSet]
  apply measure_mono_null _ himage
  rintro w ⟨hw, z, hz, rfl⟩
  exact ⟨z, ⟨by simpa only [mem_ofPred_eq, Q, P, hleft z hz] using hw, hz⟩, rfl⟩

private theorem inverse_function_memLp {p : ℂ} (hp : ‖p‖ = 1)
    {K : Set LoopPlane} (hK : IsCompact K)
    (hleft : ∀ z ∈ K, diskBoundaryInverse p (diskBoundaryCoordinate p z) = z)
    {u : LoopPlane → ℝ} (hu : MemLp u 2 (volume.restrict K)) :
    MemLp (fun w => u (diskBoundaryInverse p w)) 2
      (volume.restrict (diskBoundaryCoordinate p '' K)) := by
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  have hP := contDiff_diskBoundaryCoordinate p
  have hinj : InjOn P K := fun x hx y hy hxy => by
    have h := congrArg Q hxy
    dsimp only [Q, P] at h
    rwa [hleft x hx, hleft y hy] at h
  have hJ : ContinuousOn (fun z : LoopPlane => Real.exp (-z 1) ^ 2) K := by fun_prop
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have transfer (v : LoopPlane → ℝ) (hv : IntegrableOn v K) :
      IntegrableOn (fun w => v (Q w)) (P '' K) := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hK.measurableSet
      (fun z _ => (hP.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt) hinj _).mpr
    apply (IntegrableOn.continuousOn_mul hJ hv hK).congr
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    dsimp only [Q]
    rw [diskBoundaryCoordinate_det hp, abs_of_nonneg (sq_nonneg _), hleft z hz]
    rfl
  exact (memLp_two_iff_integrable_sq
    (transfer u (hu.integrable (by norm_num : (1 : ENNReal) ≤ 2))).1).mpr
      (transfer (fun z => u z ^ 2) hu.integrable_sq)






theorem exists_boundary_function_pushforward_uniform :
    ∃ R : ℝ, 0 < R ∧ ∀ {p : ℂ}, ‖p‖ = 1 → ∀ r : ℝ, 0 < r → r ≤ R →
      let K := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      let Q := diskBoundaryInverse p
      P '' K ⊆ loopDiskSet ∧
      (∀ z ∈ K, Q (P z) = z) ∧
      ∀ (u : LoopPlane → ℝ) (d : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ),
        MemLp u 2 (volume.restrict K) →
        (∀ i, MemLp (d i) 2 (volume.restrict K)) →
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
  obtain ⟨R, hR, hpush⟩ := exists_boundary_halfDisk_pushforward_uniform
  refine ⟨R, hR, ?_⟩
  intro p hp r hr hrR
  obtain ⟨hcap, hleft, hpushr⟩ := hpush hp r hr hrR
  refine ⟨hcap, hleft, ?_⟩
  intro u d b hu hd hgreen
  let K := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  let U := hu.toLp u
  let V (i : Fin 2) := (hd i).toLp (d i)
  have hU : U =ᵐ[volume.restrict K] u := hu.coeFn_toLp
  have hV (i : Fin 2) : V i =ᵐ[volume.restrict K] d i := (hd i).coeFn_toLp
  have hclass (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) :
      (∫ z in K, V i z * test z + U z * fderiv ℝ test z (e i)) =
        -(e 1) i * ∫ s in (-r)..r, b s * test (s • e 0) := by
    rw [← hgreen test i]
    apply integral_congr_ae
    filter_upwards [hU, hV i] with z hz hd'
    rw [hz, hd']
  obtain ⟨huZ, hdZ, hZgreen⟩ := hpushr U V b hclass
  have hUQ := inverse_ae hK hleft hU
  have hVQ (i : Fin 2) := inverse_ae hK hleft (hV i)
  let D := fun i w => ∑ k : Fin 2,
    ((fderiv ℝ P (Q w) (e k)) i / Real.exp (-(Q w) 1) ^ 2) * d k (Q w)
  have hD (i : Fin 2) : (fun w => ∑ k : Fin 2,
      ((fderiv ℝ P (Q w) (e k)) i / Real.exp (-(Q w) 1) ^ 2) * V k (Q w))
        =ᵐ[volume.restrict (P '' K)] D i := by
    filter_upwards [ae_all_iff.mpr hVQ] with w hw
    simp only [D, Q, hw]
  refine ⟨huZ.ae_eq hUQ, fun i => (hdZ i).ae_eq (hD i), ?_⟩
  intro test i
  rw [← hZgreen test i]
  apply integral_congr_ae
  filter_upwards [hUQ, hD i] with w hu' hd'
  rw [hu', hd']



theorem exists_boundary_function_pushforward {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      let K := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      let Q := diskBoundaryInverse p
      P '' K ⊆ loopDiskSet ∧
      (∀ z ∈ K, Q (P z) = z) ∧
      ∀ (u : LoopPlane → ℝ) (d : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ),
        MemLp u 2 (volume.restrict K) →
        (∀ i, MemLp (d i) 2 (volume.restrict K)) →
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
  obtain ⟨R, hR, h⟩ := exists_boundary_function_pushforward_uniform
  exact ⟨R, hR, h hp⟩

private theorem midpoint_mem {ρ : ℝ} {a b : LoopAmbient}
    (ha : a ∈ closedBall 0 ρ) (hb : b ∈ closedBall 0 ρ) :
    (1 / 2 : ℝ) • (a + b) ∈ closedBall 0 ρ := by
  simpa only [smul_add] using (convex_closedBall (0 : LoopAmbient) ρ) ha hb
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)

private theorem midpoint_halfCone_green_clm {N : ℕ}
    {g : LoopAmbient → EuclideanSpace ℝ (Fin N)}
    {v d : ℝ → LoopAmbient} {r ρ C : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hv : AbsolutelyContinuousOnInterval v 0 Real.pi)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      v t - v s = ∫ θ in s..t, d θ)
    (hD : ∀ y ∈ closedBall (0 : LoopAmbient) ρ, ‖fderiv ℝ g y‖ ≤ C)
    (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) (j : Fin N) :
    let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
    (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
      coneDiskField g r m v d 0 i z j * test z + coneDiskMap g r m v 0 z j *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      r * (∫ θ in (0 : ℝ)..Real.pi,
        g (v θ) j * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i) -
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
        ∫ s in (-r)..r, g (halfConeDiameter r (v 0) (v Real.pi) s) j *
          test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  let L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := EuclideanSpace.proj j
  let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
  have h0 : m ∈ closedBall 0 ρ := midpoint_mem
    (hvb ⟨le_rfl, Real.pi_pos.le⟩) (hvb ⟨Real.pi_pos.le, le_rfl⟩)
  have hDL (y : LoopAmbient) (hy : y ∈ closedBall 0 ρ) :
      ‖fderiv ℝ (L ∘ g) y‖ ≤ ‖L‖ * C := by
    have hym : y ∈ ball (0 : LoopAmbient) (2 * ρ) :=
      (closedBall_subset_ball (by linarith)) hy
    have hgd := (hg.contDiffAt (isOpen_ball.mem_nhds hym)).differentiableAt one_ne_zero
    rw [(L.hasFDerivAt.comp y hgd.hasFDerivAt).fderiv]
    exact (L.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hD y hy) (norm_nonneg L))
  have h := (midpoint_halfCone_green hr hρ (mul_nonneg (norm_nonneg L) hC) hv
    (L.contDiff.comp_contDiffOn hg) hvb hd hinc hDL test ht i).2
  calc
    _ = ∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        coneDiskField (L ∘ g) r m v d 0 i z * test z +
          coneDiskMap (L ∘ g) r m v 0 z *
            fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
      apply setIntegral_congr_fun (measurableSet_closedBall.inter
        (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet)
      intro z hz
      have hz' : z ∈ closedBall (0 : LoopPlane) r ∩ {z | (0 : LoopPlane) 1 ≤ z 1} := hz
      rw [← polarCoordinates_preimage_halfRectangle] at hz'
      have hm := coneCoordinates_mem_closedBall hr h0 (hvb hz'.2) hz'.1
      have hgd := (hg.contDiffAt (isOpen_ball.mem_nhds
        ((closedBall_subset_ball (by linarith : ρ < 2 * ρ)) hm))).differentiableAt one_ne_zero
      simp only [coneDiskField, coneCartesianField_clm L r m v d _ _ i hgd,
        coneDiskMap, Function.comp_apply]
      rfl
    _ = _ := h

private theorem halfDisk_green_integrable {N : ℕ} {K : Set LoopPlane}
    {u d : LoopPlane → EuclideanSpace ℝ (Fin N)}
    (hu : MemLp u 2 (volume.restrict K)) (hd : MemLp d 2 (volume.restrict K))
    (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N) :
    IntegrableOn (fun z => d z j * test z +
      u z j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) K := by
  have h1 := (hd.eval_piLp j).integrable_mul ((test.memLp 2 volume).restrict K)
  have h2 := (hu.eval_piLp j).integrable_mul
    (((∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test).memLp 2 volume).restrict K)
  simpa +instances only [Pi.add_apply, Pi.mul_apply, IntegrableOn,
    SchwartzMap.lineDerivOp_apply_eq_fderiv] using! h1.add h2

set_option maxHeartbeats 1800000 in

open Classical in






theorem exists_boundary_half_cone_competitor_uniform
    {M : Type*} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (he : Continuous e) (hγ : Continuous γ) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi ∧
      ∀ (F : M65WeakDisk e γ) {p : ℂ} (hp : ‖p‖ = 1), ∀ r : ℝ, 0 < r → r ≤ R →
      let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      let Q := diskBoundaryInverse p
      ∀ (A : LoopAmbient → M) (v d : ℝ → LoopAmbient) (ρ C : ℝ),
        0 < ρ → 0 ≤ C →
        AbsolutelyContinuousOnInterval v 0 Real.pi →
        ContDiffOn ℝ 1 (e ∘ A) (ball 0 (2 * ρ)) →
        MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ) →
        MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) →
        (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          v t - v s = ∫ θ in s..t, d θ) →
        (∀ y ∈ closedBall (0 : LoopAmbient) ρ, ‖fderiv ℝ (e ∘ A) y‖ ≤ C) →
        MemLp (fun z => e (F.value (P z))) 2 (volume.restrict S) →
        (∀ i, MemLp (weakDiskBoundaryField F p i) 2 (volume.restrict S)) →
        ∀ B : C(LoopCircle, LoopCircle), M65WeakCircleParameter B →
        (∀ z ∉ boundaryCirclePoint hp '' Icc (-r) r, B z = F.parameter z) →
        (∀ s ∈ Icc (-r) r,
          A (halfConeDiameter r (v 0) (v Real.pi) s) = γ (B (boundaryCirclePoint hp s))) →
        (∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
          (∫ z in S, weakDiskBoundaryField F p i z j * test z +
            e (F.value (P z)) j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
            r * (∫ θ in (0 : ℝ)..Real.pi,
              e (A (v θ)) j * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i) -
            (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
              ∫ s in (-r)..r, e (γ (F.parameter (boundaryCirclePoint hp s))) j *
                test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) →
        let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
        let q := fun w => coneDiskMap A r m v 0 (Q w)
        let D := fun i w => F.derivative i w + WithLp.toLp 2 (fun j =>
          ∑ k : Fin 2, ((fderiv ℝ P (Q w) (EuclideanSpace.basisFun (Fin 2) ℝ k)) i /
            Real.exp (-(Q w) 1) ^ 2) *
              (coneDiskField (e ∘ A) r m v d 0 k (Q w) j -
                weakDiskBoundaryField F p k (Q w) j))
        ∃ G : M65WeakDisk e γ, G.parameter = B ∧
          (∀ z ∈ P '' S, G.value z = q z) ∧
          (∀ z ∉ P '' S, G.value z = F.value z) ∧
          ∀ i, G.derivative i =ᵐ[volume.restrict loopDiskSet]
            (P '' S).piecewise (D i) (fun z => F.derivative i z) := by
  classical
  obtain ⟨R0, hR0, hpush⟩ := exists_boundary_function_pushforward_uniform
  let R := min R0 (Real.pi / 2)
  have hR : 0 < R := lt_min hR0 (half_pos Real.pi_pos)
  have hRπ : R < Real.pi := (min_le_right _ _).trans_lt (half_lt_self Real.pi_pos)
  refine ⟨R, hR, hRπ, ?_⟩
  intro F p hp r hr hrR
  dsimp only
  intro A v d ρ C hρ hC hv hg hvb hd hinc hD hOldU hOldD B hB hmatch hdiam hOldGreen
  let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
  let newValue := coneDiskMap A r m v 0
  let newField := coneDiskField (e ∘ A) r m v d 0
  let u := fun z => e (newValue z) - e (F.value (P z))
  let df := fun i z => newField i z - weakDiskBoundaryField F p i z
  let b := fun s => e (A (halfConeDiameter r (v 0) (v Real.pi) s)) -
    e (γ (F.parameter (boundaryCirclePoint hp s)))
  let Z := P '' S
  let basis := EuclideanSpace.basisFun (Fin 2) ℝ
  obtain ⟨hcap, hleft, hpushr⟩ := hpush hp r hr (hrR.trans (min_le_left _ _))
  have hS : IsCompact S := (isCompact_closedBall (0 : LoopPlane) r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hZ : IsCompact Z := hS.image (contDiff_diskBoundaryCoordinate p).continuous
  have hright (w : LoopPlane) (hw : w ∈ Z) : P (Q w) = w := by
    obtain ⟨z, hz, rfl⟩ := hw
    dsimp only [P, Q]
    rw [hleft z hz]
  have h0 : m ∈ closedBall 0 ρ := midpoint_mem
    (hvb ⟨le_rfl, Real.pi_pos.le⟩) (hvb ⟨Real.pi_pos.le, le_rfl⟩)
  have hvc : ContinuousOn v (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hv.continuousOn
  have hCone := halfCone_memLp hr hρ hC hvc hg h0 hvb hd hD (0 : LoopPlane)
  have hConeU : MemLp (fun z => e (newValue z)) 2 (volume.restrict S) := hCone.1
  have hConeD (i : Fin 2) : MemLp (newField i) 2 (volume.restrict S) := hCone.2 i
  have hu : MemLp u 2 (volume.restrict S) := hConeU.sub hOldU
  have hdf (i : Fin 2) : MemLp (df i) 2 (volume.restrict S) := (hConeD i).sub (hOldD i)
  have hbcont : ContinuousOn b (Icc (-r) r) := by
    have hn : EqOn (fun s => e (A (halfConeDiameter r (v 0) (v Real.pi) s)))
        (fun s => e (γ (B (boundaryCirclePoint hp s)))) (Icc (-r) r) :=
      fun s hs => congrArg e (hdiam s hs)
    have hc : Continuous (boundaryCirclePoint hp) :=
      (((contDiff_diskBoundaryCoordinate p).continuous.comp
        (continuous_id.smul continuous_const)).subtype_mk _)
    exact (((he.comp (hγ.comp B.continuous)).comp hc).continuousOn.congr hn).sub
      (((he.comp (hγ.comp F.parameter.continuous)).comp hc).continuousOn)
  have hgreen (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N) :
      (∫ z in S, df i z j * test z + u z j * fderiv ℝ test z (basis i)) =
        -(basis 1) i * ∫ s in (-r)..r, b s j * test (s • basis 0) := by
    have hnew := midpoint_halfCone_green_clm hr hρ hC hv hg hvb hd hinc hD
      test (test.smooth 1) i j
    change (∫ z in S, newField i z j * test z +
      e (newValue z) j * fderiv ℝ test z (basis i)) =
        r * (∫ θ in (0 : ℝ)..Real.pi,
          e (A (v θ)) j * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i) -
        (basis 1) i * ∫ s in (-r)..r,
          e (A (halfConeDiameter r (v 0) (v Real.pi) s)) j * test (s • basis 0) at hnew
    have hnewI := halfDisk_green_integrable hConeU (hConeD i) test i j
    have holdI := halfDisk_green_integrable hOldU (hOldD i) test i j
    have heq : (fun z => df i z j * test z + u z j * fderiv ℝ test z (basis i)) =
        fun z => (newField i z j * test z + e (newValue z) j * fderiv ℝ test z (basis i)) -
          (weakDiskBoundaryField F p i z j * test z +
            e (F.value (P z)) j * fderiv ℝ test z (basis i)) := by
      funext z
      simp only [df, u, PiLp.sub_apply]
      ring
    rw [heq, integral_sub hnewI holdI, hnew, hOldGreen test i j]
    have hc : Continuous (boundaryCirclePoint hp) :=
      (((contDiff_diskBoundaryCoordinate p).continuous.comp
        (continuous_id.smul continuous_const)).subtype_mk _)
    have holdB : Continuous (fun s => e (γ (F.parameter (boundaryCirclePoint hp s))) j *
        test (s • basis 0)) :=
      ((EuclideanSpace.proj j).continuous.comp (he.comp (hγ.comp
        (F.parameter.continuous.comp hc)))).mul
          (test.continuous.comp (continuous_id.smul continuous_const))
    have hbI : IntervalIntegrable (fun s => b s j * test (s • basis 0)) volume (-r) r :=
      (ContinuousOn.mul
        ((EuclideanSpace.proj j).continuous.comp_continuousOn hbcont)
        (test.continuous.comp (continuous_id.smul continuous_const)).continuousOn
        ).intervalIntegrable_of_Icc (by linarith)
    have hsplit : (∫ s in (-r)..r,
        e (A (halfConeDiameter r (v 0) (v Real.pi) s)) j * test (s • basis 0)) =
          (∫ s in (-r)..r, b s j * test (s • basis 0)) +
            ∫ s in (-r)..r, e (γ (F.parameter (boundaryCirclePoint hp s))) j *
              test (s • basis 0) := by
      rw [← intervalIntegral.integral_add hbI (holdB.intervalIntegrable _ _)]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [b, PiLp.sub_apply]
      ring
    rw [hsplit]
    ring
  have hpushed (j : Fin N) := hpushr (fun z => u z j) (fun i z => df i z j)
    (fun s => b s j) (hu.eval_piLp j) (fun i => (hdf i).eval_piLp j)
      (fun test i => hgreen test i j)
  let delta := fun i w => WithLp.toLp 2 (fun j : Fin N =>
    ∑ k : Fin 2, ((fderiv ℝ P (Q w) (basis k)) i / Real.exp (-(Q w) 1) ^ 2) * df k (Q w) j)
  let D := fun i w => F.derivative i w + delta i w
  let q := fun w => newValue (Q w)
  have hq : MemLp (fun w => e (q w)) 2 (volume.restrict Z) :=
    MemLp.of_eval_piLp (fun j => inverse_function_memLp hp hS hleft (hConeU.eval_piLp j))
  have hdelta (i : Fin 2) : MemLp (delta i) 2 (volume.restrict Z) :=
    MemLp.of_eval_piLp (fun j => (hpushed j).2.1 i)
  have hDL (i : Fin 2) : MemLp (D i) 2 (volume.restrict Z) :=
    ((Lp.memLp (F.derivative i)).mono_measure
      (Measure.restrict_mono_set volume hcap)).add (hdelta i)
  apply F.exists_boundary_replacement he hγ hZ hcap q D hq hDL B hB
  intro test i j
  have hArc := boundaryCirclePoint_eq_puncturedArc hp
  let puncture : LoopCircle := ⟨-Complex.orthonormalBasisOneI.repr p, by
    rw [norm_neg, LinearIsometryEquiv.norm_map, hp]⟩
  have hArc' (s : ℝ) : boundaryCirclePoint hp s = puncturedArc puncture s := hArc s
  have hmatch' (z : LoopCircle) (hz : z ∉ puncturedArc puncture '' Icc (-r) r) :
      B z = F.parameter z := by
    apply hmatch z
    simpa only [show boundaryCirclePoint hp = puncturedArc puncture from funext hArc] using hz
  have hcircle := boundary_replacement_green_integral e γ puncture (hrR.trans_lt hRπ)
    F.parameter B hmatch' test i j
  have heq : (∫ t in Icc (-Real.pi) Real.pi,
      (e (γ (B (m65LoopAngular t))) j - e (γ (F.parameter (m65LoopAngular t))) j) *
        m65DiskBoundaryTest test i t) =
      ∫ s in (-r)..r, b s j * test (P (s • basis 0)) * P (s • basis 0) i := by
    rw [intervalIntegral.integral_of_le (by linarith : -r ≤ r),
      ← integral_Icc_eq_integral_Ioc]
    calc
      _ = ∫ s in Icc (-r) r,
          (e (γ (B (puncturedArc puncture s))) j -
            e (γ (F.parameter (puncturedArc puncture s))) j) *
              test (puncturedArc puncture s) * (puncturedArc puncture s : LoopPlane) i := by
        simpa only [m65DiskBoundaryTest, m65LoopAngular, mul_assoc] using hcircle
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro s hs
        dsimp only
        rw [← hArc' s, ← hdiam s hs]
        rfl
  calc
    _ = ∫ w in Z, delta i w j * test w +
        u (Q w) j * fderiv ℝ test w (basis i) := by
      apply setIntegral_congr_fun hZ.measurableSet
      intro w hw
      simp only [D, q, u, PiLp.add_apply, PiLp.sub_apply, hright w hw]
      ring
    _ = ∫ s in (-r)..r, b s j * test (P (s • basis 0)) * P (s • basis 0) i :=
      (hpushed j).2.2 test i
    _ = _ := heq.symm

open Classical in


theorem exists_boundary_half_cone_competitor
    {M : Type*} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (he : Continuous e) (hγ : Continuous γ)
    {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      let Q := diskBoundaryInverse p
      ∀ (A : LoopAmbient → M) (v d : ℝ → LoopAmbient) (ρ C : ℝ),
        0 < ρ → 0 ≤ C →
        AbsolutelyContinuousOnInterval v 0 Real.pi →
        ContDiffOn ℝ 1 (e ∘ A) (ball 0 (2 * ρ)) →
        MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ) →
        MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) →
        (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          v t - v s = ∫ θ in s..t, d θ) →
        (∀ y ∈ closedBall (0 : LoopAmbient) ρ, ‖fderiv ℝ (e ∘ A) y‖ ≤ C) →
        MemLp (fun z => e (F.value (P z))) 2 (volume.restrict S) →
        (∀ i, MemLp (weakDiskBoundaryField F p i) 2 (volume.restrict S)) →
        ∀ B : C(LoopCircle, LoopCircle), M65WeakCircleParameter B →
        (∀ z ∉ boundaryCirclePoint hp '' Icc (-r) r, B z = F.parameter z) →
        (∀ s ∈ Icc (-r) r,
          A (halfConeDiameter r (v 0) (v Real.pi) s) = γ (B (boundaryCirclePoint hp s))) →
        (∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
          (∫ z in S, weakDiskBoundaryField F p i z j * test z +
            e (F.value (P z)) j * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
            r * (∫ θ in (0 : ℝ)..Real.pi,
              e (A (v θ)) j * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i) -
            (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
              ∫ s in (-r)..r, e (γ (F.parameter (boundaryCirclePoint hp s))) j *
                test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) →
        let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
        let q := fun w => coneDiskMap A r m v 0 (Q w)
        let D := fun i w => F.derivative i w + WithLp.toLp 2 (fun j =>
          ∑ k : Fin 2, ((fderiv ℝ P (Q w) (EuclideanSpace.basisFun (Fin 2) ℝ k)) i /
            Real.exp (-(Q w) 1) ^ 2) *
              (coneDiskField (e ∘ A) r m v d 0 k (Q w) j -
                weakDiskBoundaryField F p k (Q w) j))
        ∃ G : M65WeakDisk e γ, G.parameter = B ∧
          (∀ z ∈ P '' S, G.value z = q z) ∧
          (∀ z ∉ P '' S, G.value z = F.value z) ∧
          ∀ i, G.derivative i =ᵐ[volume.restrict loopDiskSet]
            (P '' S).piecewise (D i) (fun z => F.derivative i z) := by
  obtain ⟨R, hR, hRπ, h⟩ := exists_boundary_half_cone_competitor_uniform he hγ
  exact ⟨R, hR, hRπ, h F hp⟩

end PoincareConjecture.M65Boundary
