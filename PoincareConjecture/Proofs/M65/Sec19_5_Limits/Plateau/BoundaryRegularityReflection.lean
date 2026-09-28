import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityLocalMinimum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology SchwartzMap ENNReal LineDeriv

namespace PoincareConjecture.M65Boundary

def boundaryPlaneReflection : LoopPlane ≃ₗᵢ[ℝ] LoopPlane :=
  Complex.orthonormalBasisOneI.repr.symm.trans
    (Complex.conjLIE.trans Complex.orthonormalBasisOneI.repr)

theorem reflection_coordinates (z : LoopPlane) :
    boundaryPlaneReflection z 0 = z 0 ∧ boundaryPlaneReflection z 1 = -z 1 := by
  simp [boundaryPlaneReflection, Complex.orthonormalBasisOneI_repr_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply]

theorem reflection_involution (z : LoopPlane) :
    boundaryPlaneReflection (boundaryPlaneReflection z) = z := by
  ext i
  fin_cases i
  · change boundaryPlaneReflection (boundaryPlaneReflection z) 0 = z 0
    rw [(reflection_coordinates _).1, (reflection_coordinates _).1]
  · change boundaryPlaneReflection (boundaryPlaneReflection z) 1 = z 1
    rw [(reflection_coordinates _).2, (reflection_coordinates _).2, neg_neg]

private theorem diameter_null : volume {z : LoopPlane | z 1 = 0} = 0 := by
  let L : LoopPlane →L[ℝ] ℝ := EuclideanSpace.proj 1
  change volume (LinearMap.ker L.toLinearMap : Set LoopPlane) = 0
  apply Measure.addHaar_submodule
  intro htop
  have hm : EuclideanSpace.basisFun (Fin 2) ℝ 1 ∈
      LinearMap.ker L.toLinearMap := by rw [htop]; trivial
  norm_num [L, LinearMap.mem_ker, EuclideanSpace.basisFun_apply] at hm

private theorem reflection_preimage_halfDisk (r : ℝ) :
    boundaryPlaneReflection ⁻¹' (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) =
      closedBall (0 : LoopPlane) r ∩ {z | z 1 ≤ 0} := by
  ext z
  simp only [mem_preimage, mem_inter_iff, mem_closedBall_zero_iff, mem_ofPred_eq,
    LinearIsometryEquiv.norm_map, (reflection_coordinates _).2, neg_nonneg]

theorem halfDisk_even_memLp {E : Type*} [NormedAddCommGroup E]
    {f : LoopPlane → E} {r : ℝ}
    (hf : MemLp f 2 (volume.restrict
      (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}))) :
    MemLp (fun z => if 0 ≤ z 1 then f z else f (boundaryPlaneReflection z)) 2
      (volume.restrict (closedBall (0 : LoopPlane) r)) := by
  classical
  let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let H : Set LoopPlane := {z | 0 ≤ z 1}
  have hH : MeasurableSet H :=
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hupper : MemLp f 2 ((volume.restrict (closedBall (0 : LoopPlane) r)).restrict H) := by
    simpa only [Measure.restrict_restrict hH, inter_comm, H] using hf
  have hreflected := hf.comp_measurePreserving
    (boundaryPlaneReflection.measurePreserving.restrict_preimage_emb
      boundaryPlaneReflection.toHomeomorph.measurableEmbedding S)
  have hlower : MemLp (fun z => f (boundaryPlaneReflection z)) 2
      ((volume.restrict (closedBall (0 : LoopPlane) r)).restrict Hᶜ) := by
    rw [Measure.restrict_restrict hH.compl]
    apply hreflected.mono_measure
    apply Measure.restrict_mono_set volume
    rw [reflection_preimage_halfDisk]
    exact fun z hz => ⟨hz.2, (lt_of_not_ge (show ¬0 ≤ z 1 from hz.1)).le⟩
  exact MemLp.piecewise hH hupper hlower

private theorem halfDisk_integral_split {r : ℝ} {f : LoopPlane → ℝ}
    (hf : IntegrableOn f (closedBall (0 : LoopPlane) r)) :
    (∫ z in closedBall (0 : LoopPlane) r, f z) =
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}, f z) +
      ∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        f (boundaryPlaneReflection z) := by
  let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let T := boundaryPlaneReflection ⁻¹' S
  have hS : MeasurableSet S := measurableSet_closedBall.inter
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hT : MeasurableSet T := hS.preimage boundaryPlaneReflection.continuous.measurable
  have hunion : S ∪ T = closedBall (0 : LoopPlane) r := by
    dsimp only [T, S]
    rw [reflection_preimage_halfDisk]
    ext z
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hz
      rcases le_total 0 (z 1) with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  have hnull : volume (S ∩ T) = 0 := by
    apply measure_mono_null _ diameter_null
    intro z hz
    have hzT : z ∈ closedBall (0 : LoopPlane) r ∩ {z | z 1 ≤ 0} := by
      simpa only [T, S, reflection_preimage_halfDisk] using hz.2
    have ht : z 1 ≤ 0 := hzT.2
    exact le_antisymm ht hz.1.2
  have hST : AEDisjoint volume S T := hnull
  have hsum := setIntegral_union₀ hST hT.nullMeasurableSet
    (hf.mono_set (by rw [← hunion]; exact subset_union_left))
    (hf.mono_set (by rw [← hunion]; exact subset_union_right))
  rw [hunion] at hsum
  rw [hsum]
  congr 1
  have hchange := boundaryPlaneReflection.measurePreserving.setIntegral_preimage_emb
    boundaryPlaneReflection.toHomeomorph.measurableEmbedding
    (fun z => f (boundaryPlaneReflection z)) S
  simpa only [Function.comp_def, reflection_involution] using hchange

private theorem reflection_basis (i : Fin 2) :
    boundaryPlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      (if i = 0 then (1 : ℝ) else -1) • EuclideanSpace.basisFun (Fin 2) ℝ i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [boundaryPlaneReflection, Complex.orthonormalBasisOneI_repr_apply,
      EuclideanSpace.basisFun_apply]

set_option maxHeartbeats 1800000 in

theorem halfDisk_reflected_localMap_of_green {M : Type*} {N : ℕ}
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
    ∃ X : M65LocalWeakMap e (ball (0 : LoopPlane) r),
      (∀ z, X.value z = if 0 ≤ z 1 then value z else value (boundaryPlaneReflection z)) ∧
      ∀ i z, X.derivative i z = if 0 ≤ z 1 then D i z else
        (if i = 0 then (1 : ℝ) else -1) • D i (boundaryPlaneReflection z) := by
  classical
  let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let B := closedBall (0 : LoopPlane) r
  let U := ball (0 : LoopPlane) r
  let H : Set LoopPlane := {z | 0 ≤ z 1}
  let q := fun z => if 0 ≤ z 1 then value z else value (boundaryPlaneReflection z)
  let sig := fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1
  let d := fun i z => if 0 ≤ z 1 then D i z else sig i • D i (boundaryPlaneReflection z)
  let basis := EuclideanSpace.basisFun (Fin 2) ℝ
  have hH : MeasurableSet H :=
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hS : MeasurableSet S := measurableSet_closedBall.inter hH
  have hq : MemLp (fun z => e (q z)) 2 (volume.restrict B) := by
    apply (halfDisk_even_memLp hu).ae_eq
    filter_upwards with z
    by_cases hz : 0 ≤ z 1 <;> simp [q, hz]
  have hD (i : Fin 2) : MemLp (d i) 2 (volume.restrict B) := by
    have hev := halfDisk_even_memLp (hd i)
    have hp := MemLp.piecewise hH (hev.restrict H) ((hev.const_smul (sig i)).restrict Hᶜ)
    apply hp.ae_eq
    filter_upwards with z
    by_cases hz : 0 ≤ z 1 <;> simp [d, H, hz]
  have hweak (test : 𝓢(LoopPlane, ℝ)) (hs : tsupport test ⊆ U) (i : Fin 2) (j : Fin N) :
      (∫ z in U, test z * d i z j) =
        -(∫ z in U, fderiv ℝ test z (basis i) * e (q z) j) := by
    let psi : 𝓢(LoopPlane, ℝ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      boundaryPlaneReflection.toContinuousLinearEquiv test
    have hpsi (z : LoopPlane) : psi z = test (boundaryPlaneReflection z) := rfl
    have hpsid (z : LoopPlane) : fderiv ℝ psi z (basis i) =
        sig i * fderiv ℝ test (boundaryPlaneReflection z) (basis i) := by
      have hh := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (basis i))
        ((test.differentiableAt.hasFDerivAt.comp z
          boundaryPlaneReflection.toContinuousLinearEquiv.hasFDerivAt).fderiv)
      change fderiv ℝ psi z (basis i) =
        fderiv ℝ test (boundaryPlaneReflection z) (boundaryPlaneReflection (basis i)) at hh
      rw [show boundaryPlaneReflection (basis i) = sig i • basis i from reflection_basis i,
        map_smul, smul_eq_mul] at hh
      exact hh
    have hcircle (z : LoopPlane) (hz : ‖z‖ = r) : test z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hlt := mem_ball_zero_iff.mp (hs hm)
      rw [hz] at hlt
      exact (lt_irrefl r) hlt
    have hnorm (θ : ℝ) : ‖r • Proofs.M58.angularPoint θ‖ = r := by
      rw [norm_smul, Proofs.M58.norm_angularPoint, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    have hcircle0 (θ : ℝ) : test (r • Proofs.M58.angularPoint θ) = 0 :=
      hcircle _ (hnorm θ)
    have hcircle1 (θ : ℝ) : psi (r • Proofs.M58.angularPoint θ) = 0 :=
      hcircle _ ((boundaryPlaneReflection.norm_map _).trans (hnorm θ))
    have hdiameter (s : ℝ) : psi (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
      rw [hpsi, map_smul]
      rw [show boundaryPlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
          EuclideanSpace.basisFun (Fin 2) ℝ 0 from by
        simpa only [ite_true, one_smul] using reflection_basis 0]
    have hDI : IntegrableOn (fun z => d i z j * test z) B := by
      simpa +instances only [Pi.mul_apply, IntegrableOn, B] using!
        (hD i).eval_piLp j |>.integrable_mul ((test.memLp 2 volume).restrict B)
    have hVI : IntegrableOn (fun z => e (q z) j * fderiv ℝ test z (basis i)) B := by
      simpa +instances only [Pi.mul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
        IntegrableOn, B] using!
        (hq.eval_piLp j).integrable_mul (((∂_{basis i} test).memLp 2 volume).restrict B)
    let f := fun z => d i z j * test z + e (q z) j * fderiv ℝ test z (basis i)
    have hsplit := halfDisk_integral_split (hDI.add hVI)
    change (∫ z in B, f z) = (∫ z in S, f z) +
      ∫ z in S, f (boundaryPlaneReflection z) at hsplit
    have hupper : (∫ z in S, f z) =
        ∫ z in S, D i z j * test z + e (value z) j * fderiv ℝ test z (basis i) := by
      apply setIntegral_congr_fun hS
      intro z hz
      have hzp : 0 ≤ z 1 := hz.2
      simp only [f, d, q, hzp, if_true]
    have hlower : (∫ z in S, f (boundaryPlaneReflection z)) =
        sig i * ∫ z in S, D i z j * psi z + e (value z) j * fderiv ℝ psi z (basis i) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      have hne : ∀ᵐ z : LoopPlane, z 1 ≠ 0 := by
        rw [ae_iff]
        simpa only [not_not] using diameter_null
      filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hne] with z hz hn
      have hzpos : 0 < z 1 := lt_of_le_of_ne hz.2 (Ne.symm hn)
      have hneg : ¬0 ≤ boundaryPlaneReflection z 1 := by
        rw [(reflection_coordinates z).2]
        linarith
      dsimp only [f, d, q]
      rw [if_neg hneg, if_neg hneg, reflection_involution, PiLp.smul_apply,
        smul_eq_mul, hpsi, hpsid]
      fin_cases i <;> norm_num [sig]
      ring
    have hg0 := hgreen test i j
    have hg1 := hgreen psi i j
    change (∫ z in S, D i z j * test z + e (value z) j * fderiv ℝ test z (basis i)) = _ at hg0
    change (∫ z in S, D i z j * psi z + e (value z) j * fderiv ℝ psi z (basis i)) = _ at hg1
    simp only [hcircle0, hcircle1, mul_zero, zero_mul, intervalIntegral.integral_zero,
      zero_sub, hdiameter] at hg0 hg1
    have hzero : (∫ z in B, f z) = 0 := by
      rw [hsplit, hupper, hlower, hg0, hg1]
      fin_cases i <;> norm_num [sig, EuclideanSpace.basisFun_apply]
    change (∫ z in B, d i z j * test z + e (q z) j *
      fderiv ℝ test z (basis i)) = 0 at hzero
    rw [integral_add hDI hVI] at hzero
    have hL (T : Set LoopPlane) (hT : tsupport test ⊆ T) :
        (∫ z in T, d i z j * test z) = ∫ z, d i z j * test z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun hm => hz (hT hm)), mul_zero]
    have hV (T : Set LoopPlane) (hT : tsupport test ⊆ T) :
        (∫ z in T, e (q z) j * fderiv ℝ test z (basis i)) =
          ∫ z, e (q z) j * fderiv ℝ test z (basis i) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [fderiv_of_notMem_tsupport ℝ (fun hm => hz (hT hm)), zero_apply, mul_zero]
    rw [hL B (hs.trans ball_subset_closedBall), hV B (hs.trans ball_subset_closedBall)] at hzero
    simp_rw [mul_comm (test _) _, mul_comm (fderiv ℝ test _ _) _]
    rw [hL U hs, hV U hs]
    linarith only [hzero]
  exact ⟨{
    value := q
    derivative := d
    value_memLp := fun K _hK hKU => hq.mono_measure
      (Measure.restrict_mono_set volume (hKU.trans ball_subset_closedBall))
    derivative_memLp := fun i K _hK hKU => (hD i).mono_measure
      (Measure.restrict_mono_set volume (hKU.trans ball_subset_closedBall))
    weak_derivative := fun test _hc hs i j => hweak test hs i j
  }, fun _ => rfl, fun _ _ => rfl⟩

open scoped ContDiff Manifold in

theorem weakDisk_exists_boundary_reflected_minimum
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g)
    {p : ℂ} (hp : ‖p‖ = 1) {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      ∃ (X : M65LocalWeakMap e (ball (0 : LoopPlane) R))
        (Y : M65LocalWeakMap e (ball (0 : LoopPlane) R ∩ {z | 0 < z 1})),
        (∀ z, X.value z = if 0 ≤ z 1 then F.value (diskBoundaryCoordinate p z)
          else F.value (diskBoundaryCoordinate p (boundaryPlaneReflection z))) ∧
        (∀ i z, X.derivative i z = if 0 ≤ z 1 then weakDiskBoundaryField F p i z else
          (if i = 0 then (1 : ℝ) else -1) •
            weakDiskBoundaryField F p i (boundaryPlaneReflection z)) ∧
        Y.value = (fun z => F.value (diskBoundaryCoordinate p z)) ∧
        Y.derivative = weakDiskBoundaryField F p ∧ M65LocallyMinimizesEnergy g Y := by
  have hclosed : IsClosed (range e) := by
    simpa only [image_univ] using (compact.image he.continuous).isClosed
  obtain ⟨R0, hR0, hsemicircle⟩ := weakDisk_boundary_semicircle F he.continuous hγ hclosed hp
  obtain ⟨R1, hR1, hvalue, hfield⟩ := weakDisk_boundary_memLp F hp
  obtain ⟨R2, hR2, hlocal⟩ :=
    boundary_localMap_minimizes_uniform g he hinj hemb compact hγ F hmin
  let A := min R0 (min R1 (min R2 Rmax))
  have hA : 0 < A := lt_min hR0 (lt_min hR1 (lt_min hR2 hRmax))
  have hA0 : A ≤ R0 := min_le_left _ _
  have hA1 : A ≤ R1 := (min_le_right _ _).trans (min_le_left _ _)
  have hA2 : A ≤ R2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hAM : A ≤ Rmax := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hAE := ae_restrict_of_ae_restrict_of_subset
    (Icc_subset_Icc le_rfl hA0) (hsemicircle (A / 2) (half_pos hA))
  have hvol : volume (Icc (A / 2) A) ≠ 0 := by
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  obtain ⟨R, hRI, hRG⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol hAE
  have hR : 0 < R := (half_pos hA).trans_le hRI.1
  obtain ⟨_hW, V, _hV, _hVAE, _hTarget, _hV0, _hVπ, _hinc, hgreen⟩ := hRG
  have hsub : closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1} ⊆
      closedBall (0 : LoopPlane) R1 ∩ {z | 0 ≤ z 1} :=
    inter_subset_inter_left _ (closedBall_subset_closedBall (hRI.2.trans hA1))
  have hu := hvalue.mono_measure (Measure.restrict_mono_set volume hsub)
  have hd (i : Fin 2) := (hfield i).mono_measure (Measure.restrict_mono_set volume hsub)
  obtain ⟨X, hXv, hXd⟩ := halfDisk_reflected_localMap_of_green e
    (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p) hR hu hd
    V (fun s => e (γ (F.parameter (boundaryCirclePoint hp s)))) hgreen
  obtain ⟨Y, hYv, hYd⟩ := halfDisk_localMap_of_green e
    (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p) hR hu hd
    V (fun s => e (γ (F.parameter (boundaryCirclePoint hp s)))) hgreen
  refine ⟨R, hR, hRI.2.trans hAM, X, Y, hXv, hXd, hYv, hYd,
    hlocal hp R hR (hRI.2.trans hA2) Y hYv hYd ?_ ?_⟩
  · simpa only [hYv] using hu
  · simpa only [hYd] using hd

end PoincareConjecture.M65Boundary
