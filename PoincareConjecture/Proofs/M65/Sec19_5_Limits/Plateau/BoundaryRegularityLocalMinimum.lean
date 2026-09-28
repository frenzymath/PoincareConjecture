import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityLocalMap
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerDiskLocal











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap ENNReal LineDeriv

universe u

namespace PoincareConjecture.M65Boundary

private theorem push_original_columns {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) {p : ℂ} (hp : ‖p‖ = 1) (z : LoopPlane) (i : Fin 2) :
    boundaryPushField p z (fun k => weakDiskBoundaryField F p k z) i =
      F.derivative i (diskBoundaryCoordinate p z) := by
  have h (k : Fin 2) : weakDiskBoundaryField F p k z =
      ∑ l : Fin 2, (fderiv ℝ (diskBoundaryCoordinate p) z
        (EuclideanSpace.basisFun (Fin 2) ℝ k)) l •
          F.derivative l (diskBoundaryCoordinate p z) := by
    ext j
    simp only [weakDiskBoundaryField, Fin.sum_univ_two,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [h]
  exact boundaryPushField_pull hp z _ i

set_option maxHeartbeats 1800000 in





theorem boundary_zero_green_energy_comparison_uniform
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) :
    ∃ R : ℝ, 0 < R ∧ ∀ {p : ℂ}, ‖p‖ = 1 → ∀ r : ℝ, 0 < r → r ≤ R →
      let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      ∀ (q : LoopPlane → M) (d : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N)),
        MemLp (fun z => e (F.value (P z))) 2 (volume.restrict S) →
        (∀ i, MemLp (weakDiskBoundaryField F p i) 2 (volume.restrict S)) →
        MemLp (fun z => e (q z)) 2 (volume.restrict S) →
        (∀ i, MemLp (d i) 2 (volume.restrict S)) →
        (∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
          (∫ z in S, (d i z j - weakDiskBoundaryField F p i z j) * test z +
            (e (q z) j - e (F.value (P z)) j) *
              fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0) →
        (∫ z in S, m65EmbeddedEnergyDensity g e (fun z => F.value (P z))
          (weakDiskBoundaryField F p) z) ≤ ∫ z in S, m65EmbeddedEnergyDensity g e q d z := by
  classical
  obtain ⟨R, hR, hpush⟩ := exists_boundary_function_pushforward_uniform
  refine ⟨R, hR, ?_⟩
  intro p hp r hr hrR
  dsimp only
  intro q d hOldU hOldD hNewU hNewD hgreen
  let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  let Z := P '' S
  let basis := EuclideanSpace.basisFun (Fin 2) ℝ
  let u := fun z => e (q z) - e (F.value (P z))
  let df := fun i z => d i z - weakDiskBoundaryField F p i z
  obtain ⟨hcap, hleft, hpushr⟩ := hpush hp r hr hrR
  have hS : IsCompact S := (isCompact_closedBall (0 : LoopPlane) r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hZ : IsCompact Z := hS.image (contDiff_diskBoundaryCoordinate p).continuous
  have hright (w : LoopPlane) (hw : w ∈ Z) : P (Q w) = w := by
    obtain ⟨z, hz, rfl⟩ := hw
    dsimp only [P, Q]
    rw [hleft z hz]
  have hu : MemLp u 2 (volume.restrict S) := hNewU.sub hOldU
  have hdf (i : Fin 2) : MemLp (df i) 2 (volume.restrict S) :=
    (hNewD i).sub (hOldD i)
  have hpushed (j : Fin N) := hpushr (fun z => u z j) (fun i z => df i z j)
    (fun _ => 0) (hu.eval_piLp j) (fun i => (hdf i).eval_piLp j)
      (fun test i => by
        simpa only [u, df, PiLp.sub_apply, zero_mul, intervalIntegral.integral_zero,
          mul_zero] using hgreen test i j)
  let delta := fun i w => WithLp.toLp 2 (fun j : Fin N =>
    ∑ k : Fin 2, ((fderiv ℝ P (Q w) (basis k)) i / Real.exp (-(Q w) 1) ^ 2) * df k (Q w) j)
  let D := fun i w => F.derivative i w + delta i w
  let q' := fun w => q (Q w)
  have hOldUZ : MemLp (fun w => e (F.value w)) 2 (volume.restrict Z) :=
    ((Lp.memLp F.embeddedValue).ae_eq F.embeddedValue_ae).mono_measure
      (Measure.restrict_mono_set volume hcap)
  have hUZ : MemLp (fun w => u (Q w)) 2 (volume.restrict Z) :=
    MemLp.of_eval_piLp (fun j => (hpushed j).1)
  have hq : MemLp (fun w => e (q' w)) 2 (volume.restrict Z) := by
    apply (hOldUZ.add hUZ).ae_eq
    filter_upwards [ae_restrict_mem hZ.measurableSet] with w hw
    dsimp only [Pi.add_apply, u, q']
    rw [hright w hw]
    abel
  have hdelta (i : Fin 2) : MemLp (delta i) 2 (volume.restrict Z) :=
    MemLp.of_eval_piLp (fun j => (hpushed j).2.1 i)
  have hD (i : Fin 2) : MemLp (D i) 2 (volume.restrict Z) :=
    ((Lp.memLp (F.derivative i)).mono_measure
      (Measure.restrict_mono_set volume hcap)).add (hdelta i)
  obtain ⟨G, _hparameter, hvalues, hout, hfields⟩ :=
    F.exists_boundary_replacement he.continuous hγ hZ hcap q' D hq hD
      F.parameter F.weakly_monotone (fun test i j => by
        simp only [sub_self, zero_mul, integral_zero]
        calc
          _ = ∫ w in Z, delta i w j * test w +
              u (Q w) j * fderiv ℝ test w (basis i) := by
            apply setIntegral_congr_fun hZ.measurableSet
            intro w hw
            simp only [D, q', u, PiLp.add_apply, PiLp.sub_apply, hright w hw]
            ring
          _ = 0 := by
            simpa only [zero_mul, intervalIntegral.integral_zero] using (hpushed j).2.2 test i)
  refine boundary_replacement_energy_le g he hinj hemb compact F G hmin hp hS hleft hcap
    q d hvalues ?_ hout ?_
  · intro i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hcap (hfields i),
      ae_restrict_mem hZ.measurableSet] with w hw hwZ
    rw [piecewise_eq_of_mem Z _ _ hwZ] at hw
    rw [hw]
    have hdiff : delta i w =
        boundaryPushField p (Q w) (fun k => d k (Q w)) i -
          boundaryPushField p (Q w) (fun k => weakDiskBoundaryField F p k (Q w)) i := by
      ext j
      simp only [delta, df, boundaryPushField, Fin.sum_univ_two, PiLp.add_apply,
        PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, P, basis]
      ring
    change F.derivative i w + delta i w = _
    rw [hdiff, push_original_columns F hp,
      show diskBoundaryCoordinate p (Q w) = w from hright w hwZ]
    abel
  · intro i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset (hfields i),
      ae_restrict_mem (measurableSet_closedBall.diff hZ.measurableSet)] with w hw hm
    exact hw.trans (piecewise_eq_of_notMem _ _ _ hm.2)

open Classical in
private theorem replacement_memLp {E : Type*} [NormedAddCommGroup E]
    {Z S : Set LoopPlane} (hZ : MeasurableSet Z) {f g : LoopPlane → E}
    (hf : MemLp f 2 (volume.restrict Z)) (hg : MemLp g 2 (volume.restrict S)) :
    MemLp (Z.piecewise f g) 2 (volume.restrict S) := by
  classical
  apply MemLp.piecewise hZ _ (hg.restrict Zᶜ)
  apply hf.mono_measure
  rw [Measure.restrict_restrict hZ]
  exact Measure.restrict_mono_set volume inter_subset_left

set_option maxHeartbeats 1800000 in





theorem boundary_localMap_minimizes_uniform
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) :
    ∃ R : ℝ, 0 < R ∧ ∀ {p : ℂ}, ‖p‖ = 1 → ∀ r : ℝ, 0 < r → r ≤ R →
      let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let U := ball (0 : LoopPlane) r ∩ {z | 0 < z 1}
      ∀ X : M65LocalWeakMap e U,
        X.value = (fun z => F.value (diskBoundaryCoordinate p z)) →
        X.derivative = weakDiskBoundaryField F p →
        MemLp (fun z => e (X.value z)) 2 (volume.restrict S) →
        (∀ i, MemLp (X.derivative i) 2 (volume.restrict S)) →
        M65LocallyMinimizesEnergy g X := by
  classical
  obtain ⟨R, hR, hcompare⟩ :=
    boundary_zero_green_energy_comparison_uniform g he hinj hemb compact hγ F hmin
  refine ⟨R, hR, ?_⟩
  intro p hp r hr hrR
  dsimp only
  intro X hXvalue hXfield hOldU hOldD x s hs hsU G hmatch
  let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let U := ball (0 : LoopPlane) r ∩ {z | 0 < z 1}
  let Z := closedBall x s
  let q := Z.piecewise G.value X.value
  let d := fun i => Z.piecewise (G.derivative i) (X.derivative i)
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hS : IsCompact S := (isCompact_closedBall (0 : LoopPlane) r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hZ : IsCompact Z := isCompact_closedBall x s
  have hZS : Z ⊆ S := fun z hz =>
    ⟨ball_subset_closedBall (hsU hz).1, (show 0 < z 1 from (hsU hz).2).le⟩
  have hNewU : MemLp (fun z => e (q z)) 2 (volume.restrict S) := by
    have hpiece := replacement_memLp hZ.measurableSet (G.value_memLp Z hZ hsU) hOldU
    apply hpiece.ae_eq
    filter_upwards with z
    by_cases hz : z ∈ Z
    · simp only [q, piecewise_eq_of_mem Z _ _ hz]
    · simp only [q, piecewise_eq_of_notMem Z _ _ hz]
  have hNewD (i : Fin 2) : MemLp (d i) 2 (volume.restrict S) :=
    replacement_memLp hZ.measurableSet (G.derivative_memLp i Z hZ hsU) (hOldD i)
  have hgreen (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N) :
      (∫ z in S, (d i z j - X.derivative i z j) * test z +
        (e (q z) j - e (X.value z) j) *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
    let diff := fun z => (d i z j - X.derivative i z j) * test z +
      (e (q z) j - e (X.value z) j) *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)
    have heq : (∫ z in S, diff z) = ∫ z in Z, diff z :=
      setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hS.measurableSet.nullMeasurableSet hZS
        (Filter.Eventually.of_forall fun z hz => by
          simp only [diff, d, q, piecewise_eq_of_notMem Z _ _ hz.2,
            sub_self, zero_mul, add_zero])
    change (∫ z in S, diff z) = 0
    rw [heq]
    calc
      _ = ∫ z in Z, (G.derivative i z j - X.derivative i z j) * test z +
          (e (G.value z) j - e (X.value z) j) *
            fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
        apply setIntegral_congr_fun hZ.measurableSet
        intro z hz
        simp only [diff, d, q, piecewise_eq_of_mem Z _ _ hz]
      _ = 0 := M65Euler.compact_disk_green_difference hU X G x hs.le hsU hmatch test i j
  have hcomparison := hcompare hp r hr hrR q d
    (by simpa only [hXvalue] using hOldU)
    (by simpa only [hXfield] using hOldD) hNewU hNewD
    (by simpa only [hXvalue, hXfield] using hgreen)
  let original := m65EmbeddedEnergyDensity g e X.value X.derivative
  let replacement := m65EmbeddedEnergyDensity g e G.value G.derivative
  let changed := m65EmbeddedEnergyDensity g e q d
  have hFint : IntegrableOn original S :=
    m65EmbeddedEnergyDensity_integrable g e he hinj hemb compact hOldU.1 hOldD
  have hGint : IntegrableOn replacement Z := G.energy_integrable g he hinj hemb compact Z hZ hsU
  have hpiece : changed = Z.piecewise replacement original := by
    funext z
    by_cases hz : z ∈ Z <;>
      simp [changed, replacement, original, q, d, m65EmbeddedEnergyDensity, hz]
  have hsplit : (∫ z in S, changed z) =
      (∫ z in Z, replacement z) + (∫ z in S, original z) - ∫ z in Z, original z := by
    rw [hpiece]
    have hh := integral_piecewise (μ := volume.restrict S) hZ.measurableSet
      (hGint.restrict (t := S)) (hFint.integrableOn (s := Zᶜ))
    rw [Measure.restrict_restrict_of_subset hZS, Measure.restrict_restrict hZ.measurableSet.compl,
      inter_comm Zᶜ S, ← Set.sdiff_eq S Z,
      setIntegral_sdiff hZ.measurableSet hFint hZS] at hh
    rw [hh]
    ring
  change (∫ z in Z, original z) ≤ ∫ z in Z, replacement z
  have hcomp : (∫ z in S, original z) ≤ ∫ z in S, changed z := by
    simpa only [original, changed, hXvalue, hXfield] using hcomparison
  rw [hsplit] at hcomp
  linarith only [hcomp]





theorem weakDisk_exists_boundary_localMinimum
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g)
    {p : ℂ} (hp : ‖p‖ = 1) {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      ∃ X : M65LocalWeakMap e (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}),
        X.value = (fun z => F.value (diskBoundaryCoordinate p z)) ∧
        X.derivative = weakDiskBoundaryField F p ∧ M65LocallyMinimizesEnergy g X := by
  obtain ⟨R0, hR0, hlocal⟩ :=
    boundary_localMap_minimizes_uniform g he hinj hemb compact hγ F hmin
  obtain ⟨R1, hR1, hvalue, hfield⟩ := weakDisk_boundary_memLp F hp
  have hclosed : IsClosed (range e) := by
    simpa only [image_univ] using (compact.image he.continuous).isClosed
  obtain ⟨R, hR, hRR, X, hXv, hXD⟩ := weakDisk_exists_boundary_localMap
    F he.continuous hγ hclosed hp (lt_min hR0 (lt_min hR1 hRmax))
  have hRR0 : R ≤ R0 := hRR.trans (min_le_left _ _)
  have hRR1 : R ≤ R1 := (hRR.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hRRmax : R ≤ Rmax := (hRR.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsub : closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1} ⊆
      closedBall (0 : LoopPlane) R1 ∩ {z | 0 ≤ z 1} :=
    inter_subset_inter_left _ (closedBall_subset_closedBall hRR1)
  refine ⟨R, hR, hRRmax, X, hXv, hXD, hlocal hp R hR hRR0 X hXv hXD ?_ ?_⟩
  · simpa only [hXv] using hvalue.mono_measure (Measure.restrict_mono_set volume hsub)
  · intro i
    simpa only [hXD] using (hfield i).mono_measure (Measure.restrict_mono_set volume hsub)

end PoincareConjecture.M65Boundary
