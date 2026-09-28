import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHalfConeCompetitor










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareConjecture.M65Boundary

open M65Interior



def boundaryPushField {N : ℕ} (p : ℂ) (z : LoopPlane)
    (d : Fin 2 → EuclideanSpace ℝ (Fin N)) (i : Fin 2) : EuclideanSpace ℝ (Fin N) :=
  ∑ k : Fin 2, ((fderiv ℝ (diskBoundaryCoordinate p) z
    (EuclideanSpace.basisFun (Fin 2) ℝ k)) i / Real.exp (-z 1) ^ 2) • d k

private theorem boundary_norm_square {p : ℂ} (hp : ‖p‖ = 1) (z : LoopPlane) :
    (diskBoundaryCoordinate p z 0) ^ 2 + (diskBoundaryCoordinate p z 1) ^ 2 =
      Real.exp (-z 1) ^ 2 := by
  have hh : ‖diskBoundaryCoordinate p z‖ ^ 2 =
      (diskBoundaryCoordinate p z 0) ^ 2 + (diskBoundaryCoordinate p z 1) ^ 2 := by
    simpa only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using
      EuclideanSpace.norm_sq_eq (diskBoundaryCoordinate p z)
  rw [norm_diskBoundaryCoordinate hp] at hh
  exact hh.symm




theorem boundaryPushField_pull {N : ℕ} {p : ℂ} (hp : ‖p‖ = 1)
    (z : LoopPlane) (d : Fin 2 → EuclideanSpace ℝ (Fin N)) (i : Fin 2) :
    boundaryPushField p z (fun k => ∑ l : Fin 2,
      (fderiv ℝ (diskBoundaryCoordinate p) z
        (EuclideanSpace.basisFun (Fin 2) ℝ k)) l • d l) i = d i := by
  have hJ : Real.exp (-z 1) ^ 2 ≠ 0 := pow_ne_zero _ (Real.exp_ne_zero _)
  obtain ⟨h0, h1⟩ := diskBoundaryCoordinate_columns p z
  have hn := boundary_norm_square hp z
  ext j
  fin_cases i <;>
    simp only [boundaryPushField, Fin.sum_univ_two, h0, h1, PiLp.add_apply,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] <;>
    norm_num [EuclideanSpace.basisFun_apply] <;>
    field_simp <;> rw [← hn] <;> ring





theorem boundaryPushField_energy {N : ℕ} {p : ℂ} (hp : ‖p‖ = 1)
    (z : LoopPlane)
    (H : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (d : Fin 2 → EuclideanSpace ℝ (Fin N)) :
    Real.exp (-z 1) ^ 2 * ((1 / 2 : ℝ) * ∑ i : Fin 2,
      H (boundaryPushField p z d i) (boundaryPushField p z d i)) =
        (1 / 2 : ℝ) * ∑ i : Fin 2, H (d i) (d i) := by
  have hJ : Real.exp (-z 1) ^ 2 ≠ 0 := pow_ne_zero _ (Real.exp_ne_zero _)
  obtain ⟨h0, h1⟩ := diskBoundaryCoordinate_columns p z
  have hn := boundary_norm_square hp z
  simp only [boundaryPushField, Fin.sum_univ_two, h0, h1, PiLp.add_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  norm_num [EuclideanSpace.basisFun_apply]
  field_simp
  rw [← hn]
  ring




theorem weakDiskBoundaryField_energy {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    {γ : LoopCircle → M} (F : M65WeakDisk e γ) {p : ℂ} (hp : ‖p‖ = 1)
    (z : LoopPlane) :
    m65EmbeddedEnergyDensity g e (fun z => F.value (diskBoundaryCoordinate p z))
      (weakDiskBoundaryField F p) z =
        Real.exp (-z 1) ^ 2 * m65EmbeddedEnergyDensity g e F.value
          (fun i w => F.derivative i w) (diskBoundaryCoordinate p z) := by
  let d (i : Fin 2) := F.derivative i (diskBoundaryCoordinate p z)
  let D (k : Fin 2) := ∑ l : Fin 2,
    (fderiv ℝ (diskBoundaryCoordinate p) z
      (EuclideanSpace.basisFun (Fin 2) ℝ k)) l • d l
  have hD (k : Fin 2) : weakDiskBoundaryField F p k z = D k := by
    ext j
    simp only [weakDiskBoundaryField, D, d, Fin.sum_univ_two,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have h := boundaryPushField_energy hp z
    (m65EmbeddingMetric g e (F.value (diskBoundaryCoordinate p z))) D
  simp only [D, boundaryPushField_pull hp] at h
  simpa only [m65EmbeddedEnergyDensity, hD, d] using h.symm

open Classical in




theorem weakDisk_replacement_energy_le {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (F G : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g)
    {Z : Set LoopPlane} (hZ : MeasurableSet Z) (hZD : Z ⊆ loopDiskSet)
    (hout : ∀ z ∉ Z, G.value z = F.value z)
    (hfields : ∀ i, ∀ᵐ z ∂volume.restrict (loopDiskSet \ Z),
      G.derivative i z = F.derivative i z) :
    (∫ z in Z, m65EmbeddedEnergyDensity g e F.value (fun i w => F.derivative i w) z) ≤
      ∫ z in Z, m65EmbeddedEnergyDensity g e G.value (fun i w => G.derivative i w) z := by
  classical
  let EF := m65EmbeddedEnergyDensity g e F.value (fun i w => F.derivative i w)
  let EG := m65EmbeddedEnergyDensity g e G.value (fun i w => G.derivative i w)
  have hF : IntegrableOn EF loopDiskSet := F.energy_integrable g he hinj hemb compact
  have hG : IntegrableOn EG loopDiskSet := G.energy_integrable g he hinj hemb compact
  have houtside : (∫ z in loopDiskSet \ Z, EG z) = ∫ z in loopDiskSet \ Z, EF z := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hfields,
      ae_restrict_mem (measurableSet_closedBall.diff hZ)] with z hz hm
    simp only [EG, EF, m65EmbeddedEnergyDensity, hout z hm.2, hz]
  have hcomparison := hmin G
  change (∫ z in loopDiskSet, EF z) ≤ ∫ z in loopDiskSet, EG z at hcomparison
  have hFs := setIntegral_sdiff hZ hF hZD
  have hGs := setIntegral_sdiff hZ hG hZD
  change (∫ z in Z, EF z) ≤ ∫ z in Z, EG z
  linarith only [hcomparison, houtside, hFs, hGs]





theorem boundary_replacement_energy_le {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (F G : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g)
    {p : ℂ} (hp : ‖p‖ = 1) {S : Set LoopPlane} (hS : IsCompact S)
    (hleft : ∀ z ∈ S, diskBoundaryInverse p (diskBoundaryCoordinate p z) = z)
    (hcap : diskBoundaryCoordinate p '' S ⊆ loopDiskSet)
    (q : LoopPlane → M) (d : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (hvalues : ∀ z ∈ diskBoundaryCoordinate p '' S,
      G.value z = q (diskBoundaryInverse p z))
    (hinside : ∀ i, ∀ᵐ w ∂volume.restrict (diskBoundaryCoordinate p '' S),
      G.derivative i w = boundaryPushField p (diskBoundaryInverse p w)
        (fun k => d k (diskBoundaryInverse p w)) i)
    (hout : ∀ z ∉ diskBoundaryCoordinate p '' S, G.value z = F.value z)
    (hfields : ∀ i, ∀ᵐ z ∂volume.restrict (loopDiskSet \ (diskBoundaryCoordinate p '' S)),
      G.derivative i z = F.derivative i z) :
    (∫ z in S, m65EmbeddedEnergyDensity g e (fun z => F.value (diskBoundaryCoordinate p z))
      (weakDiskBoundaryField F p) z) ≤ ∫ z in S, m65EmbeddedEnergyDensity g e q d z := by
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  let Z := P '' S
  let EF := m65EmbeddedEnergyDensity g e F.value (fun i w => F.derivative i w)
  let EG := m65EmbeddedEnergyDensity g e G.value (fun i w => G.derivative i w)
  let EQ := fun w => m65EmbeddedEnergyDensity g e (fun w => q (Q w))
    (fun i w => boundaryPushField p (Q w) (fun k => d k (Q w)) i) w
  have hP := contDiff_diskBoundaryCoordinate p
  have hZ : IsCompact Z := hS.image hP.continuous
  have hinjective : InjOn P S := fun x hx y hy hxy => by
    have hh := congrArg Q hxy
    dsimp only [Q, P] at hh
    rwa [hleft x hx, hleft y hy] at hh
  have hchange (f : LoopPlane → ℝ) :
      (∫ z in S, Real.exp (-z 1) ^ 2 * f (P z)) = ∫ w in Z, f w := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume hS.measurableSet
      (fun z _ => (hP.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt) hinjective f
    simpa only [diskBoundaryCoordinate_det hp, abs_sq, smul_eq_mul, P, Z]
      using h.symm
  have hGQ : (∫ w in Z, EG w) = ∫ w in Z, EQ w := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hinside, ae_restrict_mem hZ.measurableSet] with w hw hm
    simp only [EG, EQ, m65EmbeddedEnergyDensity, hvalues w hm, hw, Q]
  have hGE : (∫ w in Z, EG w) = ∫ z in S, m65EmbeddedEnergyDensity g e q d z := by
    rw [hGQ, ← hchange EQ]
    apply setIntegral_congr_fun hS.measurableSet
    intro z hz
    dsimp only [EQ, P, Q, m65EmbeddedEnergyDensity]
    rw [hleft z hz]
    exact boundaryPushField_energy hp z (m65EmbeddingMetric g e (q z)) (fun i => d i z)
  have hFE : (∫ w in Z, EF w) =
      ∫ z in S, m65EmbeddedEnergyDensity g e (fun z => F.value (P z))
        (weakDiskBoundaryField F p) z := by
    rw [← hchange EF]
    apply setIntegral_congr_fun hS.measurableSet
    intro z _
    exact (weakDiskBoundaryField_energy g F hp z).symm
  have h := weakDisk_replacement_energy_le g he hinj hemb compact F G hmin
    hZ.measurableSet hcap hout hfields
  rwa [hGE, hFE] at h

private theorem boundaryPushField_weak {M : Type*} {N : ℕ}
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

set_option maxHeartbeats 1200000 in





theorem exists_boundary_half_cone_energy_comparison_uniform
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi ∧ ∀ {p : ℂ} (hp : ‖p‖ = 1),
      ∀ r : ℝ, 0 < r → r ≤ R →
      let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
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
        (∫ z in S, m65EmbeddedEnergyDensity g e (fun z => F.value (P z))
          (weakDiskBoundaryField F p) z) ≤
            ∫ z in S, m65EmbeddedEnergyDensity g e (coneDiskMap A r m v 0)
              (coneDiskField (e ∘ A) r m v d 0) z := by
  classical
  obtain ⟨R0, hR0, hRπ, hcone⟩ := exists_boundary_half_cone_competitor_uniform he.continuous hγ
  obtain ⟨R1, hR1, hpush⟩ := exists_boundary_function_pushforward_uniform
  refine ⟨min R0 R1, lt_min hR0 hR1, (min_le_left _ _).trans_lt hRπ, ?_⟩
  intro p hp r hr hrR
  dsimp only
  intro A v d ρ C hρ hC hv hg hvb hd hinc hD hOldU hOldD B hB hmatch hdiam hGreen
  obtain ⟨hcap, hleft, _⟩ := hpush hp r hr (hrR.trans (min_le_right _ _))
  obtain ⟨G, _, hvalues, hout, hfields⟩ :=
    hcone F hp r hr (hrR.trans (min_le_left _ _)) A v d ρ C hρ hC hv hg hvb hd hinc hD
      hOldU hOldD B hB hmatch hdiam hGreen
  let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  let P := diskBoundaryCoordinate p
  let Q := diskBoundaryInverse p
  let Z := P '' S
  let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
  let q := coneDiskMap A r m v 0
  let field := coneDiskField (e ∘ A) r m v d 0
  have hS : IsCompact S := (isCompact_closedBall (0 : LoopPlane) r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hZ : IsCompact Z := hS.image (contDiff_diskBoundaryCoordinate p).continuous
  have hright (w : LoopPlane) (hw : w ∈ Z) : P (Q w) = w := by
    obtain ⟨z, hz, rfl⟩ := hw
    dsimp only [P, Q]
    rw [hleft z hz]
  refine boundary_replacement_energy_le g he hinj hemb compact F G hmin hp hS hleft hcap
    q field hvalues ?_ hout ?_
  · intro i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hcap (hfields i),
      ae_restrict_mem hZ.measurableSet] with w hw hwZ
    rw [piecewise_eq_of_mem Z _ _ hwZ] at hw
    rw [hw]
    have hdiff : WithLp.toLp 2 (fun j : Fin N => ∑ k : Fin 2,
        ((fderiv ℝ P (Q w) (EuclideanSpace.basisFun (Fin 2) ℝ k)) i /
          Real.exp (-(Q w) 1) ^ 2) *
            (field k (Q w) j - weakDiskBoundaryField F p k (Q w) j)) =
      boundaryPushField p (Q w) (fun k => field k (Q w)) i -
        boundaryPushField p (Q w) (fun k => weakDiskBoundaryField F p k (Q w)) i := by
      ext j
      simp only [boundaryPushField, Fin.sum_univ_two, PiLp.add_apply,
        PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, P]
      ring
    change F.derivative i w + _ = boundaryPushField p (Q w) (fun k => field k (Q w)) i
    rw [hdiff, boundaryPushField_weak F hp, show diskBoundaryCoordinate p (Q w) = w from
      hright w hwZ]
    abel
  · intro i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset (hfields i),
      ae_restrict_mem (measurableSet_closedBall.diff hZ.measurableSet)] with w hw hm
    exact hw.trans (piecewise_eq_of_notMem _ _ _ hm.2)



theorem exists_boundary_half_cone_energy_comparison
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
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
        (∫ z in S, m65EmbeddedEnergyDensity g e (fun z => F.value (P z))
          (weakDiskBoundaryField F p) z) ≤
            ∫ z in S, m65EmbeddedEnergyDensity g e (coneDiskMap A r m v 0)
              (coneDiskField (e ∘ A) r m v d 0) z := by
  obtain ⟨R, hR, hRπ, h⟩ :=
    exists_boundary_half_cone_energy_comparison_uniform g he hinj hemb compact hγ F hmin
  exact ⟨R, hR, hRπ, h hp⟩

end PoincareConjecture.M65Boundary
