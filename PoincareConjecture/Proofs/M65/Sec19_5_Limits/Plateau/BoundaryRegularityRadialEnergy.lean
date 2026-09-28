import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityCapturedCone
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityRadialIntegral
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPowerDecay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold ENNReal

universe u

namespace PoincareConjecture.M65Boundary

open M65Interior

theorem weakDisk_boundary_memLp_uniform {M : Type u} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M} :
    ∃ R : ℝ, 0 < R ∧ ∀ (F : M65WeakDisk e γ) {p : ℂ}, ‖p‖ = 1 →
      let S := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
      MemLp (fun z => e (F.value (diskBoundaryCoordinate p z))) 2 (volume.restrict S) ∧
        ∀ i, MemLp (weakDiskBoundaryField F p i) 2 (volume.restrict S) := by
  obtain ⟨R, hR, hgeometry⟩ := exists_uniform_boundary_halfDisk_pullback
  refine ⟨R, hR, ?_⟩
  intro F p hp
  obtain ⟨_hleft, _hcap, _hreg, C, hC, hdom⟩ := hgeometry p hp
  let S := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
  let P := diskBoundaryCoordinate p
  have hS : IsCompact S := (isCompact_closedBall (0 : LoopPlane) R).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hP := contDiff_diskBoundaryCoordinate p
  have hpull {v : LoopPlane → EuclideanSpace ℝ (Fin N)}
      (hv : MemLp v 2 (volume.restrict loopDiskSet)) :
      MemLp (fun z => v (P z)) 2 (volume.restrict S) :=
    (hv.of_measure_le_smul hC hdom).comp_of_map hP.continuous.measurable.aemeasurable
  refine ⟨hpull ((Lp.memLp F.embeddedValue).ae_eq F.embeddedValue_ae), ?_⟩
  intro i
  let a (k : Fin 2) (z : LoopPlane) :=
    (fderiv ℝ P z (EuclideanSpace.basisFun (Fin 2) ℝ i)) k
  have ha (k : Fin 2) : Continuous (a k) :=
    (EuclideanSpace.proj k).continuous.comp
      ((hP.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hterm (k : Fin 2) : MemLp (fun z => a k z • F.derivative k (P z))
      2 (volume.restrict S) := by
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (ha k).continuousOn
    have hd := hpull (Lp.memLp (F.derivative k))
    apply hd.of_le_mul (c := B) ((ha k).aestronglyMeasurable.smul hd.1)
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    change ‖a k z • F.derivative k (P z)‖ ≤ B * ‖F.derivative k (P z)‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hB z hz) (norm_nonneg _)
  have hsum := (hterm 0).add (hterm 1)
  convert hsum using 1
  funext z
  ext j
  simp only [weakDiskBoundaryField, Fin.sum_univ_two, Pi.add_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, a, P]

theorem weakDisk_boundary_memLp {M : Type u} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R : ℝ, 0 < R ∧
      let S := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
      MemLp (fun z => e (F.value (diskBoundaryCoordinate p z))) 2 (volume.restrict S) ∧
        ∀ i, MemLp (weakDiskBoundaryField F p i) 2 (volume.restrict S) := by
  obtain ⟨R, hR, h⟩ := weakDisk_boundary_memLp_uniform (e := e) (γ := γ)
  exact ⟨R, hR, h F hp⟩

theorem weakDisk_boundary_energy_le {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e q))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (F : M65WeakDisk e γ) {p : ℂ} (hp : ‖p‖ = 1)
    {S : Set LoopPlane} (hS : IsCompact S)
    (hleft : ∀ z ∈ S, diskBoundaryInverse p (diskBoundaryCoordinate p z) = z)
    (hcap : diskBoundaryCoordinate p '' S ⊆ loopDiskSet) :
    (∫ z in S, m65EmbeddedEnergyDensity g e
      (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p) z) ≤
        F.energy g := by
  let P := diskBoundaryCoordinate p
  let E := m65EmbeddedEnergyDensity g e F.value (fun i z => F.derivative i z)
  have hP := contDiff_diskBoundaryCoordinate p
  have hPinj : InjOn P S := fun x hx y hy hxy => by
    have h := congrArg (diskBoundaryInverse p) hxy
    change diskBoundaryInverse p (diskBoundaryCoordinate p x) =
      diskBoundaryInverse p (diskBoundaryCoordinate p y) at h
    rwa [hleft x hx, hleft y hy] at h
  have hchange : (∫ z in S, m65EmbeddedEnergyDensity g e
      (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p) z) =
      ∫ z in P '' S, E z := by
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS.measurableSet
      (fun z _ => (hP.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt) hPinj]
    apply setIntegral_congr_fun hS.measurableSet
    intro z _
    dsimp only
    rw [weakDiskBoundaryField_energy g F hp, diskBoundaryCoordinate_det hp,
      abs_of_nonneg (sq_nonneg _)]
    rfl
  rw [hchange]
  exact setIntegral_mono_set (F.energy_integrable g he hinj hemb compact)
    (ae_of_all _ fun z => embeddedEnergyDensity_nonneg g e F.value
      (fun i z => F.derivative i z) z) (ae_of_all _ fun _ hz => hcap hz)

theorem local_halfDisk_radial {f : LoopPlane → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : IntegrableOn f (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1})) :
    AbsolutelyContinuousOnInterval
      (fun s => ∫ z in closedBall (0 : LoopPlane) s ∩ {z | 0 ≤ z 1}, f z) 0 R ∧
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      IntegrableOn (fun θ => f (r • Proofs.M58.angularPoint θ)) (Icc (0 : ℝ) Real.pi) ∧
      HasDerivAt
        (fun s => ∫ z in closedBall (0 : LoopPlane) s ∩ {z | 0 ≤ z 1}, f z)
        (r * ∫ θ in Icc (0 : ℝ) Real.pi, f (r • Proofs.M58.angularPoint θ)) r := by
  classical
  let H : Set LoopPlane := {z | 0 ≤ z 1}
  let g := H.indicator f
  have hH : MeasurableSet H :=
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hg : IntegrableOn g (closedBall (0 : LoopPlane) R) := by
    rw [IntegrableOn, integrable_indicator_iff hH, IntegrableOn, Measure.restrict_restrict hH,
      inter_comm]
    exact hf
  have heq : (fun s => ∫ z in closedBall (0 : LoopPlane) s, g z) =
      fun s => ∫ z in closedBall (0 : LoopPlane) s ∩ H, f z := by
    funext s
    dsimp only [g]
    rw [integral_indicator hH, Measure.restrict_restrict hH, inter_comm]
  obtain ⟨hac, hrad⟩ := local_disk_radial hR hg
  rw [heq] at hac hrad
  refine ⟨hac, ?_⟩
  filter_upwards [hrad, ae_restrict_mem measurableSet_Ioo] with r hr hrR
  have hpolar (θ : ℝ) : polarPlane 0 (r, θ) = r • Proofs.M58.angularPoint θ := by
    simp only [polarPlane, zero_add]
  have hmem (θ : ℝ) (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
      r • Proofs.M58.angularPoint θ ∈ H ↔ 0 ≤ θ := by
    change 0 ≤ (r • Proofs.M58.angularPoint θ) 1 ↔ 0 ≤ θ
    simp only [PiLp.smul_apply, smul_eq_mul, Proofs.M58.angularPoint,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_nonneg_iff_of_pos_left hrR.1]
    constructor
    · intro hs
      by_contra hn
      exact (Real.sin_neg_of_neg_of_neg_pi_lt (lt_of_not_ge hn) hθ.1).not_ge hs
    · intro hs
      exact Real.sin_nonneg_of_nonneg_of_le_pi hs hθ.2.le
  have hgi : IntegrableOn (fun θ => f (r • Proofs.M58.angularPoint θ))
      (Ioo (0 : ℝ) Real.pi) := by
    apply (hr.1.mono_set (Ioo_subset_Ioo (by linarith [Real.pi_pos]) le_rfl)).congr_fun
      _ measurableSet_Ioo
    intro θ hθ
    dsimp only
    rw [hpolar]
    exact indicator_of_mem ((hmem θ ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).mpr hθ.1.le) f
  have hμ : volume.restrict (Ioo (0 : ℝ) Real.pi) =
      volume.restrict (Icc (0 : ℝ) Real.pi) := Measure.restrict_congr_set Ioo_ae_eq_Icc
  have hint : (∫ θ in Ioo (-Real.pi) Real.pi, g (polarPlane 0 (r, θ))) =
      ∫ θ in Icc (0 : ℝ) Real.pi, f (r • Proofs.M58.angularPoint θ) := by
    calc
      _ = ∫ θ in Ioo (-Real.pi) Real.pi,
          (Ici (0 : ℝ)).indicator (fun θ => f (r • Proofs.M58.angularPoint θ)) θ := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro θ hθ
        dsimp only
        rw [hpolar]
        by_cases h : 0 ≤ θ
        · dsimp only [g]
          rw [indicator_of_mem ((hmem θ hθ).mpr h), indicator_of_mem (show θ ∈ Ici 0 from h)]
        · dsimp only [g]
          rw [indicator_of_notMem (mt (hmem θ hθ).mp h),
            indicator_of_notMem (show θ ∉ Ici 0 from h)]
      _ = ∫ θ in Ico (0 : ℝ) Real.pi, f (r • Proofs.M58.angularPoint θ) := by
        have hs : Ici (0 : ℝ) ∩ Ioo (-Real.pi) Real.pi = Ico (0 : ℝ) Real.pi := by
          ext θ
          simp only [mem_inter_iff, mem_Ici, mem_Ioo, mem_Ico]
          constructor
          · exact fun h => ⟨h.1, h.2.2⟩
          · exact fun h => ⟨h.1, by linarith [Real.pi_pos], h.2⟩
        rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici, hs]
      _ = _ := setIntegral_congr_set Ico_ae_eq_Icc
  rw [hint] at hr
  exact ⟨by simpa only [IntegrableOn, hμ] using hgi, hr.2⟩

theorem boundaryMinimum_radial_energy_inequality_uniform {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e q))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p0 : ℂ} (hp0 : ‖p0‖ = 1) :
    ∃ R K η : ℝ, 0 < R ∧ 1 ≤ K ∧ 0 < η ∧
      ∀ {p : ℂ}, ‖p‖ = 1 → dist p p0 < η →
      let en := m65EmbeddedEnergyDensity g e
        (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p)
      let E := fun s => ∫ z in closedBall (0 : LoopPlane) s ∩ {z | 0 ≤ z 1}, en z
      IntegrableOn en (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}) ∧
        AbsolutelyContinuousOnInterval E 0 R ∧
        ∀ ε : ℝ, 0 < ε → ε < R → ∀ᵐ r ∂volume.restrict (Ioo ε R),
          E r ≤ K * r * deriv E r := by
  obtain ⟨R0, δ, A, η, hR0, hδ, hA, hη, hcomparison⟩ :=
    boundary_small_semicircle_comparison_uniform g he hinj hemb compact hγ hsmooth hregular
      F hmin hp0
  obtain ⟨R1, hR1, hLp⟩ := weakDisk_boundary_memLp_uniform (e := e) (γ := γ)
  have hclosed : IsClosed (range e) := by
    simpa only [image_univ] using (compact.image he.continuous).isClosed
  obtain ⟨R2, hR2, hsemicircles⟩ := weakDisk_boundary_semicircle_uniform he.continuous hγ hclosed
  obtain ⟨R3, hR3, hgeometry⟩ := exists_uniform_boundary_halfDisk_pullback
  let R := min R0 (min R1 (min R2 R3))
  have hR : 0 < R := lt_min hR0 (lt_min hR1 (lt_min hR2 hR3))
  have hRR0 : R ≤ R0 := min_le_left _ _
  have hRR1 : R ≤ R1 := (min_le_right _ _).trans (min_le_left _ _)
  have hRR2 : R ≤ R2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hRR3 : R ≤ R3 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hE0 : 0 ≤ F.energy g := integral_nonneg fun z =>
    embeddedEnergyDensity_nonneg g e F.value (fun i z => F.derivative i z) z
  obtain ⟨c, C, hc, _hC, hb⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  let a := 2 * A / c
  let b := 2 * Real.pi * F.energy g / (c * δ ^ 2)
  let K := 1 + a + b
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  have haK : a ≤ K := by dsimp only [K]; linarith
  have hbK : b ≤ K := by dsimp only [K]; linarith
  refine ⟨R, K, η, hR, hK, hη, ?_⟩
  intro p hp hnear
  dsimp only
  obtain ⟨hvalue, hfield⟩ := hLp F hp
  have hsemicircle := hsemicircles F hp
  have hcompare := hcomparison hp hnear
  obtain ⟨hleft, hcap, _hinv, _C, _hC', _hmap⟩ := hgeometry p hp
  let S (s : ℝ) := closedBall (0 : LoopPlane) s ∩ {z | 0 ≤ z 1}
  have hSS {r s : ℝ} (hrs : r ≤ s) : S r ⊆ S s :=
    inter_subset_inter_left _ (closedBall_subset_closedBall hrs)
  let P := diskBoundaryCoordinate p
  let D := weakDiskBoundaryField F p
  let en := m65EmbeddedEnergyDensity g e (fun z => F.value (P z)) D
  let E (s : ℝ) := ∫ z in S s, en z
  have hFi := hvalue.mono_measure (Measure.restrict_mono (hSS hRR1) le_rfl)
  have hDi (i : Fin 2) := (hfield i).mono_measure (Measure.restrict_mono (hSS hRR1) le_rfl)
  have hei : IntegrableOn en (S R) :=
    m65EmbeddedEnergyDensity_integrable g e he hinj hemb compact hFi.1 hDi
  have hen (z : LoopPlane) : 0 ≤ en z :=
    embeddedEnergyDensity_nonneg g e (fun z => F.value (P z)) D z
  obtain ⟨hac, hrad⟩ := local_halfDisk_radial hR hei
  refine ⟨hei, hac, ?_⟩
  intro ε hε _hεR
  have hsemi := ae_restrict_of_ae_restrict_of_subset
    (show Ioo ε R ⊆ Icc ε R2 from fun _ h => ⟨h.1.le, h.2.le.trans hRR2⟩)
    (hsemicircle ε hε)
  have hradii := ae_restrict_of_ae_restrict_of_subset
    (show Ioo ε R ⊆ Ioo (0 : ℝ) R from fun _ h => ⟨hε.trans h.1, h.2⟩) hrad
  filter_upwards [hsemi, hradii, ae_restrict_mem measurableSet_Ioo]
    with r hsemi hradii hrange
  have hr : 0 < r := hε.trans hrange.1
  obtain ⟨hW, V, hVC, _hVAE, htarget, hV0, hVπ, hinc, hgreen⟩ := hsemi
  obtain ⟨heri, hderiv⟩ := hradii
  let W (θ : ℝ) := (-r * Real.sin θ) • D 0 (r • Proofs.M58.angularPoint θ) +
    (r * Real.cos θ) • D 1 (r • Proofs.M58.angularPoint θ)
  have hderiv0 : 0 ≤ deriv E r := by
    rw [hderiv.deriv]
    exact mul_nonneg hr.le (integral_nonneg fun θ => hen (r • Proofs.M58.angularPoint θ))
  have hX : 0 ≤ r * deriv E r := mul_nonneg hr.le hderiv0
  have hpoint (θ : ℝ) : (c / 2) * ‖W θ‖ ^ 2 ≤
      r ^ 2 * en (r • Proofs.M58.angularPoint θ) := by
    have h1 := mul_le_mul_of_nonneg_left
      (angular_field_norm_sq_le (D 0 (r • Proofs.M58.angularPoint θ))
        (D 1 (r • Proofs.M58.angularPoint θ)) r θ) (show 0 ≤ c / 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left
      (m65EmbeddedEnergyDensity_bounds g e hb (fun z => F.value (P z)) D
        (r • Proofs.M58.angularPoint θ)).1 (sq_nonneg r)
    simp only [Fin.sum_univ_two] at h2
    dsimp only [W, en]
    nlinarith only [h1, h2]
  have hi : (c / 2) * (∫ θ in Icc (0 : ℝ) Real.pi, ‖W θ‖ ^ 2) ≤
      r ^ 2 * ∫ θ in Icc (0 : ℝ) Real.pi, en (r • Proofs.M58.angularPoint θ) := by
    simpa only [integral_const_mul] using integral_mono_ae
      (hW.norm.integrable_sq.const_mul (c / 2)) (heri.const_mul (r ^ 2))
      (ae_of_all _ hpoint)
  have hangular : (∫ θ in Icc (0 : ℝ) Real.pi, ‖W θ‖ ^ 2) ≤
      (2 / c) * (r * deriv E r) := by
    calc
      _ ≤ (r ^ 2 * ∫ θ in Icc (0 : ℝ) Real.pi,
          en (r • Proofs.M58.angularPoint θ)) / (c / 2) := by
        apply (le_div_iff₀ (show 0 < c / 2 by positivity)).mpr
        simpa only [mul_comm] using hi
      _ = _ := by rw [hderiv.deriv]; dsimp only [en]; field_simp
  have hSr : IsCompact (S r) := (isCompact_closedBall (0 : LoopPlane) r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hSr3 : S r ⊆ closedBall (0 : LoopPlane) R3 ∩ {z | 0 ≤ z 1} :=
    hSS (hrange.2.le.trans hRR3)
  have hEr : E r ≤ F.energy g := weakDisk_boundary_energy_le g he hinj hemb compact F hp hSr
    (fun z hz => hleft z (hSr3 hz).1) (by rintro _ ⟨z, hz, rfl⟩; exact hcap (hSr3 hz))
  by_cases hsmall : ∀ θ ∈ Icc (0 : ℝ) Real.pi, ‖V θ - V 0‖ < δ
  · have hbound := hcompare r hr (hrange.2.le.trans hRR0)
      (hFi.mono_measure (Measure.restrict_mono (hSS hrange.2.le) le_rfl))
      (fun i => (hDi i).mono_measure (Measure.restrict_mono (hSS hrange.2.le) le_rfl))
      V W hVC htarget hV0 hVπ hW hinc hsmall hgreen
    calc
      E r ≤ A * ∫ θ in Icc (0 : ℝ) Real.pi, ‖W θ‖ ^ 2 := hbound
      _ ≤ A * ((2 / c) * (r * deriv E r)) := mul_le_mul_of_nonneg_left hangular hA.le
      _ = a * (r * deriv E r) := by dsimp only [a]; ring
      _ ≤ K * r * deriv E r := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right haK hX
  · push Not at hsmall
    obtain ⟨θ, hθ, hθδ⟩ := hsmall
    have hosc := interval_increment_norm_sq_le Real.pi_pos.le hW hinc
      0 ⟨le_rfl, Real.pi_pos.le⟩ θ hθ
    have hdelta : δ ^ 2 ≤ (2 * Real.pi / c) * (r * deriv E r) := by
      calc
        _ ≤ ‖V θ - V 0‖ ^ 2 := pow_le_pow_left₀ hδ.le hθδ 2
        _ ≤ Real.pi * ∫ θ in Icc (0 : ℝ) Real.pi, ‖W θ‖ ^ 2 := by
          simpa only [sub_zero] using hosc
        _ ≤ Real.pi * ((2 / c) * (r * deriv E r)) :=
          mul_le_mul_of_nonneg_left hangular Real.pi_pos.le
        _ = _ := by ring
    have hlarge : F.energy g ≤ b * (r * deriv E r) := by
      have h := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ F.energy g / δ ^ 2 by positivity)
      calc
        F.energy g = (F.energy g / δ ^ 2) * δ ^ 2 := by field_simp
        _ ≤ (F.energy g / δ ^ 2) * ((2 * Real.pi / c) * (r * deriv E r)) := h
        _ = _ := by dsimp only [b]; ring
    exact hEr.trans (hlarge.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hbK hX))

theorem boundaryMinimum_radial_energy_inequality {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e q))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R K : ℝ, 0 < R ∧ 1 ≤ K ∧
      let en := m65EmbeddedEnergyDensity g e
        (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p)
      let E := fun s => ∫ z in closedBall (0 : LoopPlane) s ∩ {z | 0 ≤ z 1}, en z
      IntegrableOn en (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}) ∧
        AbsolutelyContinuousOnInterval E 0 R ∧
        ∀ ε : ℝ, 0 < ε → ε < R → ∀ᵐ r ∂volume.restrict (Ioo ε R),
          E r ≤ K * r * deriv E r := by
  obtain ⟨R, K, η, hR, hK, hη, h⟩ :=
    boundaryMinimum_radial_energy_inequality_uniform g he hinj hemb compact hγ hsmooth
      hregular F hmin hp
  exact ⟨R, K, hR, hK, h hp (by simpa only [dist_self] using hη)⟩

theorem boundaryMinimum_energy_power_decay_uniform {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e q))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p0 : ℂ} (hp0 : ‖p0‖ = 1) :
    ∃ R a η : ℝ, 0 < R ∧ 0 < a ∧ a ≤ 1 ∧ 0 < η ∧
      ∀ {p : ℂ}, ‖p‖ = 1 → dist p p0 < η →
      let en := m65EmbeddedEnergyDensity g e
        (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p)
      let E := fun s => ∫ z in closedBall (0 : LoopPlane) s ∩ {z | 0 ≤ z 1}, en z
      ∀ r : ℝ, 0 < r → r ≤ R → E r ≤ E R * (r / R) ^ a := by
  obtain ⟨R, K, η, hR, hK, hη, hradial⟩ :=
    boundaryMinimum_radial_energy_inequality_uniform g he hinj hemb compact hγ hsmooth
      hregular F hmin hp0
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨R, K⁻¹, η, hR, inv_pos.mpr hK0, (inv_le_one₀ hK0).mpr hK, hη, ?_⟩
  intro p hp hnear
  obtain ⟨_hei, hAC, hineq⟩ := hradial hp hnear
  dsimp only
  intro r hr hrR
  rcases hrR.eq_or_lt with rfl | hrR
  · simp only [div_self hr.ne', Real.one_rpow, mul_one, le_refl]
  apply ac_radial_power_decay hr hrR.le hK0
  · exact hAC.mono (by
      rw [uIcc_of_le hrR.le, uIcc_of_le hR.le]
      exact Icc_subset_Icc hr.le le_rfl)
  · exact hineq r hr hrR

theorem boundaryMinimum_energy_power_decay {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e q))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R a : ℝ, 0 < R ∧ 0 < a ∧ a ≤ 1 ∧
      let en := m65EmbeddedEnergyDensity g e
        (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p)
      let E := fun s => ∫ z in closedBall (0 : LoopPlane) s ∩ {z | 0 ≤ z 1}, en z
      ∀ r : ℝ, 0 < r → r ≤ R → E r ≤ E R * (r / R) ^ a := by
  obtain ⟨R, a, η, hR, ha, ha1, hη, h⟩ :=
    boundaryMinimum_energy_power_decay_uniform g he hinj hemb compact hγ hsmooth hregular
      F hmin hp
  exact ⟨R, a, hR, ha, ha1, h hp (by simpa only [dist_self] using hη)⟩

end PoincareConjecture.M65Boundary
