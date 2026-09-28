import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityReflection
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalHolder











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

open M65Interior





theorem localMinimum_energy_decay_actual_prefactor
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (E0 : ℝ) (hE0 : 0 ≤ E0) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      ∀ (U : Set LoopPlane) (X : M65LocalWeakMap e U), IsOpen U →
        M65LocallyMinimizesEnergy g X → ∀ (x : LoopPlane) (r R : ℝ),
          0 < r → r ≤ R → closedBall x R ⊆ U →
          (∫ z in closedBall x R, m65EmbeddedEnergyDensity g e X.value X.derivative z) ≤ E0 →
          (∫ z in closedBall x r, m65EmbeddedEnergyDensity g e X.value X.derivative z) ≤
            (∫ z in closedBall x R, m65EmbeddedEnergyDensity g e X.value X.derivative z) *
              (r / R) ^ a := by
  obtain ⟨K, hK, hbound⟩ :=
    localMinimum_radial_energy_inequality g e he hinj hemb compact E0 hE0
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨K⁻¹, inv_pos.mpr hKpos, (inv_le_one₀ hKpos).mpr hK, ?_⟩
  intro U X hU hmin x r R hr hrR hRU htotal
  have hR : 0 < R := hr.trans_le hrR
  rcases hrR.eq_or_lt with rfl | hrR
  · simp only [div_self hr.ne', Real.one_rpow, mul_one, le_refl]
  let E := fun s => ∫ z in closedBall x s, m65EmbeddedEnergyDensity g e X.value X.derivative z
  have hE : AbsolutelyContinuousOnInterval E r R :=
    (X.energy_radial g he hinj hemb compact x hR hRU).1.mono (by
      rw [uIcc_of_le hrR.le, uIcc_of_le hR.le]
      exact Icc_subset_Icc hr.le le_rfl)
  exact ac_radial_power_decay hr hrR.le hKpos hE
    (hbound U X hU hmin x r R hr hrR hRU htotal)




theorem diskBoundaryCoordinate_translate (p : ℂ) (s : ℝ) (z : LoopPlane) :
    diskBoundaryCoordinate p (s • EuclideanSpace.basisFun (Fin 2) ℝ 0 + z) =
      diskBoundaryCoordinate (p * Complex.exp (Complex.I * s)) z := by
  unfold diskBoundaryCoordinate M65StrictTrace.boundaryCoordinate
  congr 1
  rw [map_add, map_smul]
  have hb : Complex.orthonormalBasisOneI.repr.symm
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) = 1 := by
    simp [EuclideanSpace.basisFun_apply]
  rw [hb, Complex.real_smul, mul_one, mul_add, Complex.exp_add]
  ring



theorem weakDiskBoundaryField_translate {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) (p : ℂ) (s : ℝ) (z : LoopPlane) (i : Fin 2) :
    weakDiskBoundaryField F p i (s • EuclideanSpace.basisFun (Fin 2) ℝ 0 + z) =
      weakDiskBoundaryField F (p * Complex.exp (Complex.I * s)) i z := by
  have hfunction : (fun w => diskBoundaryCoordinate p
      (s • EuclideanSpace.basisFun (Fin 2) ℝ 0 + w)) =
        diskBoundaryCoordinate (p * Complex.exp (Complex.I * s)) :=
    funext (diskBoundaryCoordinate_translate p s)
  have hderivative : fderiv ℝ (diskBoundaryCoordinate p)
      (s • EuclideanSpace.basisFun (Fin 2) ℝ 0 + z) =
        fderiv ℝ (diskBoundaryCoordinate (p * Complex.exp (Complex.I * s))) z := by
    have hd := ((contDiff_diskBoundaryCoordinate p).differentiable (by simp)
      (s • EuclideanSpace.basisFun (Fin 2) ℝ 0 + z)).hasFDerivAt.comp z
        ((hasFDerivAt_id z).const_add (s • EuclideanSpace.basisFun (Fin 2) ℝ 0))
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, hfunction] using hd.fderiv.symm
  ext j
  simp only [weakDiskBoundaryField, diskBoundaryCoordinate_translate, hderivative]





theorem boundaryMinimum_energy_bound_uniform {M : Type*} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e q))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p0 : ℂ} (hp0 : ‖p0‖ = 1) :
    ∃ R a η B : ℝ, 0 < R ∧ 0 < a ∧ a ≤ 1 ∧ 0 < η ∧ 0 ≤ B ∧
      ∀ {p : ℂ}, ‖p‖ = 1 → dist p p0 < η → ∀ r : ℝ, 0 < r → r ≤ R →
      (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        m65EmbeddedEnergyDensity g e (fun z => F.value (diskBoundaryCoordinate p z))
          (weakDiskBoundaryField F p) z) ≤ B * r ^ a := by
  obtain ⟨R0, K, η, hR0, hK, hη, hrad⟩ :=
    boundaryMinimum_radial_energy_inequality_uniform g he hinj hemb compact hγ hsmooth
      hregular F hmin hp0
  obtain ⟨R1, hR1, hinverse⟩ := exists_uniform_boundary_halfDisk_pullback
  let R := min R0 R1
  have hR : 0 < R := lt_min hR0 hR1
  have hRR0 : R ≤ R0 := min_le_left _ _
  have hRR1 : R ≤ R1 := min_le_right _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hE0 : 0 ≤ F.energy g := integral_nonneg fun z =>
    embeddedEnergyDensity_nonneg g e F.value (fun i z => F.derivative i z) z
  refine ⟨R, K⁻¹, η, F.energy g / R ^ K⁻¹, hR, inv_pos.mpr hKpos,
    (inv_le_one₀ hKpos).mpr hK, hη, div_nonneg hE0 (Real.rpow_nonneg hR.le _), ?_⟩
  intro p hp hnear r hr hrR
  let E := fun s => ∫ z in closedBall (0 : LoopPlane) s ∩ {z | 0 ≤ z 1},
    m65EmbeddedEnergyDensity g e (fun z => F.value (diskBoundaryCoordinate p z))
      (weakDiskBoundaryField F p) z
  obtain ⟨_hEi, hAC, hineq⟩ := hrad hp hnear
  have hdecay : E r ≤ E R * (r / R) ^ K⁻¹ := by
    rcases hrR.eq_or_lt with rfl | hrR
    · simp only [div_self hr.ne', Real.one_rpow, mul_one, le_refl]
    apply ac_radial_power_decay hr hrR.le hKpos
    · exact hAC.mono (by
        rw [uIcc_of_le hrR.le, uIcc_of_le hR0.le]
        exact Icc_subset_Icc hr.le hRR0)
    · exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hRR0)
        (hineq r hr (hrR.trans_le hRR0))
  obtain ⟨hleft, hcap, _⟩ := hinverse p hp
  have htotal : E R ≤ F.energy g :=
    weakDisk_boundary_energy_le g he hinj hemb compact F hp
      ((isCompact_closedBall (0 : LoopPlane) R).inter_right
        (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous))
      (fun z hz => hleft z (closedBall_subset_closedBall hRR1 hz.1))
      (by
        rintro _ ⟨z, hz, rfl⟩
        exact hcap ⟨closedBall_subset_closedBall hRR1 hz.1, hz.2⟩)
  calc
    E r ≤ E R * (r / R) ^ K⁻¹ := hdecay
    _ ≤ F.energy g * (r / R) ^ K⁻¹ :=
      mul_le_mul_of_nonneg_right htotal (Real.rpow_nonneg (div_nonneg hr.le hR.le) _)
    _ = F.energy g / R ^ K⁻¹ * r ^ K⁻¹ := by
      rw [Real.div_rpow hr.le hR.le]
      ring




theorem weakDisk_boundary_energy_translate {M : Type*} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    {γ : LoopCircle → M} (F : M65WeakDisk e γ) (p : ℂ) (s r : ℝ) :
    (∫ z in closedBall (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) r ∩ {z | 0 ≤ z 1},
      m65EmbeddedEnergyDensity g e (fun z => F.value (diskBoundaryCoordinate p z))
        (weakDiskBoundaryField F p) z) =
      ∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
        m65EmbeddedEnergyDensity g e
          (fun z => F.value (diskBoundaryCoordinate (p * Complex.exp (Complex.I * s)) z))
          (weakDiskBoundaryField F (p * Complex.exp (Complex.I * s))) z := by
  let x := s • EuclideanSpace.basisFun (Fin 2) ℝ 0
  let en := m65EmbeddedEnergyDensity g e
    (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p)
  have hpre : (fun z : LoopPlane => x + z) ⁻¹'
      (closedBall x r ∩ {z | 0 ≤ z 1}) =
        closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1} := by
    ext z
    simp [x, dist_eq_norm, EuclideanSpace.basisFun_apply]
  have hchange := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding en
    (closedBall x r ∩ {z | 0 ≤ z 1})
  rw [hpre] at hchange
  rw [← hchange]
  apply setIntegral_congr_fun
    (measurableSet_closedBall.inter
      (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet)
  intro z _
  simp only [en, x, m65EmbeddedEnergyDensity, diskBoundaryCoordinate_translate,
    weakDiskBoundaryField_translate]




theorem reflected_energy_density {M : Type*} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (q : LoopPlane → M) (D : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (z : LoopPlane) :
    m65EmbeddedEnergyDensity g e
      (fun w => if 0 ≤ w 1 then q w else q (boundaryPlaneReflection w))
      (fun i w => if 0 ≤ w 1 then D i w else
        (if i = 0 then (1 : ℝ) else -1) • D i (boundaryPlaneReflection w)) z =
      if 0 ≤ z 1 then m65EmbeddedEnergyDensity g e q D z
      else m65EmbeddedEnergyDensity g e q D (boundaryPlaneReflection z) := by
  by_cases hz : 0 ≤ z 1
  · simp only [m65EmbeddedEnergyDensity, hz, if_true]
  · simp [m65EmbeddedEnergyDensity, hz, Fin.sum_univ_two]

private theorem reflection_even_function (f : LoopPlane → ℝ) (z : LoopPlane) :
    (if 0 ≤ (boundaryPlaneReflection z) 1 then f (boundaryPlaneReflection z)
      else f (boundaryPlaneReflection (boundaryPlaneReflection z))) =
        if 0 ≤ z 1 then f z else f (boundaryPlaneReflection z) := by
  rw [(reflection_coordinates _).2, reflection_involution]
  rcases lt_trichotomy (z 1) 0 with hz | hz | hz
  · simp [hz.le, hz.not_ge]
  · have heq : boundaryPlaneReflection z = z := by
      ext i
      fin_cases i
      · exact (reflection_coordinates z).1
      · change boundaryPlaneReflection z 1 = z 1
        rw [(reflection_coordinates z).2, hz, neg_zero]
    simp [hz, heq]
  · simp [hz.le, not_le_of_gt hz]

private theorem even_integral_le_twice_half {f : LoopPlane → ℝ} {r : ℝ}
    (hf : IntegrableOn f (closedBall (0 : LoopPlane) r))
    (hnonneg : ∀ z, 0 ≤ f z)
    (heven : ∀ z, f (boundaryPlaneReflection z) = f z) :
    (∫ z in closedBall (0 : LoopPlane) r, f z) ≤
      2 * ∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}, f z := by
  let H : Set LoopPlane := {z | 0 ≤ z 1}
  let u := H.indicator f
  have hH : MeasurableSet H :=
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hu : IntegrableOn u (closedBall (0 : LoopPlane) r) := hf.indicator hH
  have hpre : boundaryPlaneReflection ⁻¹' closedBall (0 : LoopPlane) r =
      closedBall (0 : LoopPlane) r := by
    ext z
    simp only [mem_preimage, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
  have hmu := boundaryPlaneReflection.measurePreserving.restrict_preimage_emb
    boundaryPlaneReflection.toHomeomorph.measurableEmbedding (closedBall (0 : LoopPlane) r)
  rw [hpre] at hmu
  have hv := hmu.integrable_comp_of_integrable hu
  have hbound : ∀ z, f z ≤ u z + u (boundaryPlaneReflection z) := by
    intro z
    change f z ≤ H.indicator f z + H.indicator f (boundaryPlaneReflection z)
    by_cases hz : 0 ≤ z 1
    · rw [indicator_of_mem (show z ∈ H from hz)]
      exact le_add_of_nonneg_right (indicator_nonneg (fun w _ => hnonneg w) _)
    · have href : boundaryPlaneReflection z ∈ H := by
        change 0 ≤ (boundaryPlaneReflection z) 1
        rw [(reflection_coordinates _).2]
        exact neg_nonneg.mpr (le_of_not_ge hz)
      rw [indicator_of_notMem (show z ∉ H from hz), indicator_of_mem href, heven, zero_add]
  have hi := integral_mono_ae hf (hu.add hv) (ae_of_all _ hbound)
  have hsame := hmu.integral_comp boundaryPlaneReflection.toHomeomorph.measurableEmbedding u
  change (∫ z in closedBall (0 : LoopPlane) r, f z) ≤
    ∫ z in closedBall (0 : LoopPlane) r, u z + (u ∘ boundaryPlaneReflection) z at hi
  rw [integral_add hu hv] at hi
  simp only [Function.comp_def] at hi
  rw [hsame] at hi
  simpa only [u, integral_indicator hH, Measure.restrict_restrict hH,
    inter_comm H, two_mul] using hi

private theorem axis_norm (s : ℝ) :
    ‖s • EuclideanSpace.basisFun (Fin 2) ℝ 0‖ = |s| := by
  rw [norm_smul, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one, Real.norm_eq_abs]

private theorem axis_distance (x : LoopPlane) :
    dist x (x 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0) = |x 1| := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, EuclideanSpace.basisFun_apply, Real.sqrt_sq_eq_abs]

private theorem reflection_axis (s : ℝ) :
    boundaryPlaneReflection (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      s • EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
  ext i
  fin_cases i
  · exact (reflection_coordinates _).1
  · change boundaryPlaneReflection (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) 1 = _
    simp [(reflection_coordinates _).2, EuclideanSpace.basisFun_apply]

private theorem even_integral_at_axis {f : LoopPlane → ℝ} {s r : ℝ}
    (hf : IntegrableOn f (closedBall (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) r))
    (hnonneg : ∀ z, 0 ≤ f z)
    (heven : ∀ z, f (boundaryPlaneReflection z) = f z) :
    (∫ z in closedBall (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) r, f z) ≤
      2 * ∫ z in closedBall (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) r ∩ {z | 0 ≤ z 1},
        f z := by
  let x := s • EuclideanSpace.basisFun (Fin 2) ℝ 0
  have hpre : (fun z : LoopPlane => x + z) ⁻¹' closedBall x r =
      closedBall (0 : LoopPlane) r := by ext z; simp [dist_eq_norm]
  have hpreH : (fun z : LoopPlane => x + z) ⁻¹'
      (closedBall x r ∩ {z | 0 ≤ z 1}) =
        closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1} := by
    ext z
    simp [x, dist_eq_norm, EuclideanSpace.basisFun_apply]
  have hmu := (measurePreserving_add_left volume x).restrict_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding (closedBall x r)
  rw [hpre] at hmu
  have hb := even_integral_le_twice_half (hmu.integrable_comp_of_integrable hf)
    (fun z => hnonneg (x + z)) (fun z => by
      change f (x + boundaryPlaneReflection z) = f (x + z)
      calc
        _ = f (boundaryPlaneReflection (x + z)) := by rw [map_add, reflection_axis]
        _ = _ := heven _)
  have hchange := hmu.integral_comp (Homeomorph.addLeft x).measurableEmbedding f
  have hchangeH := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (closedBall x r ∩ {z | 0 ≤ z 1})
  rw [hpreH] at hchangeH
  simpa only [Function.comp_def, hchange, hchangeH] using hb

private theorem even_integral_reflection {f : LoopPlane → ℝ}
    (heven : ∀ z, f (boundaryPlaneReflection z) = f z) (x : LoopPlane) (r : ℝ) :
    (∫ z in closedBall (boundaryPlaneReflection x) r, f z) =
      ∫ z in closedBall x r, f z := by
  have hpre : boundaryPlaneReflection ⁻¹' closedBall x r =
      closedBall (boundaryPlaneReflection x) r := by
    ext z
    simp only [mem_preimage, mem_closedBall]
    have hd := boundaryPlaneReflection.dist_map z (boundaryPlaneReflection x)
    rw [reflection_involution] at hd
    exact iff_of_eq (congrArg (fun d => d ≤ r) hd)
  have h := boundaryPlaneReflection.measurePreserving.setIntegral_preimage_emb
    boundaryPlaneReflection.toHomeomorph.measurableEmbedding f (closedBall x r)
  simpa only [hpre, heven] using h





theorem even_energy_decay_of_halfDisk_and_interior
    {f : LoopPlane → ℝ} {R a b B : ℝ} (_hR : 0 < R) (hR1 : R ≤ 1)
    (hb1 : b ≤ 1) (hB : 0 ≤ B)
    (hf : IntegrableOn f (closedBall (0 : LoopPlane) (4 * R)))
    (hnonneg : ∀ z, 0 ≤ f z)
    (heven : ∀ z, f (boundaryPlaneReflection z) = f z)
    (hboundary : ∀ s : ℝ, |s| ≤ R / 2 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 3 * R →
      (∫ z in closedBall (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) ρ ∩ {z | 0 ≤ z 1},
        f z) ≤ B * ρ ^ b)
    (hlocal : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2), 0 < x 1 →
      ∀ r T : ℝ, 0 < r → r ≤ T → T < x 1 →
      (∫ z in closedBall x r, f z) ≤
        (∫ z in closedBall x T, f z) * (r / T) ^ a) :
    ∀ x ∈ closedBall (0 : LoopPlane) (R / 2), ∀ r : ℝ, 0 < r → r ≤ R / 2 →
      (∫ z in closedBall x r, f z) ≤ (6 * B) * r ^ min a b := by
  have h3 : (3 : ℝ) ^ b ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hb1
  have hupper : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2), 0 ≤ x 1 →
      ∀ r : ℝ, 0 < r → r ≤ R / 2 →
      (∫ z in closedBall x r, f z) ≤ (6 * B) * r ^ min a b := by
    intro x hx hxpos r hr hrR
    have hxnorm : ‖x‖ ≤ R / 2 := mem_closedBall_zero_iff.mp hx
    have hcoord (i : Fin 2) : |x i| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    have hx0 : |x 0| ≤ R / 2 := (hcoord 0).trans hxnorm
    have hx1 : x 1 ≤ R / 2 :=
      (le_abs_self _).trans ((hcoord 1).trans hxnorm)
    let q := x 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0
    have hdist : dist x q = x 1 := by rw [axis_distance, abs_of_nonneg hxpos]
    have hbig (t : ℝ) (ht : t ≤ 3 * R) : closedBall q t ⊆ closedBall 0 (4 * R) :=
      closedBall_subset_closedBall' (by
        rw [dist_zero_right, axis_norm]
        linarith)
    have hfi (t : ℝ) (ht : t ≤ 3 * R) : IntegrableOn f (closedBall q t) :=
      hf.mono_set (hbig t ht)
    have hr1 : r ≤ 1 := by linarith
    by_cases hnear : x 1 ≤ 2 * r
    · have hcover : closedBall x r ⊆ closedBall q (3 * r) :=
        closedBall_subset_closedBall' (by rw [hdist]; linarith)
      have h3r : 3 * r ≤ 3 * R := by linarith
      have hpow : r ^ b ≤ r ^ min a b :=
        Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_right _ _)
      calc
        _ ≤ ∫ z in closedBall q (3 * r), f z :=
          setIntegral_mono_set (hfi _ h3r) (ae_of_all _ hnonneg)
            (ae_of_all _ fun _ hz => hcover hz)
        _ ≤ 2 * ∫ z in closedBall q (3 * r) ∩ {z | 0 ≤ z 1}, f z :=
          even_integral_at_axis (hfi _ h3r) hnonneg heven
        _ ≤ 2 * (B * (3 * r) ^ b) :=
          mul_le_mul_of_nonneg_left (hboundary _ hx0 _ (by positivity) h3r) (by norm_num)
        _ ≤ (6 * B) * r ^ min a b := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hr.le]
          have hp := mul_le_mul h3 hpow (Real.rpow_nonneg hr.le _) (by norm_num)
          have hb := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB)
          nlinarith only [hb]
    · have hfar : 2 * r < x 1 := lt_of_not_ge hnear
      let T := x 1 / 2
      have hT : 0 < T := by dsimp only [T]; linarith
      have hrT : r ≤ T := by dsimp only [T]; linarith
      have hT1 : T ≤ 1 := by dsimp only [T]; linarith
      have hTlt : T < x 1 := by dsimp only [T]; linarith
      have h3T : 3 * T ≤ 3 * R := by dsimp only [T]; linarith
      have hcover : closedBall x T ⊆ closedBall q (3 * T) ∩ {z | 0 ≤ z 1} := by
        intro z hz
        refine ⟨closedBall_subset_closedBall'
          (show T + dist x q ≤ 3 * T by rw [hdist]; dsimp only [T]; linarith) hz, ?_⟩
        have hd : |z 1 - x 1| ≤ T := by
          have hc : |z 1 - x 1| ≤ ‖z - x‖ := by
            simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (z - x) 1
          exact hc.trans (mem_closedBall.mp hz)
        have hl := (abs_le.mp hd).1
        change 0 ≤ z 1
        dsimp only [T] at hl
        linarith
      have houter : (∫ z in closedBall x T, f z) ≤ (3 * B) * T ^ min a b := by
        calc
          _ ≤ ∫ z in closedBall q (3 * T) ∩ {z | 0 ≤ z 1}, f z :=
            setIntegral_mono_set ((hfi _ h3T).mono_set inter_subset_left)
              (ae_of_all _ hnonneg) (ae_of_all _ fun _ hz => hcover hz)
          _ ≤ B * (3 * T) ^ b := hboundary _ hx0 _ (by positivity) h3T
          _ ≤ _ := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hT.le]
            have hp := mul_le_mul h3
              (Real.rpow_le_rpow_of_exponent_ge hT hT1 (min_le_right a b))
              (Real.rpow_nonneg hT.le _) (by norm_num)
            have hb := mul_le_mul_of_nonneg_left hp hB
            nlinarith only [hb]
      have hratio : (r / T) ^ a ≤ (r / T) ^ min a b :=
        Real.rpow_le_rpow_of_exponent_ge (div_pos hr hT)
          ((div_le_one hT).mpr hrT) (min_le_left _ _)
      calc
        _ ≤ (∫ z in closedBall x T, f z) * (r / T) ^ a :=
          hlocal x hx (by linarith) r T hr hrT hTlt
        _ ≤ (∫ z in closedBall x T, f z) * (r / T) ^ min a b :=
          mul_le_mul_of_nonneg_left hratio (integral_nonneg hnonneg)
        _ ≤ ((3 * B) * T ^ min a b) * (r / T) ^ min a b :=
          mul_le_mul_of_nonneg_right houter (Real.rpow_nonneg (div_nonneg hr.le hT.le) _)
        _ = (3 * B) * r ^ min a b := by
          rw [Real.div_rpow hr.le hT.le]
          have hp : T ^ min a b ≠ 0 := (Real.rpow_pos_of_pos hT _).ne'
          field_simp
        _ ≤ (6 * B) * r ^ min a b :=
          mul_le_mul_of_nonneg_right (by nlinarith only [hB]) (Real.rpow_nonneg hr.le _)
  intro x hx r hr hrR
  by_cases hxpos : 0 ≤ x 1
  · exact hupper x hx hxpos r hr hrR
  · rw [← even_integral_reflection heven x r]
    apply hupper (boundaryPlaneReflection x)
    · simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using hx
    · rw [(reflection_coordinates _).2]
      exact neg_nonneg.mpr (le_of_not_ge hxpos)
    · exact hr
    · exact hrR





theorem weakDisk_exists_boundary_full_energy_decay
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ Q R α B : ℝ, 0 < R ∧ R < Q ∧ 0 < α ∧ α ≤ 1 ∧ 0 ≤ B ∧
      ∃ X : M65LocalWeakMap e (ball (0 : LoopPlane) Q),
        (∀ z, X.value z = if 0 ≤ z 1 then F.value (diskBoundaryCoordinate p z)
          else F.value (diskBoundaryCoordinate p (boundaryPlaneReflection z))) ∧
        (∀ i z, X.derivative i z = if 0 ≤ z 1 then weakDiskBoundaryField F p i z else
          (if i = 0 then (1 : ℝ) else -1) •
            weakDiskBoundaryField F p i (boundaryPlaneReflection z)) ∧
        ∀ x ∈ closedBall (0 : LoopPlane) (R / 2), ∀ r : ℝ, 0 < r → r ≤ R / 2 →
          (∫ z in closedBall x r, m65EmbeddedEnergyDensity g e X.value X.derivative z) ≤
            B * r ^ α := by
  obtain ⟨R0, b, η, B, hR0, hb, hb1, hη, hB, hboundary⟩ :=
    boundaryMinimum_energy_bound_uniform g he hinj hemb compact hγ hsmooth hregular F hmin hp
  obtain ⟨Rinv, hRinv, hgeometry⟩ := exists_uniform_boundary_halfDisk_pullback
  obtain ⟨Q, hQ, hQinv, X, Y, hXv, hXd, hYv, hYd, hYmin⟩ :=
    weakDisk_exists_boundary_reflected_minimum g he hinj hemb compact hγ F hmin hp hRinv
  have hE0 : 0 ≤ F.energy g := integral_nonneg fun z =>
    embeddedEnergyDensity_nonneg g e F.value (fun i z => F.derivative i z) z
  obtain ⟨a, ha, ha1, hinterior⟩ :=
    localMinimum_energy_decay_actual_prefactor g e he hinj hemb compact (F.energy g) hE0
  have hc : Continuous (fun s : ℝ => p * Complex.exp (Complex.I * s)) := by fun_prop
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0)) η hη
  let R := min 1 (min (Q / 8) (min (R0 / 4) δ))
  have hR : 0 < R := lt_min zero_lt_one
    (lt_min (by positivity) (lt_min (by positivity) hδ))
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRQ : R ≤ Q / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hRR0 : R ≤ R0 / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hRδ : R ≤ δ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hcompact : closedBall (0 : LoopPlane) (4 * R) ⊆ ball 0 Q :=
    closedBall_subset_ball (by linarith)
  let f := m65EmbeddedEnergyDensity g e X.value X.derivative
  let original := m65EmbeddedEnergyDensity g e
    (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p)
  have hfeq (z : LoopPlane) : f z =
      if 0 ≤ z 1 then original z else original (boundaryPlaneReflection z) := by
    have hv := funext hXv
    have hd := funext fun i => funext (hXd i)
    simpa only [f, hv, hd, original] using reflected_energy_density g e
      (fun z => F.value (diskBoundaryCoordinate p z)) (weakDiskBoundaryField F p) z
  have hfeven (z : LoopPlane) : f (boundaryPlaneReflection z) = f z := by
    rw [hfeq, hfeq]
    exact reflection_even_function original z
  have hfnonneg (z : LoopPlane) : 0 ≤ f z :=
    embeddedEnergyDensity_nonneg g e X.value X.derivative z
  have hfi := X.energy_integrable g he hinj hemb compact
    (closedBall (0 : LoopPlane) (4 * R)) (isCompact_closedBall _ _) hcompact
  have hbound : ∀ s : ℝ, |s| ≤ R / 2 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 3 * R →
      (∫ z in closedBall (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) ρ ∩ {z | 0 ≤ z 1},
        f z) ≤ B * ρ ^ b := by
    intro s hs ρ hρ hρR
    have hunit : ‖p * Complex.exp (Complex.I * s)‖ = 1 := by
      rw [norm_mul, hp, one_mul, Complex.norm_exp]
      simp [Complex.mul_re]
    have hnear : dist (p * Complex.exp (Complex.I * s)) p < η := by
      have hsδ : dist s 0 < δ := by rw [dist_zero_right, Real.norm_eq_abs]; linarith
      simpa using hclose hsδ
    calc
      _ = ∫ z in closedBall (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) ρ ∩ {z | 0 ≤ z 1},
          original z := by
        apply setIntegral_congr_fun (measurableSet_closedBall.inter
          (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet)
        intro z hz
        have hzp : 0 ≤ z 1 := hz.2
        rw [hfeq, if_pos hzp]
      _ = _ := weakDisk_boundary_energy_translate g F p s ρ
      _ ≤ _ := hboundary hunit hnear ρ hρ (by linarith)
  have hlocal : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2), 0 < x 1 →
      ∀ r T : ℝ, 0 < r → r ≤ T → T < x 1 →
      (∫ z in closedBall x r, f z) ≤ (∫ z in closedBall x T, f z) * (r / T) ^ a := by
    intro x hx hxpos r T hr hrT hTlt
    have hT : 0 < T := hr.trans_le hrT
    have hxnorm : ‖x‖ ≤ R / 2 := mem_closedBall_zero_iff.mp hx
    have hx1 : x 1 ≤ R / 2 := by
      have hc : |x 1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 1
      exact (le_abs_self _).trans (hc.trans hxnorm)
    have hball : closedBall x T ⊆ ball (0 : LoopPlane) Q := by
      apply (closedBall_subset_closedBall' (show T + dist x 0 ≤ 4 * R by
        rw [dist_zero_right]; linarith)).trans hcompact
    have hpositive : ∀ z ∈ closedBall x T, 0 < z 1 := by
      intro z hz
      have hc : |z 1 - x 1| ≤ ‖z - x‖ := by
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (z - x) 1
      have hl := (abs_le.mp (hc.trans (mem_closedBall.mp hz))).1
      linarith
    have hYball : closedBall x T ⊆ ball (0 : LoopPlane) Q ∩ {z | 0 < z 1} :=
      fun z hz => ⟨hball hz, hpositive z hz⟩
    obtain ⟨hleft, hcap, _⟩ := hgeometry p hp
    have htotal : (∫ z in closedBall x T,
        m65EmbeddedEnergyDensity g e Y.value Y.derivative z) ≤ F.energy g := by
      rw [hYv, hYd]
      exact weakDisk_boundary_energy_le g he hinj hemb compact F hp
        (isCompact_closedBall _ _)
        (fun z hz => hleft z (closedBall_subset_closedBall hQinv
          (ball_subset_closedBall (hball hz)))) (by
          rintro _ ⟨z, hz, rfl⟩
          exact hcap ⟨closedBall_subset_closedBall hQinv
            (ball_subset_closedBall (hball hz)), (hpositive z hz).le⟩)
    have hchange (s : ℝ) (hs : s ≤ T) :
        (∫ z in closedBall x s, f z) =
          ∫ z in closedBall x s, m65EmbeddedEnergyDensity g e Y.value Y.derivative z := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro z hz
      rw [hfeq, if_pos (hpositive z (closedBall_subset_closedBall hs hz)).le, hYv, hYd]
    rw [hchange r hrT, hchange T le_rfl]
    exact hinterior _ Y
      (isOpen_ball.inter (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous))
      hYmin x r T hr hrT hYball htotal
  refine ⟨Q, R, min a b, 6 * B, hR, by linarith, lt_min ha hb,
    (min_le_left _ _).trans ha1, mul_nonneg (by norm_num) hB, X, hXv, hXd, ?_⟩
  exact even_energy_decay_of_halfDisk_and_interior hR hR1 hb1 hB hfi hfnonneg hfeven hbound hlocal

end PoincareConjecture.M65Boundary
