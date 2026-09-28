import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateWeakDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.Localization
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Witnesses

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter UniformSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

private def zeroExtendL2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : Set X} (hK : MeasurableSet K) :
    Lp ℝ 2 (μ.restrict K) →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => ((memLp_indicator_iff_restrict hK).mpr (Lp.memLp f)).toLp
        (K.indicator f)
      map_add' := by
        intro f g
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
        exact ((ae_restrict_iff' hK).mp (Lp.coeFn_add f g)).mono fun x hx => by
          by_cases h : x ∈ K
          · simp only [indicator_of_mem h, hx h, Pi.add_apply]
          · simp only [Pi.add_apply, indicator_of_notMem h, add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
        exact ((ae_restrict_iff' hK).mp (Lp.coeFn_smul c f)).mono fun x hx => by
          by_cases h : x ∈ K
          · simp only [indicator_of_mem h, hx h, Pi.smul_apply, RingHom.id_apply]
          · simp only [indicator_of_notMem h, smul_zero, Pi.smul_apply] }
    1 (fun f => by
      change ‖((memLp_indicator_iff_restrict hK).mpr (Lp.memLp f)).toLp _‖ ≤ _
      rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hK, Lp.norm_def, one_mul])

private theorem zeroExtendL2_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : Set X} (hK : MeasurableSet K)
    (f : Lp ℝ 2 (μ.restrict K)) :
    (zeroExtendL2 hK f : X → ℝ) =ᵐ[μ] K.indicator f := by
  exact ((memLp_indicator_iff_restrict hK).mpr (Lp.memLp f)).coeFn_toLp

private def boundedMulL2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (C : ℝ)
    (hC : ∀ x, ‖a x‖ ≤ C) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := by
  have hm (f : Lp ℝ 2 μ) : MemLp (fun x => a x * f x) 2 μ :=
    (Lp.memLp f).of_le_mul (ha.mul (Lp.aestronglyMeasurable f))
      (Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  exact LinearMap.mkContinuous
    { toFun := fun f => (hm f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [hx, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [hx, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    C (fun f => Lp.norm_le_mul_norm_of_ae_le_mul <| by
      filter_upwards [(hm f).coeFn_toLp] with x hx
      change ‖((hm f).toLp _) x‖ ≤ C * ‖f x‖
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

private theorem boundedMulL2_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (C : ℝ)
    (hC : ∀ x, ‖a x‖ ≤ C) (f : Lp ℝ 2 μ) :
    (boundedMulL2 a ha C hC f : X → ℝ) =ᵐ[μ] fun x => a x * f x := by
  have hm : MemLp (fun x => a x * f x) 2 μ :=
    (Lp.memLp f).of_le_mul (ha.mul (Lp.aestronglyMeasurable f))
      (Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  exact hm.coeFn_toLp

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

variable (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
  (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
  (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target)

include hc hs in
omit [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] in
private theorem coordinateSupport_compact : IsCompact (e.symm '' tsupport χ) :=
  hc.isCompact.image_of_continuousOn (e.symm.continuousOn.mono hs)

include hs in
omit [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] in
private theorem coordinateSupport_subset : e.symm '' tsupport χ ⊆ e.source := by
  rintro z ⟨y, hy, rfl⟩
  exact e.map_target (hs hy)

private def localizedValue : Lp ℝ 2 g.volumeMeasure →L[ℝ]
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let a := chartPullback e χ
  have ha := (contDiff_chartPullback e he hχ hc hs).continuous
  have hac := hasCompactSupport_chartPullback e hc hs
  let C := (hac.exists_bound_of_continuous ha).choose
  have hC := (hac.exists_bound_of_continuous ha).choose_spec
  exact (boundedMulL2 a ha.aestronglyMeasurable C hC).comp
    ((zeroExtendL2 (coordinateSupport_compact e χ hc hs).measurableSet).comp
      (g.compactL2Pullback e he hei (coordinateSupport_compact e χ hc hs)
        (coordinateSupport_subset e χ hs)))

private theorem localizedValue_ae (u : Lp ℝ 2 g.volumeMeasure) :
    (localizedValue e he hei χ hχ hc hs u : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] chartPullback e (fun y => χ y * u y) := by
  let a := chartPullback e χ
  have ha := (contDiff_chartPullback e he hχ hc hs).continuous
  have hac := hasCompactSupport_chartPullback e hc hs
  let C := (hac.exists_bound_of_continuous ha).choose
  have hC := (hac.exists_bound_of_continuous ha).choose_spec
  let K := e.symm '' tsupport χ
  have hK := coordinateSupport_compact e χ hc hs
  let P := g.compactL2Pullback e he hei hK (coordinateSupport_subset e χ hs)
  change (boundedMulL2 a ha.aestronglyMeasurable C hC
    (zeroExtendL2 hK.measurableSet (P u)) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] _
  filter_upwards [boundedMulL2_ae a ha.aestronglyMeasurable C hC
      (zeroExtendL2 hK.measurableSet (P u)), zeroExtendL2_ae hK.measurableSet (P u),
    (ae_restrict_iff' hK.measurableSet).mp
      (g.compactL2Pullback_ae e he hei hK (coordinateSupport_subset e χ hs) u)]
    with z hz hzero hP
  rw [hz, hzero]
  by_cases hsource : z ∈ e.source
  · rw [chartPullback_apply e _ hsource]
    change chartPullback e χ z * K.indicator (P u) z = _
    rw [chartPullback_apply e χ hsource]
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK, hP hzK]
    · have hχz : χ (e z) = 0 := image_eq_zero_of_notMem_tsupport
        (fun hz => hzK ⟨e z, hz, e.left_inv hsource⟩)
      rw [hχz, zero_mul, zero_mul]
  · simp only [a, chartPullback, indicator_of_notMem hsource, zero_mul]

private theorem localizedValue_test_ae (f : EnergyTest D Ω) :
    (localizedValue e he hei χ hχ hc hs (testToL2 D Ω f) :
      EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] chartPullback e (f.mulSmooth χ hχ) := by
  have hK := coordinateSupport_compact e χ hc hs
  filter_upwards [localizedValue_ae e he hei χ hχ hc hs (testToL2 D Ω f),
    (ae_restrict_iff' hK.measurableSet).mp
      (g.ae_comp_on_compact e he hei hK (coordinateSupport_subset e χ hs)
        f.memLp.coeFn_toLp)] with z hz hrep
  rw [hz]
  by_cases hsource : z ∈ e.source
  · rw [chartPullback_apply e _ hsource, chartPullback_apply e _ hsource,
      EnergyTest.mulSmooth_apply]
    by_cases hχz : e z ∈ tsupport χ
    · exact congrArg (χ (e z) * ·) (hrep ⟨e z, hχz, e.left_inv hsource⟩)
    · rw [image_eq_zero_of_notMem_tsupport hχz, zero_mul, zero_mul]
  · simp only [chartPullback, indicator_of_notMem hsource]

private def localizedDerivativeTest (v : EuclideanSpace ℝ (Fin n)) :
    EnergyTest D Ω →L[ℝ] Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (zeroExtendL2 (coordinateSupport_compact e χ hc hs).measurableSet).comp
    ((EnergyTest.coordinateDerivativeCLM e he hei (coordinateSupport_compact e χ hc hs)
      (coordinateSupport_subset e χ hs) v).comp (mulSmoothCLM D Ω χ hχ hc))

private theorem localizedDerivativeTest_ae (v : EuclideanSpace ℝ (Fin n))
    (f : EnergyTest D Ω) :
    (localizedDerivativeTest e he hei χ hχ hc hs v f : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] fun z => fderiv ℝ (chartPullback e (f.mulSmooth χ hχ)) z v := by
  have hK := coordinateSupport_compact e χ hc hs
  have hKs := coordinateSupport_subset e χ hs
  let F := f.mulSmooth χ hχ
  have hFs : tsupport (F : M → ℝ) ⊆ e.target :=
    (f.mulSmooth_support_subset χ hχ).trans hs
  have hUs : tsupport (chartPullback e F) ⊆ e.symm '' tsupport χ :=
    (tsupport_chartPullback_subset_image e F.hasCompactSupport hFs).trans
      (image_mono (f.mulSmooth_support_subset χ hχ))
  filter_upwards [zeroExtendL2_ae hK.measurableSet
      (EnergyTest.coordinateDerivativeL2 e he hK hKs v F),
    (ae_restrict_iff' hK.measurableSet).mp
      (EnergyTest.coordinateDerivativeL2_ae e he hK hKs v F)] with z hz hd
  change (zeroExtendL2 hK.measurableSet
    (EnergyTest.coordinateDerivativeL2 e he hK hKs v F)) z = _
  rw [hz]
  by_cases hzK : z ∈ e.symm '' tsupport χ
  · rw [indicator_of_mem hzK, hd hzK]
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v)
      (chartPullback_eventuallyEq e F (hKs hzK)).fderiv_eq.symm
  · rw [indicator_of_notMem hzK]
    have hd0 : fderiv ℝ (chartPullback e F) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hz => hzK (hUs (tsupport_fderiv_subset ℝ hz)))
    change 0 = fderiv ℝ (chartPullback e F) z v
    rw [hd0, zero_apply]

private def localizedDerivative (v : EuclideanSpace ℝ (Fin n)) :
    H1Zero D Ω →L[ℝ] Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (localizedDerivativeTest e he hei χ hχ hc hs v).extend Completion.toComplL

private theorem localizedDerivative_coe (v : EuclideanSpace ℝ (Fin n))
    (f : EnergyTest D Ω) :
    localizedDerivative e he hei χ hχ hc hs v (f : H1Zero D Ω) =
      localizedDerivativeTest e he hei χ hχ hc hs v f :=
  (localizedDerivativeTest e he hei χ hχ hc hs v).extend_eq
    Completion.denseRange_coe (Completion.isUniformInducing_coe _) f

include he hei hχ hc hs in

theorem memW01p_chartPullback_toL2 [NeZero n]
    (hflat : ∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) (u : H1Zero D Ω) :
    Poincare.Analysis.Sobolev.Weak.MemW01p 2
      (chartPullback e (fun y => χ y * toL2 D Ω u y))
      {z : EuclideanSpace ℝ (Fin n) | 0 < z 0} volume := by
  let H : Set (EuclideanSpace ℝ (Fin n)) := {z | 0 < z 0}
  have hH : IsOpen H := isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
  let R := LpToLpRestrictCLM (EuclideanSpace ℝ (Fin n)) ℝ ℝ volume 2 H
  let V := (R.comp (localizedValue e he hei χ hχ hc hs)).comp (toL2 D Ω)
  let G (i : Fin n) := R.comp (localizedDerivative (D := D) (Ω := Ω)
    e he hei χ hχ hc hs (EuclideanSpace.single i 1))
  let F := chartPullback e (fun y => χ y * toL2 D Ω u y)
  have hV : (V u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict H] F :=
    (LpToLpRestrictCLM_coeFn ℝ H _).trans
      (ae_restrict_of_ae (localizedValue_ae e he hei χ hχ hc hs (toL2 D Ω u)))
  obtain ⟨f, hf, -⟩ := exists_energyTest_approximation u
  let φ (j : ℕ) := chartPullback e ((f j).mulSmooth χ hχ)
  have hφc (j : ℕ) : HasCompactSupport (φ j) :=
    hasCompactSupport_chartPullback e ((f j).mulSmooth χ hχ).hasCompactSupport
      (((f j).mulSmooth_support_subset χ hχ).trans hs)
  have hφs (j : ℕ) : ContDiff ℝ ∞ (φ j) :=
    contDiff_chartPullback e he ((f j).mulSmooth χ hχ).smooth
      ((f j).mulSmooth χ hχ).hasCompactSupport
      (((f j).mulSmooth_support_subset χ hχ).trans hs)
  have hφH (j : ℕ) : tsupport (φ j) ⊆ H := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := tsupport_chartPullback_subset_image e
      ((f j).mulSmooth χ hχ).hasCompactSupport
      (((f j).mulSmooth_support_subset χ hχ).trans hs) hz
    have hyt := hs ((f j).mulSmooth_support_subset χ hχ hy)
    apply (hflat _ (e.map_target hyt)).mp
    rw [e.right_inv hyt]
    exact ((f j).mulSmooth χ hχ).support_subset hy
  have hVj (j : ℕ) : (V (f j : H1Zero D Ω) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume.restrict H] φ j := by
    change (R (localizedValue e he hei χ hχ hc hs (toL2 D Ω (f j : H1Zero D Ω))) :
      EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict H] _
    rw [toL2_coe]
    exact (LpToLpRestrictCLM_coeFn ℝ H _).trans
      (ae_restrict_of_ae (localizedValue_test_ae e he hei χ hχ hc hs (f j)))
  have hGj (i : Fin n) (j : ℕ) :
      (G i (f j : H1Zero D Ω) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[volume.restrict H] fun z => fderiv ℝ (φ j) z (EuclideanSpace.single i 1) := by
    change (R (localizedDerivative e he hei χ hχ hc hs (EuclideanSpace.single i 1)
      (f j : H1Zero D Ω)) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict H] _
    rw [localizedDerivative_coe]
    exact (LpToLpRestrictCLM_coeFn ℝ H _).trans
      (ae_restrict_of_ae (localizedDerivativeTest_ae e he hei χ hχ hc hs
        (EuclideanSpace.single i 1) (f j)))
  have hVl : Tendsto (fun j => V (f j : H1Zero D Ω)) atTop (𝓝 (V u)) :=
    V.continuous.continuousAt.tendsto.comp hf
  have hGl (i : Fin n) : Tendsto (fun j => G i (f j : H1Zero D Ω)) atTop (𝓝 (G i u)) :=
    (G i).continuous.continuousAt.tendsto.comp hf
  have hweak (i : Fin n) : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv
      i (G i u) F H := by
    intro ψ hψ hψc hψH
    have hw := Poincare.Analysis.Elliptic.weak_partial_of_tendsto_L2 i hVl (hGl i)
      (fun j θ hθ hθc hθH => ?_) ψ hψ hψc hψH
    · exact (integral_congr_ae (hV.mul EventuallyEq.rfl)).symm.trans hw
    · calc
        _ = ∫ z in H, φ j z * fderiv ℝ θ z (EuclideanSpace.single i 1) :=
          integral_congr_ae ((hVj j).mul EventuallyEq.rfl)
        _ = -(∫ z in H, fderiv ℝ (φ j) z (EuclideanSpace.single i 1) * θ z) :=
          Poincare.Analysis.Elliptic.integral_mul_partial_test hH (hφs j).contDiffOn
            (EuclideanSpace.single i 1) hθ hθc hθH
        _ = _ := congrArg Neg.neg (integral_congr_ae ((hGj i j).mul EventuallyEq.rfl)).symm
  let w : Poincare.Analysis.Sobolev.Weak.MemW1pWitness 2 F H :=
    { memLp := (Lp.memLp (V u)).ae_eq hV
      weakGrad := fun z => WithLp.toLp 2 (fun i => G i u z)
      weakGrad_component_memLp := fun i => Lp.memLp (G i u)
      isWeakGrad := hweak }
  refine ⟨w.memW1p, w, φ, hφs, hφc, hφH, ?_, ?_⟩
  · have hl := hVl.edist (tendsto_const_nhds (x := V u))
    simp only [edist_self] at hl
    apply hl.congr'
    exact Eventually.of_forall fun j => by
      change edist (V (f j : H1Zero D Ω)) (V u) =
        eLpNorm (fun z => φ j z - F z) 2 (volume.restrict H)
      rw [Lp.edist_def]
      exact eLpNorm_congr_ae ((hVj j).sub hV)
  · intro i
    have hl := (hGl i).edist (tendsto_const_nhds (x := G i u))
    simp only [edist_self] at hl
    apply hl.congr'
    exact Eventually.of_forall fun j => by
      change edist (G i (f j : H1Zero D Ω)) (G i u) =
        eLpNorm (fun z => fderiv ℝ (φ j) z (EuclideanSpace.single i 1) - G i u z)
          2 (volume.restrict H)
      rw [Lp.edist_def]
      exact eLpNorm_congr_ae ((hGj i j).sub EventuallyEq.rfl)

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
