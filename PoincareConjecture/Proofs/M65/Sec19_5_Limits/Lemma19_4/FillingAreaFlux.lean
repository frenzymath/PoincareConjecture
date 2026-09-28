import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaCompetitors
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaBoundaryLength
import PoincareConjecture.Proofs.M65.Def18_23_Profile.ScalarInfimum










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M65Filling

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]




theorem radial_flux_integrable (g : RiemannianMetric 3 M)
    {f : LoopPlane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (W : (p : M) → TangentSpace (𝓡 3) p)
    (hW : Continuous (fun p => (⟨p, W p⟩ : TangentBundle (𝓡 3) M))) :
    IntervalIntegrable (fun theta => g.inner (f (Proofs.M58.angularPoint theta))
      (W (f (Proofs.M58.angularPoint theta)))
      (mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (Proofs.M58.angularPoint theta)
        (Proofs.M58.angularPoint theta))) volume (-Real.pi) Real.pi := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hang := Proofs.M58.contDiff_angularPoint.continuous
  have hmem (theta : ℝ) : Proofs.M58.angularPoint theta ∈ loopDiskSet := by
    change ‖Proofs.M58.angularPoint theta - 0‖ ≤ 1
    rw [sub_zero, Proofs.M58.norm_angularPoint]
  have hfcurve : Continuous (fun theta => f (Proofs.M58.angularPoint theta)) :=
    hf.continuousOn.comp_continuous hang hmem
  have harg : Continuous (fun theta =>
      (⟨Proofs.M58.angularPoint theta, Proofs.M58.angularPoint theta⟩ :
        TangentBundle (𝓡 2) LoopPlane)) :=
    (tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp (hang.prodMk hang)
  have hrad : Continuous (fun theta =>
      (⟨f (Proofs.M58.angularPoint theta),
        mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (Proofs.M58.angularPoint theta)
          (Proofs.M58.angularPoint theta)⟩ : TangentBundle (𝓡 3) M)) :=
    (hf.continuousOn_tangentMapWithin le_rfl m65LoopDisk_uniqueMDiffOn).comp_continuous
      harg hmem
  exact ((hW.comp hfcurve).inner_bundle hrad).intervalIntegrable _ _





theorem radial_flux_le_of_residual [T2Space M]
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {gamma : C1FreeLoopSpace (M := M)} (S : M65MinimalDisk g D gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ x, curveVelocity (n := 3) (periodicFreeLoop gamma) x ≠ 0)
    (W H : (p : M) → TangentSpace (𝓡 3) p) {epsilon : ℝ}
    (hresidual : ∀ x, g.tangentNorm (periodicFreeLoop gamma x)
      (W (periodicFreeLoop gamma x) - H (periodicFreeLoop gamma x)) ≤ epsilon)
    (hWI : IntervalIntegrable (fun theta =>
      g.inner (S.disk.map (Proofs.M58.angularPoint theta))
        (W (S.disk.map (Proofs.M58.angularPoint theta)))
        (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet (Proofs.M58.angularPoint theta)
          (Proofs.M58.angularPoint theta))) volume (-Real.pi) Real.pi)
    (hHI : IntervalIntegrable (fun theta =>
      g.inner (S.disk.map (Proofs.M58.angularPoint theta))
        (H (S.disk.map (Proofs.M58.angularPoint theta)))
        (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet (Proofs.M58.angularPoint theta)
          (Proofs.M58.angularPoint theta))) volume (-Real.pi) Real.pi) :
    (∫ theta in (-Real.pi)..Real.pi,
      g.inner (S.disk.map (Proofs.M58.angularPoint theta))
        (W (S.disk.map (Proofs.M58.angularPoint theta)))
        (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet (Proofs.M58.angularPoint theta)
          (Proofs.M58.angularPoint theta))) ≤
      (∫ theta in (-Real.pi)..Real.pi,
        g.inner (S.disk.map (Proofs.M58.angularPoint theta))
          (H (S.disk.map (Proofs.M58.angularPoint theta)))
          (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet (Proofs.M58.angularPoint theta)
            (Proofs.M58.angularPoint theta))) + epsilon * freeLoopLength g gamma := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨lift, _hlift, htrace, _horient⟩ := boundary_lift S hsmooth hregular
  obtain ⟨hNI, hlength⟩ := radial_norm_integral S hsmooth hregular
  have hpoint (theta : ℝ) :
      let p := S.disk.map (Proofs.M58.angularPoint theta)
      let v := mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
        (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta)
      g.inner p (W p) v ≤ g.inner p (H p) v + epsilon * g.tangentNorm p v := by
    dsimp only
    let p := S.disk.map (Proofs.M58.angularPoint theta)
    let v := mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
      (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta)
    have hn : ‖W p - H p‖ ≤ epsilon := by
      change g.tangentNorm p (W p - H p) ≤ epsilon
      dsimp only [p]
      rw [htrace theta]
      exact hresidual (lift theta)
    have hh := (real_inner_le_norm (W p - H p) v).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg v))
    change g.inner p (W p - H p) v ≤ epsilon * g.tangentNorm p v at hh
    rw [map_sub, sub_apply] at hh
    exact sub_le_iff_le_add'.mp hh
  have hle := intervalIntegral.integral_mono_on
    (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi) hWI (hHI.add (hNI.const_mul epsilon))
    (fun theta _ => hpoint theta)
  rw [intervalIntegral.integral_add hHI (hNI.const_mul epsilon),
    intervalIntegral.integral_const_mul, hlength] at hle
  exact hle




theorem scalar_area_lower_bound [CompactSpace M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b)) {q : ℝ} (hq : q ∈ Icc a b)
    {gamma : C1FreeLoopSpace (M := M)}
    (S : M65MinimalDisk (F.metric q) (F.connection q) gamma) :
    IntegrableOn (fun z => (F.connection q).scalarCurvature (S.disk.map z) *
      m60AreaDensity (F.metric q) S.disk.map z / 2) loopDiskSet volume ∧
    flowScalarCurvatureInfimum F q * fillingArea (F.metric q) gamma / 2 ≤
      ∫ z in loopDiskSet, (F.connection q).scalarCurvature (S.disk.map z) *
        m60AreaDensity (F.metric q) S.disk.map z / 2 := by
  have hR : Continuous (F.connection q).scalarCurvature :=
    (F.contMDiff_scalarCurvature q hq).continuous
  have hA := m65Attainment_area_integrable (F.metric q) S.boundary_regular
  have hI : IntegrableOn (fun z => (F.connection q).scalarCurvature (S.disk.map z) *
      m60AreaDensity (F.metric q) S.disk.map z / 2) loopDiskSet volume :=
    (IntegrableOn.continuousOn_mul
      (hR.comp_continuousOn S.boundary_regular.continuousOn) hA
      (isCompact_closedBall (0 : LoopPlane) 1)).div_const 2
  have hbelow : BddBelow (range (F.connection q).scalarCurvature) :=
    (isCompact_range hR).bddBelow
  have hmin (p : M) : flowScalarCurvatureInfimum F q ≤
      (F.connection q).scalarCurvature p := csInf_le hbelow (mem_range_self p)
  have hle := integral_mono ((hA.const_mul (flowScalarCurvatureInfimum F q)).div_const 2) hI
    (fun z => div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hmin (S.disk.map z)) (Real.sqrt_nonneg _)) (by norm_num))
  rw [integral_div, integral_const_mul] at hle
  change flowScalarCurvatureInfimum F q * S.disk.area / 2 ≤ _ at hle
  rw [S.area_eq] at hle
  exact ⟨hI, hle⟩

end PoincareConjecture.M65Filling
