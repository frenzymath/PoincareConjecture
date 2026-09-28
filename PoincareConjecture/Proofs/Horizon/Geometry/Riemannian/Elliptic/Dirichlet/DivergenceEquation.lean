import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateWeakDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateTest
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem tendsto_gradient_pairing_of_weakEigen
    (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ)
    {f : ℕ → EnergyTest D Ω}
    (hf : Tendsto (fun k => (f k : H1Zero D Ω)) atTop (𝓝 u))
    (h : EnergyTest D Ω) :
    Tendsto (fun k => ∫ x, g.inner x (D.gradient (f k) x) (D.gradient h x)
      ∂g.volumeMeasure) atTop
      (𝓝 (lambda * ∫ x, h x * toL2 D Ω u x ∂g.volumeMeasure)) := by
  have hfL2 : Tendsto (fun k => testToL2 D Ω (f k)) atTop (𝓝 (toL2 D Ω u)) := by
    simpa only [Function.comp_def, toL2_coe] using
      (toL2 D Ω).continuous.continuousAt.tendsto.comp hf
  have ht := (hf.inner (𝕜 := ℝ) (tendsto_const_nhds (x := (h : H1Zero D Ω)))).sub
    (hfL2.inner (𝕜 := ℝ) (tendsto_const_nhds (x := testToL2 D Ω h)))
  have hseq (k) : ⟪(f k : H1Zero D Ω), (h : H1Zero D Ω)⟫_ℝ -
      ⟪testToL2 D Ω (f k), testToL2 D Ω h⟫_ℝ =
      ∫ x, g.inner x (D.gradient (f k) x) (D.gradient h x) ∂g.volumeMeasure := by
    rw [UniformSpace.Completion.inner_coe, EnergyTest.inner_eq, energyInner,
      testToL2_inner, add_sub_cancel_left]
  have hlim : ⟪u, (h : H1Zero D Ω)⟫_ℝ - ⟪toL2 D Ω u, testToL2 D Ω h⟫_ℝ =
      lambda * ∫ x, h x * toL2 D Ω u x ∂g.volumeMeasure := by
    rw [heigen, toL2_coe, integral_test_mul]
    ring
  simpa only [hseq, hlim] using ht

theorem integral_gradient_eq_compact_coordinates
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (f h : EnergyTest D Ω) (hh : tsupport (h : M → ℝ) ⊆ e '' K) :
    (∫ y, g.inner y (D.gradient f y) (D.gradient h y) ∂g.volumeMeasure) =
      ∫ x in K, g.inner (e x) (D.gradient f (e x)) (D.gradient h (e x)) *
        g.pullbackVolumeDensity e x := by
  rw [← integral_compact_image_eq_pullback_density (g := g) e he hei hK hKs
    (D.continuous_inner_gradient f.smooth h.smooth).measurable]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [D.gradient_eq_zero_of_notMem_tsupport (fun ht => hy (hh ht)), map_zero]

theorem integral_test_eq_compact_coordinates
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (v : Lp ℝ 2 g.volumeMeasure) (h : EnergyTest D Ω)
    (hh : tsupport (h : M → ℝ) ⊆ e '' K) :
    (∫ y, h y * v y ∂g.volumeMeasure) =
      ∫ x in K, h (e x) * v (e x) * g.pullbackVolumeDensity e x := by
  calc
    _ = ∫ y in e '' K, h y * v y ∂g.volumeMeasure := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hy (hh ht)), zero_mul]
    _ = _ := integral_compact_image_eq_pullback_density (g := g) e he hei hK hKs
      (h.smooth.continuous.measurable.mul (Lp.stronglyMeasurable v).measurable)

private theorem memLp_on_compact {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContinuousOn F K) :
    MemLp F 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  exact MemLp.of_bound (hF.aestronglyMeasurable hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono fun x hx => hC x hx)

theorem weakEigen_divergence_compact
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω)
    (hφK : tsupport φ ⊆ K) :
    (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) u x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      lambda * ∫ x in K, φ x * toL2 D Ω u (e x) * g.pullbackVolumeDensity e x := by
  let T (j : Fin n) := coordinateDerivative (D := D) (Ω := Ω) e he hei hK hKs
    (EuclideanSpace.single j 1)
  let ψ (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :=
    divergenceCoefficients g e x i j * fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ (i j : Fin n) : MemLp (ψ i j) 2 (volume.restrict K) :=
    memLp_on_compact hK (((contDiffOn_divergenceCoefficients e he hei i j).continuousOn.mono
      hKs).mul (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn))
  have hint (w : H1Zero D Ω) (i j : Fin n) :
      Integrable (fun x => T j w x * ψ i j x) (volume.restrict K) :=
    (Lp.memLp (T j w)).integrable_mul (hψ i j)
  have heq (w : H1Zero D Ω) :
      (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j w x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∑ i, ∑ j, ∫ x in K, T j w x * ψ i j x := by
    calc
      _ = ∫ x in K, ∑ i, ∑ j, T j w x * ψ i j x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          dsimp [ψ]
          ring
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint w i j))]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hint w i j)
  obtain ⟨f, hf, -⟩ := exists_energyTest_approximation u
  have hlim (i j : Fin n) := Poincare.Analysis.Elliptic.tendsto_integral_mul_L2
    ((T j).continuous.continuousAt.tendsto.comp hf) (hψ i j)
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hlim i j
  let h : EnergyTest D Ω := EnergyTest.ofCoordinates e hei φ hφ hc hs
  have hh : tsupport (h : M → ℝ) ⊆ e '' K :=
    (tsupport_coordinateExtension_subset_image e hc (hs.trans inter_subset_left)).trans
      (image_mono hφK)
  have hseq (k : ℕ) :
      (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j (f k) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ y, g.inner y (D.gradient (f k) y) (D.gradient h y) ∂g.volumeMeasure := by
    rw [integral_gradient_eq_compact_coordinates e he hei hK hKs (f k) h hh]
    have hae : ∀ᵐ x ∂volume.restrict K, ∀ j : Fin n,
        T j (f k) x = fderiv ℝ (fun y => f k (e y)) x (EuclideanSpace.single j 1) := by
      apply ae_all_iff.mpr
      intro j
      change (coordinateDerivative (D := D) (Ω := Ω) e he hei hK hKs _ (f k : H1Zero D Ω) :
        EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict K] _
      rw [coordinateDerivative_coe]
      exact EnergyTest.coordinateDerivativeL2_ae e he hK hKs _ (f k)
    apply integral_congr_ae
    filter_upwards [hae, ae_restrict_mem hK.measurableSet] with x hx hxK
    simp_rw [hx]
    have hd := (EnergyTest.ofCoordinates_comp_eventuallyEq (D := D)
      e hei φ hφ hc hs (hKs hxK)).fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (fun y => h (e y)) x = fderiv ℝ φ x at hd
    rw [← hd, ← density_mul_inner_gradient_eq_sum_divergenceCoefficients e he hei
      (f k) h (hKs hxK), mul_comm]
  have hsum' : Tendsto (fun k =>
      ∫ y, g.inner y (D.gradient (f k) y) (D.gradient h y) ∂g.volumeMeasure) atTop
      (𝓝 (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j u x *
        fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    rw [heq]
    exact hsum.congr' (Eventually.of_forall fun k => (heq (f k)).symm.trans (hseq k))
  have hright : (∫ y, h y * toL2 D Ω u y ∂g.volumeMeasure) =
      ∫ x in K, φ x * toL2 D Ω u (e x) * g.pullbackVolumeDensity e x := by
    rw [integral_test_eq_compact_coordinates e he hei hK hKs (toL2 D Ω u) h hh]
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    dsimp only
    rw [show h (e x) = φ x from EnergyTest.ofCoordinates_apply e hei φ hφ hc hs (hKs hx)]
  have henergy := tendsto_gradient_pairing_of_weakEigen u lambda heigen hf h
  rw [hright] at henergy
  exact tendsto_nhds_unique hsum' henergy

theorem weakEigen_divergence_local
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K) (hOΩ : e '' O ⊆ Ω)
    (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) u x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in O, (lambda * g.pullbackVolumeDensity e x) * toL2 D Ω u (e x) * φ x := by
  have hs' : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω :=
    fun x hx => ⟨hKs (hOK (hs hx)), hOΩ (mem_image_of_mem e (hs hx))⟩
  have hcompact := weakEigen_divergence_compact e he hei hK hKs u lambda heigen
    hφ hc hs' (hs.trans hOK)
  have hleft : (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) u x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
        localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) u x *
        fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    calc
      _ = ∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
          coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) u x *
          fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hK.measurableSet hOK
        intro x hx
        have hd (i : Fin n) : fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 :=
          image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
            (fun ht => hx.2 (hs (tsupport_fderiv_apply_subset ℝ _ ht)))
        simp only [hd, mul_zero, Finset.sum_const_zero]
      _ = _ := by
        have hae : ∀ᵐ x ∂volume.restrict O, ∀ j : Fin n,
            localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) u x =
              coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) u x := by
          apply ae_all_iff.mpr
          intro j
          exact Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
            (by simpa only [one_smul] using Measure.restrict_mono hOK (le_refl volume)) _
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        simp only [hx]
  have hright : (∫ x in K, φ x * toL2 D Ω u (e x) * g.pullbackVolumeDensity e x) =
      ∫ x in O, φ x * toL2 D Ω u (e x) * g.pullbackVolumeDensity e x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hK.measurableSet hOK
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport (fun ht => hx.2 (hs ht)), zero_mul]
  rw [hleft, hright] at hcompact
  rw [hcompact, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end PoincareConjecture.LeviCivitaData.Dirichlet
