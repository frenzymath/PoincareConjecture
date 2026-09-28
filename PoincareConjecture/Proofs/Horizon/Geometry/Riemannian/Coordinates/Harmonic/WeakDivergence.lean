import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Minimization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.DivergenceEquation

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem gradientEnergy_eq_divergence_compact
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (u : H1Zero D Ω)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω)
    (hφK : tsupport φ ⊆ K) :
    (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) u x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      gradientEnergy D Ω u (EnergyTest.ofCoordinates (D := D) e hei φ hφ hc hs) := by
  let T (j : Fin n) := coordinateDerivative (D := D) (Ω := Ω) e he hei hK hKs
    (EuclideanSpace.single j 1)
  let ψ (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :=
    divergenceCoefficients g e x i j * fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hψ (i j : Fin n) : MemLp (ψ i j) 2 (volume.restrict K) := by
    have hcont : ContinuousOn (ψ i j) K :=
      ((contDiffOn_divergenceCoefficients e he hei i j).continuousOn.mono hKs).mul
        (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn)
    let : IsFiniteMeasure (volume.restrict K) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hK.measure_lt_top⟩
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
    exact MemLp.of_bound (hcont.aestronglyMeasurable hK.measurableSet) C
      ((ae_restrict_mem hK.measurableSet).mono fun x hx => hC x hx)
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
      gradientEnergy D Ω (f k) h := by
    rw [gradientEnergy_coe, integral_gradient_eq_compact_coordinates e he hei hK hKs (f k) h hh]
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
  have hsum' : Tendsto (fun k => gradientEnergy D Ω (f k) h) atTop
      (𝓝 (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j u x *
        fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
    rw [heq]
    exact hsum.congr' (Eventually.of_forall fun k => (heq (f k)).symm.trans (hseq k))
  have hcont : Continuous (fun w : H1Zero D Ω => gradientEnergy D Ω w h) := by fun_prop
  exact tendsto_nhds_unique hsum' (hcont.continuousAt.tendsto.comp hf)

theorem weakPoisson_replacement_divergence_compact [PreconnectedSpace M]
    {Ω' : Set M} (hΩ : Ω ⊆ Ω') {P : ℝ} (hP0 : 0 ≤ P)
    (hP : HasTestPoincare D Ω P) (q : EnergyTest D Ω')
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω)
    (hφK : tsupport φ ⊆ K) :
    (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1)
        ((q : H1Zero D Ω') + inclusion hΩ (weakPoisson D Ω hP0 hP q.laplacianLp)) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0 := by
  have hs' : tsupport φ ⊆ e.source ∩ e ⁻¹' Ω' :=
    fun x hx => ⟨(hs hx).1, hΩ (hs hx).2⟩
  have h := gradientEnergy_eq_divergence_compact e he hei hK hKs
    ((q : H1Zero D Ω') + inclusion hΩ (weakPoisson D Ω hP0 hP q.laplacianLp))
    hφ hc hs' hφK
  have hext : EnergyTest.ofCoordinates (D := D) e hei φ hφ hc hs' =
      testInclusion hΩ (EnergyTest.ofCoordinates (D := D) e hei φ hφ hc hs) := by
    rfl
  rw [hext, ← inclusion_coe] at h
  exact h.trans (weakPoisson_gradientEnergy_orthogonal hΩ hP0 hP q _)

theorem divergence_integral_eq_local
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K) (u : H1Zero D Ω)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hs : tsupport φ ⊆ O) :
    (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
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

theorem weakPoisson_replacement_divergence_local [PreconnectedSpace M]
    {Ω' : Set M} (hΩ : Ω ⊆ Ω') {P : ℝ} (hP0 : 0 ≤ P)
    (hP : HasTestPoincare D Ω P) (q : EnergyTest D Ω')
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K) (hOΩ : e '' O ⊆ Ω)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ O) :
    (∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1)
        ((q : H1Zero D Ω') + inclusion hΩ (weakPoisson D Ω hP0 hP q.laplacianLp)) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0 := by
  rw [← divergence_integral_eq_local e he hei hK hKs hOK _ hs]
  exact weakPoisson_replacement_divergence_compact hΩ hP0 hP q e he hei hK hKs hφ hc
    (fun x hx => ⟨hKs (hOK (hs hx)), hOΩ (mem_image_of_mem e (hs hx))⟩) (hs.trans hOK)

end PoincareConjecture.LeviCivitaData.Dirichlet
