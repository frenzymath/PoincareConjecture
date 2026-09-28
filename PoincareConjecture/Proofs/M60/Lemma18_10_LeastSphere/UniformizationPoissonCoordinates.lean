import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationPoisson











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

universe u

namespace PoincareConjecture.M60

open LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Omega : Set M}

private theorem memLp_on_compact {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContinuousOn F K) :
    MemLp F 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  exact MemLp.of_bound (hF.aestronglyMeasurable hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono fun x hx => hC x hx)




theorem gradient_pairing_compact_coordinates
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (u : H1Zero D Omega)
    {phi : EuclideanSpace ℝ (Fin n) → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ e.source ∩ e ⁻¹' Omega)
    (hphiK : tsupport phi ⊆ K) :
    (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) u x *
      fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ⟪u, (EnergyTest.ofCoordinates (D := D) e hei phi hphi hc hs : H1Zero D Omega)⟫_ℝ -
        ⟪toL2 D Omega u, testToL2 D Omega
          (EnergyTest.ofCoordinates e hei phi hphi hc hs)⟫_ℝ := by
  let T (j : Fin n) := coordinateDerivative (D := D) (Ω := Omega) e he hei hK hKs
    (EuclideanSpace.single j 1)
  let psi (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :=
    divergenceCoefficients g e x i j * fderiv ℝ phi x (EuclideanSpace.single i 1)
  have hpsi (i j : Fin n) : MemLp (psi i j) 2 (volume.restrict K) :=
    memLp_on_compact hK (((contDiffOn_divergenceCoefficients e he hei i j).continuousOn.mono
      hKs).mul (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn))
  have hint (w : H1Zero D Omega) (i j : Fin n) :
      Integrable (fun x => T j w x * psi i j x) (volume.restrict K) :=
    (Lp.memLp (T j w)).integrable_mul (hpsi i j)
  have heq (w : H1Zero D Omega) :
      (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j w x *
        fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∑ i, ∑ j, ∫ x in K, T j w x * psi i j x := by
    calc
      _ = ∫ x in K, ∑ i, ∑ j, T j w x * psi i j x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          dsimp [psi]
          ring
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint w i j))]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hint w i j)
  obtain ⟨f, hf, -⟩ := exists_energyTest_approximation u
  have hlim (i j : Fin n) := Poincare.Analysis.Elliptic.tendsto_integral_mul_L2
    ((T j).continuous.continuousAt.tendsto.comp hf) (hpsi i j)
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hlim i j
  let h : EnergyTest D Omega := EnergyTest.ofCoordinates e hei phi hphi hc hs
  have hh : tsupport (h : M → ℝ) ⊆ e '' K :=
    (tsupport_coordinateExtension_subset_image e hc (hs.trans inter_subset_left)).trans
      (image_mono hphiK)
  have hseq (k : ℕ) :
      (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j (f k) x *
        fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ y, g.inner y (D.gradient (f k) y) (D.gradient h y) ∂g.volumeMeasure := by
    rw [integral_gradient_eq_compact_coordinates e he hei hK hKs (f k) h hh]
    have hae : ∀ᵐ x ∂volume.restrict K, ∀ j : Fin n,
        T j (f k) x = fderiv ℝ (fun y => f k (e y)) x (EuclideanSpace.single j 1) := by
      apply ae_all_iff.mpr
      intro j
      change (coordinateDerivative (D := D) (Ω := Omega) e he hei hK hKs _
        (f k : H1Zero D Omega) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict K] _
      rw [coordinateDerivative_coe]
      exact EnergyTest.coordinateDerivativeL2_ae e he hK hKs _ (f k)
    apply integral_congr_ae
    filter_upwards [hae, ae_restrict_mem hK.measurableSet] with x hx hxK
    simp_rw [hx]
    have hd := (EnergyTest.ofCoordinates_comp_eventuallyEq (D := D)
      e hei phi hphi hc hs (hKs hxK)).fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (fun y => h (e y)) x = fderiv ℝ phi x at hd
    rw [← hd, ← density_mul_inner_gradient_eq_sum_divergenceCoefficients e he hei
      (f k) h (hKs hxK), mul_comm]
  have hsum' : Tendsto (fun k =>
      ∫ y, g.inner y (D.gradient (f k) y) (D.gradient h y) ∂g.volumeMeasure) atTop
      (𝓝 (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j * T j u x *
        fderiv ℝ phi x (EuclideanSpace.single i 1))) := by
    rw [heq]
    exact hsum.congr' (Eventually.of_forall fun k => (heq (f k)).symm.trans (hseq k))
  have hfL2 : Tendsto (fun k => testToL2 D Omega (f k)) atTop (𝓝 (toL2 D Omega u)) := by
    simpa only [Function.comp_def, toL2_coe] using
      (toL2 D Omega).continuous.continuousAt.tendsto.comp hf
  have henergy := (hf.inner (𝕜 := ℝ) (tendsto_const_nhds (x := (h : H1Zero D Omega)))).sub
    (hfL2.inner (𝕜 := ℝ) (tendsto_const_nhds (x := testToL2 D Omega h)))
  have hident (k) : ⟪(f k : H1Zero D Omega), (h : H1Zero D Omega)⟫_ℝ -
      ⟪testToL2 D Omega (f k), testToL2 D Omega h⟫_ℝ =
      ∫ x, g.inner x (D.gradient (f k) x) (D.gradient h x) ∂g.volumeMeasure := by
    rw [UniformSpace.Completion.inner_coe, EnergyTest.inner_eq, energyInner,
      testToL2_inner, add_sub_cancel_left]
  simp only [hident] at henergy
  exact tendsto_nhds_unique hsum' henergy



theorem weakPoisson_divergence_compact
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKs : K ⊆ e.source)
    (u : H1Zero D Omega) (F : Lp ℝ 2 g.volumeMeasure)
    (hforce : ∀ v : H1Zero D Omega,
      ⟪u, v⟫_ℝ - ⟪toL2 D Omega u, toL2 D Omega v⟫_ℝ = ⟪F, toL2 D Omega v⟫_ℝ)
    {phi : EuclideanSpace ℝ (Fin n) → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ e.source ∩ e ⁻¹' Omega)
    (hphiK : tsupport phi ⊆ K) :
    (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) u x *
      fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ x in K, phi x * F (e x) * g.pullbackVolumeDensity e x := by
  let h : EnergyTest D Omega := EnergyTest.ofCoordinates e hei phi hphi hc hs
  have hh : tsupport (h : M → ℝ) ⊆ e '' K :=
    (tsupport_coordinateExtension_subset_image e hc (hs.trans inter_subset_left)).trans
      (image_mono hphiK)
  rw [gradient_pairing_compact_coordinates e he hei hK hKs u hphi hc hs hphiK]
  change ⟪u, (h : H1Zero D Omega)⟫_ℝ - ⟪toL2 D Omega u, testToL2 D Omega h⟫_ℝ = _
  rw [← toL2_coe, hforce, toL2_coe, ← integral_test_mul,
    integral_test_eq_compact_coordinates e he hei hK hKs F h hh]
  apply setIntegral_congr_fun hK.measurableSet
  intro x hx
  dsimp only
  rw [show h (e x) = phi x from EnergyTest.ofCoordinates_apply e hei phi hphi hc hs (hKs hx)]



theorem weakPoisson_divergence_local
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K O : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hOK : O ⊆ K) (hOOmega : e '' O ⊆ Omega)
    (u : H1Zero D Omega) (F : Lp ℝ 2 g.volumeMeasure)
    (hforce : ∀ v : H1Zero D Omega,
      ⟪u, v⟫_ℝ - ⟪toL2 D Omega u, toL2 D Omega v⟫_ℝ = ⟪F, toL2 D Omega v⟫_ℝ)
    {phi : EuclideanSpace ℝ (Fin n) → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O) :
    (∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) u x *
      fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ x in O, (g.pullbackVolumeDensity e x * F (e x)) * phi x := by
  have hs' : tsupport phi ⊆ e.source ∩ e ⁻¹' Omega :=
    fun x hx => ⟨hKs (hOK (hs hx)), hOOmega (mem_image_of_mem e (hs hx))⟩
  have hcompact := weakPoisson_divergence_compact e he hei hK hKs u F hforce
    hphi hc hs' (hs.trans hOK)
  have hleft : (∫ x in K, ∑ i, ∑ j, divergenceCoefficients g e x i j *
      coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) u x *
      fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
        localCoordinateDerivative e he hei hK hKs hOK (EuclideanSpace.single j 1) u x *
        fderiv ℝ phi x (EuclideanSpace.single i 1) := by
    calc
      _ = ∫ x in O, ∑ i, ∑ j, divergenceCoefficients g e x i j *
          coordinateDerivative e he hei hK hKs (EuclideanSpace.single j 1) u x *
          fderiv ℝ phi x (EuclideanSpace.single i 1) := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hK.measurableSet hOK
        intro x hx
        have hd (i : Fin n) : fderiv ℝ phi x (EuclideanSpace.single i 1) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y => fderiv ℝ phi y (EuclideanSpace.single i 1))
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
  have hright : (∫ x in K, phi x * F (e x) * g.pullbackVolumeDensity e x) =
      ∫ x in O, phi x * F (e x) * g.pullbackVolumeDensity e x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hK.measurableSet hOK
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport (fun ht => hx.2 (hs ht)), zero_mul]
  rw [hleft, hright] at hcompact
  rw [hcompact]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end PoincareConjecture.M60
