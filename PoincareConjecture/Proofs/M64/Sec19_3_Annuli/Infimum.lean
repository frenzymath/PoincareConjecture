import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}





theorem m60AreaDensity_eq_zero_of_factor (g : RiemannianMetric n M)
    (c : ℝ → M) (psi : LoopPlane → ℝ) (z : LoopPlane)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) c (psi z))
    (hpsi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) psi z) :
    m60AreaDensity g (c ∘ psi) z = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let w := mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (psi z) (1 : ℝ)
  have hcol (i : Fin 2) :
      mfderiv (𝓡 2) (𝓡 n) (c ∘ psi) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        (fderiv ℝ psi z
          (EuclideanSpace.basisFun (Fin 2) ℝ i) : ℝ) • w := by
    have hvalue :
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) psi z
            (EuclideanSpace.basisFun (Fin 2) ℝ i) =
          (fderiv ℝ psi z (EuclideanSpace.basisFun (Fin 2) ℝ i) : ℝ) := by
      rw [mfderiv_eq_fderiv]
      rfl
    have hcomp := mfderiv_comp_apply (f := psi) (g := c) z hc hpsi
      (EuclideanSpace.basisFun (Fin 2) ℝ i)
    have hs : (fderiv ℝ psi z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) : ℝ) • (1 : ℝ) =
        fderiv ℝ psi z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by simp
    calc
      mfderiv (𝓡 2) (𝓡 n) (c ∘ psi) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i) =
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (psi z))
            (fderiv ℝ psi z (EuclideanSpace.basisFun (Fin 2) ℝ i)) :=
        hcomp.trans (congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (psi z)) hvalue)
      _ = (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (psi z))
            ((fderiv ℝ psi z (EuclideanSpace.basisFun (Fin 2) ℝ i)) • (1 : ℝ)) := by
        rw [hs]
      _ = (fderiv ℝ psi z (EuclideanSpace.basisFun (Fin 2) ℝ i)) • w := by
        change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (psi z))
            ((fderiv ℝ psi z (EuclideanSpace.basisFun (Fin 2) ℝ i)) • (1 : ℝ)) =
          (fderiv ℝ psi z (EuclideanSpace.basisFun (Fin 2) ℝ i)) •
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (psi z)) (1 : ℝ)
        exact (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (psi z)).map_smul
          (fderiv ℝ psi z (EuclideanSpace.basisFun (Fin 2) ℝ i)) (1 : ℝ)
  have hdet : Matrix.det (m60AreaGram g (c ∘ psi) z) = 0 := by
    rw [Matrix.det_fin_two, m60AreaGram_symm g (c ∘ psi) z 1 0]
    simp only [m60AreaGram]
    rw [hcol 0, hcol 1]
    simp only [Function.comp_apply]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  simp only [m60AreaDensity, hdet, max_self, Real.sqrt_zero]





theorem m64AnnulusArea_nonneg (f : LoopPlane → M) :
    0 ≤ m64AnnulusArea g f :=
  integral_nonneg (fun _ => Real.sqrt_nonneg _)




theorem m64AnnulusDomain_measurableSet :
    MeasurableSet m64AnnulusDomain := by
  change MeasurableSet {p : LoopPlane |
    0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}
  measurability





theorem m64AnnulusDomain_isCompact : IsCompact m64AnnulusDomain := by
  have hmap : Continuous (fun p : ℝ × ℝ => annulusPoint p.1 p.2) := by
    unfold annulusPoint
    fun_prop
  have heq : m64AnnulusDomain =
      (fun p : ℝ × ℝ => annulusPoint p.1 p.2) ''
        (Icc 0 curvePeriod ×ˢ Icc (0 : ℝ) 1) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z 0, z 1), ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩, ?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image hmap




theorem m64AnnulusDomain_volume_ne_top :
    volume m64AnnulusDomain ≠ (⊤ : ENNReal) :=
  m64AnnulusDomain_isCompact.measure_ne_top





theorem M64Annulus.area_le_energy (A : M64Annulus g c0 c1)
    (hmeas : MeasurableSet m64AnnulusDomain)
    (hE : IntegrableOn (m60EnergyDensity g A.map) m64AnnulusDomain volume) :
    A.area ≤ ∫ p in m64AnnulusDomain,
      m60EnergyDensity g A.map p := by
  unfold M64Annulus.area m64AnnulusArea
  exact MeasureTheory.setIntegral_mono_on A.area_integrable hE hmeas
    (fun p _ => m60AreaDensity_le_energyDensity g A.map p)




theorem M64Annulus.area_nonneg (A : M64Annulus g c0 c1) : 0 ≤ A.area :=
  m64AnnulusArea_nonneg A.map




theorem m64AnnulusAreaRange_nonempty (A : M64Annulus g c0 c1) :
    (m64AnnulusAreaRange g c0 c1).Nonempty :=
  ⟨A.area, A, rfl⟩




theorem m64AnnulusAreaRange_bddBelow (g : RiemannianMetric n M) (c0 c1 : ℝ → M) :
    BddBelow (m64AnnulusAreaRange g c0 c1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨A, rfl⟩
  exact A.area_nonneg




theorem m64LeastAnnulusArea_nonneg (A : M64Annulus g c0 c1) :
    0 ≤ m64LeastAnnulusArea g c0 c1 := by
  have hnonempty := m64AnnulusAreaRange_nonempty A
  have hbounded := m64AnnulusAreaRange_bddBelow g c0 c1
  apply le_csInf hnonempty
  rintro _ ⟨B, rfl⟩
  exact B.area_nonneg




theorem m64LeastAnnulusArea_le_annulus (A : M64Annulus g c0 c1) :
    m64LeastAnnulusArea g c0 c1 ≤ A.area :=
  csInf_le (m64AnnulusAreaRange_bddBelow g c0 c1) ⟨A, rfl⟩




theorem m64LeastAnnulusArea_eq_of_isLeast
    (B : M64Annulus g c0 c1)
    (hB : ∀ C : M64Annulus g c0 c1, B.area ≤ C.area) :
    B.area = m64LeastAnnulusArea g c0 c1 := by
  refine le_antisymm ?_ (m64LeastAnnulusArea_le_annulus B)
  apply le_csInf (m64AnnulusAreaRange_nonempty B)
  rintro _ ⟨C, rfl⟩
  exact hB C





theorem m64LeastAnnulusArea_near_minimizer (A : M64Annulus g c0 c1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ B : M64Annulus g c0 c1,
      B.area < m64LeastAnnulusArea g c0 c1 + epsilon := by
  have hnonempty := m64AnnulusAreaRange_nonempty A
  have hbounded := m64AnnulusAreaRange_bddBelow g c0 c1
  obtain ⟨_, ⟨B, rfl⟩, hB⟩ := exists_lt_of_csInf_lt hnonempty
    (show m64LeastAnnulusArea g c0 c1 <
      m64LeastAnnulusArea g c0 c1 + epsilon from lt_add_of_pos_right _ hepsilon)
  exact ⟨B, hB⟩

end PoincareConjecture
