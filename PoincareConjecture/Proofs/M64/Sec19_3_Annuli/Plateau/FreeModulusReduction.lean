import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusAnnulusMinimizer
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedAnnulusEnergyIdentity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum














set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => m64AnnulusDomain



noncomputable def m64ClassicalWeightedGramEnergy
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) (r : ℝ) : ℝ :=
  ∫ p in S, (r * m60AreaGram g A.map p 0 0 +
    r⁻¹ * m60AreaGram g A.map p 1 1) / 2



def m64ClassicalWeightedGramEnergyRange
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) : Set ℝ :=
  {x | ∃ (r : ℝ), 0 < r ∧ ∃ A : M64Annulus g c0 c1,
    IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
      r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume ∧
      x = m64ClassicalWeightedGramEnergy g A r}





def M64ConformalModulusApproximation
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) : Prop :=
  ∀ A : M64Annulus g c0 c1, ∀ ε : ℝ, 0 < ε →
    ∃ r : ℝ, 0 < r ∧ ∃ A' : M64Annulus g c0 c1,
      IntegrableOn (fun p => (r * m60AreaGram g A'.map p 0 0 +
        r⁻¹ * m60AreaGram g A'.map p 1 1) / 2) S volume ∧
      m64ClassicalWeightedGramEnergy g A' r ≤ A.area + ε





def M64WeightedModulusConfinement
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) (lo hi : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ A : M64Annulus g c0 c1,
    IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
      r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume →
    m64ClassicalWeightedGramEnergy g A r < m64LeastAnnulusArea g c0 c1 + 1 →
    r ∈ Icc lo hi



theorem m64LeastAnnulusArea_eq_classicalWeightedGramEnergy_sInf
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A0 : M64Annulus g c0 c1)
    (hconf : M64ConformalModulusApproximation g c0 c1) :
    m64LeastAnnulusArea g c0 c1 =
      sInf (m64ClassicalWeightedGramEnergyRange g c0 c1) := by
  have hne : (m64ClassicalWeightedGramEnergyRange g c0 c1).Nonempty := by
    obtain ⟨r, hr, A, hA, hle⟩ := hconf A0 1 one_pos
    exact ⟨m64ClassicalWeightedGramEnergy g A r, ⟨r, hr, A, hA, rfl⟩⟩
  have hbelow : BddBelow (m64ClassicalWeightedGramEnergyRange g c0 c1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, hr, A, hA, rfl⟩
    unfold m64ClassicalWeightedGramEnergy
    apply integral_nonneg
    intro p
    have h00 := m60AreaGram_diagonal_nonneg g A.map p 0
    have h11 := m60AreaGram_diagonal_nonneg g A.map p 1
    exact div_nonneg (add_nonneg (mul_nonneg hr.le h00)
      (mul_nonneg (inv_nonneg.mpr hr.le) h11)) (by norm_num)
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨r, hr, A, hA, rfl⟩
    exact (m64LeastAnnulusArea_le_annulus A).trans
      (A.area_le_weightedGramEnergy hr hA)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨A, hA⟩ := m64LeastAnnulusArea_near_minimizer A0 (half_pos hε)
    obtain ⟨r, hr, A', hA'int, hweighted⟩ := hconf A (ε / 2) (half_pos hε)
    have hlt : m64ClassicalWeightedGramEnergy g A' r <
        m64LeastAnnulusArea g c0 c1 + ε := by
      have := hweighted
      dsimp only [m64ClassicalWeightedGramEnergy] at this ⊢
      linarith
    have hle := csInf_le hbelow ⟨r, hr, A', hA'int, rfl⟩
    exact (hle.trans_lt hlt).le

variable [CompactSpace M] [T2Space M]





theorem m64LeastAnnulusArea_attained_of_freeModulus_certificates
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A0 : M64Annulus g c0 c1)
    (hconf : M64ConformalModulusApproximation g c0 c1)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hconfine : M64WeightedModulusConfinement g c0 c1 lo hi)
    (hadmit : ∀ {m : ℕ} (e : M → EuclideanSpace ℝ (Fin m))
      (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (r : ℝ)
      (L : M64ObservedWeakAnnulus (n := n) e c0 c1),
      r ∈ Icc lo hi → ContinuousOn L.map (interior m64AnnulusDomain) →
      ∃ A : M64Annulus g c0 c1,
        A.area = L.weightedEnergy B r) :
    ∃ A : M64Annulus g c0 c1, A.area = m64LeastAnnulusArea g c0 c1 := by
  obtain ⟨m, e, he, hei, hread⟩ := M60.suCompactObservation_exists
    (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨W0, -, -⟩ := m64ObservedWeakAnnulus_of_annulus A0 e he1
  obtain ⟨B, r, hr, L, hB, hpos, hsymm, hgram, hLcont, hmin⟩ :=
    m64ObservedWeakAnnulus_exists_continuous_modulus_minimizer
      g e he1 hei hread hlo hlohi W0
  obtain ⟨Astar, hAstar⟩ := hadmit e B r L hr hLcont
  have hLlower : m64LeastAnnulusArea g c0 c1 ≤ L.weightedEnergy B r := by
    rw [← hAstar]
    exact m64LeastAnnulusArea_le_annulus Astar
  have hLupper : L.weightedEnergy B r ≤ m64LeastAnnulusArea g c0 c1 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := min (ε / 2) 1
    have hδ : 0 < δ := lt_min (half_pos hε) zero_lt_one
    obtain ⟨A, hA⟩ := m64LeastAnnulusArea_near_minimizer A0 (half_pos hδ)
    obtain ⟨s, hs, A', hA'int, hweighted⟩ := hconf A (δ / 2) (half_pos hδ)
    have hnear : m64ClassicalWeightedGramEnergy g A' s <
        m64LeastAnnulusArea g c0 c1 + δ := by
      dsimp only [m64ClassicalWeightedGramEnergy] at hweighted ⊢
      linarith
    have hnear_one : m64ClassicalWeightedGramEnergy g A' s <
        m64LeastAnnulusArea g c0 c1 + 1 := lt_of_lt_of_le hnear
      (by linarith [min_le_right (ε / 2) 1])
    have hsI := hconfine s hs A' hA'int hnear_one
    obtain ⟨W, hmap, hcols⟩ := m64ObservedWeakAnnulus_of_annulus A' e he1
    have hdiag := m64ObservedMetric_tangent_diagonal g e he1 B hgram
    have hseed := m64ObservedWeakAnnulus_seed_weightedEnergy_eq
      A' e he1 B hdiag W hmap hcols s
    have hmin' := hmin s hsI W
    rw [hseed] at hmin'
    have hle : L.weightedEnergy B r ≤ A.area + δ / 2 := hmin'.trans hweighted
    have hδle : δ ≤ ε := by
      dsimp [δ]
      linarith [min_le_left (ε / 2) 1]
    linarith
  have hLeq : L.weightedEnergy B r = m64LeastAnnulusArea g c0 c1 :=
    le_antisymm hLupper hLlower
  exact ⟨Astar, hAstar.trans hLeq⟩





theorem exists_m64MinimalAnnulus_of_freeModulus_certificates
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A0 : M64Annulus g c0 c1)
    (hconf : M64ConformalModulusApproximation g c0 c1)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hconfine : M64WeightedModulusConfinement g c0 c1 lo hi)
    (hadmit : ∀ {m : ℕ} (e : M → EuclideanSpace ℝ (Fin m))
      (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (r : ℝ)
      (L : M64ObservedWeakAnnulus (n := n) e c0 c1),
      r ∈ Icc lo hi → ContinuousOn L.map (interior m64AnnulusDomain) →
      ∃ A : M64Annulus g c0 c1,
        A.area = L.weightedEnergy B r ∧
        M64PiecewiseC1Annulus A ∧
        ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map (interior m64AnnulusDomain)) :
    ∃ A : M64Annulus g c0 c1,
      A.area = m64LeastAnnulusArea g c0 c1 ∧
      M64PiecewiseC1Annulus A ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map (interior m64AnnulusDomain) := by
  obtain ⟨m, e, he, hei, hread⟩ := M60.suCompactObservation_exists
    (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨W0, -, -⟩ := m64ObservedWeakAnnulus_of_annulus A0 e he1
  obtain ⟨B, r, hr, L, hB, hpos, hsymm, hgram, hLcont, hmin⟩ :=
    m64ObservedWeakAnnulus_exists_continuous_modulus_minimizer
      g e he1 hei hread hlo hlohi W0
  have hLupper : L.weightedEnergy B r ≤ m64LeastAnnulusArea g c0 c1 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := min (ε / 2) 1
    have hδ : 0 < δ := lt_min (half_pos hε) zero_lt_one
    obtain ⟨A, hA⟩ := m64LeastAnnulusArea_near_minimizer A0 (half_pos hδ)
    obtain ⟨s, hs, A', hA'int, hweighted⟩ := hconf A (δ / 2) (half_pos hδ)
    have hnear : m64ClassicalWeightedGramEnergy g A' s <
        m64LeastAnnulusArea g c0 c1 + δ := by
      dsimp only [m64ClassicalWeightedGramEnergy] at hweighted ⊢
      linarith
    have hnear_one : m64ClassicalWeightedGramEnergy g A' s <
        m64LeastAnnulusArea g c0 c1 + 1 := lt_of_lt_of_le hnear
      (by linarith [min_le_right (ε / 2) 1])
    have hsI := hconfine s hs A' hA'int hnear_one
    obtain ⟨W, hmap, hcols⟩ := m64ObservedWeakAnnulus_of_annulus A' e he1
    have hdiag := m64ObservedMetric_tangent_diagonal g e he1 B hgram
    have hseed := m64ObservedWeakAnnulus_seed_weightedEnergy_eq
      A' e he1 B hdiag W hmap hcols s
    have hmin' := hmin s hsI W
    rw [hseed] at hmin'
    have hle : L.weightedEnergy B r ≤ A.area + δ / 2 := hmin'.trans hweighted
    have hδle : δ ≤ ε := by
      dsimp [δ]
      linarith [min_le_left (ε / 2) 1]
    linarith
  obtain ⟨Astar, hAstar, hpiece, hsmooth⟩ := hadmit e B r L hr hLcont
  have hLlower : m64LeastAnnulusArea g c0 c1 ≤ L.weightedEnergy B r := by
    rw [← hAstar]
    exact m64LeastAnnulusArea_le_annulus Astar
  have hLeq : L.weightedEnergy B r = m64LeastAnnulusArea g c0 c1 :=
    le_antisymm hLupper hLlower
  exact ⟨Astar, hAstar.trans hLeq, hpiece, hsmooth⟩

end PoincareConjecture
