import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => m64AnnulusDomain

structure M64PeriodicDegreeOneLift where
  map : ℝ → ℝ
  monotone : Monotone map
  period_shift : ∀ x : ℝ, map (x + curvePeriod) = map x + curvePeriod
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 ≤ lipschitz_constant
  lipschitz_on : ∀ x y : ℝ,
    |map x - map y| ≤ lipschitz_constant * |x - y|

def m64FreeClassicalWeightedGramEnergyRange
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) : Set ℝ :=
  {x | ∃ (r : ℝ), 0 < r ∧
    ∃ (sigma0 sigma1 : M64PeriodicDegreeOneLift),
      ∃ A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
        IntegrableOn (fun p =>
          (r * m60AreaGram g A.map p 0 0 +
            r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume ∧
          x = m64ClassicalWeightedGramEnergy g A r}

def M64FreeConformalModulusApproximation
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) : Prop :=
  ∀ A : M64Annulus g c0 c1, ∀ ε : ℝ, 0 < ε →
    ∃ r : ℝ, 0 < r ∧
      ∃ (sigma0 sigma1 : M64PeriodicDegreeOneLift),
        ∃ A' : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
          IntegrableOn (fun p =>
            (r * m60AreaGram g A'.map p 0 0 +
              r⁻¹ * m60AreaGram g A'.map p 1 1) / 2) S volume ∧
            m64ClassicalWeightedGramEnergy g A' r ≤ A.area + ε

def M64FreeBoundaryAreaTransport
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) : Prop :=
  ∀ (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map)),
    ∃ B : M64Annulus g c0 c1, B.area = A.area

theorem m64LeastAnnulusArea_le_free_weightedGramEnergy
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (htransport : M64FreeBoundaryAreaTransport g c0 c1)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hA : IntegrableOn (fun p =>
      (r * m60AreaGram g A.map p 0 0 +
        r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume) :
    m64LeastAnnulusArea g c0 c1 ≤ m64ClassicalWeightedGramEnergy g A r := by
  obtain ⟨B, hB⟩ := htransport sigma0 sigma1 A
  calc
    m64LeastAnnulusArea g c0 c1 ≤ B.area := m64LeastAnnulusArea_le_annulus B
    _ = A.area := hB
    _ ≤ m64ClassicalWeightedGramEnergy g A r := A.area_le_weightedGramEnergy hr hA

theorem m64LeastAnnulusArea_eq_freeClassicalWeightedGramEnergy_sInf
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A0 : M64Annulus g c0 c1)
    (hconf : M64FreeConformalModulusApproximation g c0 c1)
    (htransport : M64FreeBoundaryAreaTransport g c0 c1) :
    m64LeastAnnulusArea g c0 c1 =
      sInf (m64FreeClassicalWeightedGramEnergyRange g c0 c1) := by
  have hne : (m64FreeClassicalWeightedGramEnergyRange g c0 c1).Nonempty := by
    obtain ⟨r, hr, sigma0, sigma1, A, hA, hle⟩ := hconf A0 1 one_pos
    exact ⟨m64ClassicalWeightedGramEnergy g A r,
      ⟨r, hr, sigma0, sigma1, A, hA, rfl⟩⟩
  have hbelow : BddBelow (m64FreeClassicalWeightedGramEnergyRange g c0 c1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, hr, sigma0, sigma1, A, hA, rfl⟩
    unfold m64ClassicalWeightedGramEnergy
    apply integral_nonneg
    intro p
    have h00 := m60AreaGram_diagonal_nonneg g A.map p 0
    have h11 := m60AreaGram_diagonal_nonneg g A.map p 1
    exact div_nonneg (add_nonneg (mul_nonneg hr.le h00)
      (mul_nonneg (inv_nonneg.mpr hr.le) h11)) (by norm_num)
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨r, hr, sigma0, sigma1, A, hA, rfl⟩
    exact m64LeastAnnulusArea_le_free_weightedGramEnergy
      htransport sigma0 sigma1 A hr hA
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨A, hA⟩ := m64LeastAnnulusArea_near_minimizer A0 (half_pos hε)
    obtain ⟨r, hr, sigma0, sigma1, A', hA'int, hweighted⟩ :=
      hconf A (ε / 2) (half_pos hε)
    have hle := csInf_le hbelow
      ⟨r, hr, sigma0, sigma1, A', hA'int, rfl⟩
    have hlt : m64ClassicalWeightedGramEnergy g A' r <
        m64LeastAnnulusArea g c0 c1 + ε := by
      linarith
    exact (hle.trans_lt hlt).le

end PoincareConjecture
