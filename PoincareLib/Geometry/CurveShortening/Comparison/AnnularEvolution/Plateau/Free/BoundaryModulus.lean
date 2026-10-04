import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.ModulusReduction

/-!
# Free boundary reparametrizations for the annular modulus reduction

Douglas--Morrey varies the boundary parametrizations while minimizing over
annuli.  The fixed-trace supplier in `FreeModulusReduction` is retained for
the conditional fixed-trace consumers; this file exposes the free-trace
candidate class and keeps the area-preserving collar as an explicit
geometric certificate.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => m64AnnulusDomain

/-- A monotone Lipschitz degree-one lift of the angular boundary circle. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
structure M64PeriodicDegreeOneLift where
  map : ℝ → ℝ
  monotone : Monotone map
  period_shift : ∀ x : ℝ, map (x + curvePeriod) = map x + curvePeriod
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 ≤ lipschitz_constant
  lipschitz_on : ∀ x y : ℝ,
    |map x - map y| ≤ lipschitz_constant * |x - y|

/-- The free-boundary weighted-energy range. The two lifts are part of each candidate, so
its annulus has the reparametrized boundary maps literally. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449. -/
def m64FreeClassicalWeightedGramEnergyRange
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) : Set ℝ :=
  {x | ∃ (r : ℝ), 0 < r ∧
    ∃ (sigma0 sigma1 : M64PeriodicDegreeOneLift),
      ∃ A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
        IntegrableOn (fun p =>
          (r * m60AreaGram g A.map p 0 0 +
            r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume ∧
          x = m64ClassicalWeightedGramEnergy g A r}

/-- Morrey's epsilon-conformal supplier with free monotone degree-one boundary lifts.
Uniformization and the construction of the lifts are deliberately left to the producer of
this certificate. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
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

/-- Fixed-area transport after changing both boundary parametrizations. A proof of this
certificate is the two-sided zero-area collar and seam-gluing construction; it is not
inferred from the fixed-trace minimizer. Proof expansion for Morgan-Tian (2007), Lemma
19.15, pp. 447-449. -/
def M64FreeBoundaryAreaTransport
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) : Prop :=
  ∀ (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map)),
    ∃ B : M64Annulus g c0 c1, B.area = A.area

/-- Area-preserving boundary transport and the Gram inequality bound the original least area
by each free candidate weighted energy. Proof expansion for Morgan-Tian (2007), Lemma 19.15,
pp. 447-449. -/
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

/-- Free conformal approximation and area-preserving collars identify the actual area
infimum with the free weighted-energy infimum. Proof expansion for Morgan-Tian (2007), Lemma
19.15, pp. 447-449. -/
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

end PoincareMT
