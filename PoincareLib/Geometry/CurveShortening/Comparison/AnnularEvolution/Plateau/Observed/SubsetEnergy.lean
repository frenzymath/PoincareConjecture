import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.AnnulusClass

/-! Coercivity transfers the original metric energy to the sum of the
actual weak column squares on any subset of the original open annulus.
Source: the observed-metric construction and Morrey energy estimates.
Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Topology
open scoped Manifold

namespace PoincareMT.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

/-- Both weak columns are controlled on the same original subset; all integrability and
tangent constraints come from the weak annulus. Proof expansion for Morgan-Tian (2007),
Lemma 19.15, pp. 447-449. -/
theorem column_sum_energy_le_on (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound C : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v) {K : Set LoopPlane} (hK : K ⊆ S) :
    (∫ p in K, ∑ i : Fin 2, ‖A.column i p‖ ^ 2) ≤
      2 * C * ∫ p in K,
        (B (A.map p) (A.column 0 p) (A.column 0 p) +
          B (A.map p) (A.column 1 p) (A.column 1 p)) / 2 := by
  have hcol : IntegrableOn (fun p => ∑ i : Fin 2, ‖A.column i p‖ ^ 2) S :=
    integrable_finsetSum _ (fun i _ => (Lp.memLp (A.column i)).norm.integrable_sq)
  have hEi := (A.energy_integrable B hB hei hb).mono_set hK
  rw [← integral_const_mul]
  apply integral_mono_ae (hcol.mono_set hK) (hEi.const_mul _)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hK (A.tangent 0),
    ae_restrict_of_ae_restrict_of_subset hK (A.tangent 1)] with p h0 h1
  have hsum := add_le_add (hcoercive (A.map p) (A.column 0 p) h0)
    (hcoercive (A.map p) (A.column 1 p) h1)
  simp only [Fin.sum_univ_two]
  nlinarith

end PoincareMT.M64ObservedWeakAnnulus
