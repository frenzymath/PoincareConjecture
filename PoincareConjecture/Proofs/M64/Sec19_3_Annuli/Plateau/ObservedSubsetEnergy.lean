import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Topology
open scoped Manifold

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

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

end PoincareConjecture.M64ObservedWeakAnnulus
