import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Topology
open scoped Topology ENNReal

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem column_pair_integrable
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K) (i j : Fin 2) :
    IntegrableOn (fun p => Q (A.map p) (A.column i p) (A.column j p)) S volume := by
  have hcoef := hQ.comp_aestronglyMeasurable (A.map_aestronglyMeasurable hei)
  have heval : Continuous (fun q : ((E →L[ℝ] E →L[ℝ] ℝ) × E) × E =>
      q.1.1 q.1.2 q.2) :=
    (continuous_fst.fst.clm_apply continuous_fst.snd).clm_apply continuous_snd
  have hm := heval.comp_aestronglyMeasurable
    ((hcoef.prodMk (Lp.aestronglyMeasurable (A.column i))).prodMk
      (Lp.aestronglyMeasurable (A.column j)))
  have hprod : Integrable (fun p => ‖A.column i p‖ * ‖A.column j p‖) mu := by
    apply memLp_one_iff_integrable.mp
    convert! (show MemLp ((fun p => ‖A.column i p‖) * fun p => ‖A.column j p‖) 1 mu from
      (Lp.memLp (A.column j)).norm.mul (Lp.memLp (A.column i)).norm) using 1
  apply (hprod.const_mul K).mono' hm
  filter_upwards [] with p
  calc
    ‖Q (A.map p) (A.column i p) (A.column j p)‖ ≤
        ‖Q (A.map p)‖ * ‖A.column i p‖ * ‖A.column j p‖ :=
      (Q (A.map p)).le_opNorm₂ _ _
    _ ≤ K * (‖A.column i p‖ * ‖A.column j p‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hb _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end PoincareConjecture.M64ObservedWeakAnnulus
