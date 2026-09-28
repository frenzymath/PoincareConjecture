import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ChartReaderMetric
import Mathlib.Topology.PartitionOfUnity

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64ChartReadable_observed_metric
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hread : M60.SUChartReadable (n := n) e) :
    ∃ (B : M → E →L[ℝ] E →L[ℝ] ℝ) (K : ℝ),
      Continuous B ∧ 0 ≤ K ∧ (∀ q, ‖B q‖ ≤ K) ∧
      (∀ q v, 0 ≤ B q v v) ∧ (∀ q v w, B q v w = B q w v) ∧
      ∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f →
        ∀ z, ∀ i j : Fin 2,
          B (f z) (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
              m60AreaGram g f z i j := by
  classical
  choose U H hU hp hH hpos hsymm hgram using m64ChartReadable_local_metric g e he hread
  obtain ⟨rho, hrho⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hU
    (fun q _ => mem_iUnion.mpr ⟨q, hp q⟩)
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun q => ∑ᶠ p, rho p q • H p q
  let : ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ) :=
    @IsTopologicalAddGroup.toContinuousAdd _ _ _ ContinuousLinearMap.topologicalAddGroup
  have hB : Continuous B := hrho.continuous_finsum_smul hU hH
  have hbounded : Bornology.IsBounded (range B) := (isCompact_range hB).isBounded
  obtain ⟨A, hA⟩ := hbounded.exists_norm_le
  have heval (q : M) (v w : E) :
      B q v w = ∑ p ∈ rho.finsupport q, rho p q * H p q v w := by
    change (∑ᶠ p, rho p q • H p q) v w = _
    rw [← rho.sum_finsupport_smul_eq_finsum H]
    simp only [sum_apply, smul_apply, smul_eq_mul]
  refine ⟨B, max A 0, hB, le_max_right _ _, ?_, ?_, ?_, ?_⟩
  · intro q
    exact (hA _ (mem_range_self q)).trans (le_max_left _ _)
  · intro q v
    rw [heval]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (rho.nonneg p q) (hpos p q v)
  · intro q v w
    simp only [heval, hsymm]
  · intro f hf z i j
    rw [heval]
    calc
      _ = ∑ p ∈ rho.finsupport (f z), rho p (f z) * m60AreaGram g f z i j := by
        apply Finset.sum_congr rfl
        intro p hp
        have hsupport : f z ∈ Function.support (rho p) :=
          (rho.mem_finsupport (f z)).mp hp
        rw [hgram p f hf z (hrho p (subset_tsupport _ hsupport)) i j]
      _ = m60AreaGram g f z i j := by
        rw [← Finset.sum_mul, rho.sum_finsupport (mem_univ _), one_mul]

end PoincareConjecture
