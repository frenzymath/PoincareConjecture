import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ChartReaderProjection
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



theorem m64ChartReadable_tangent_projection
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) :
    ∃ (P : M → E →L[ℝ] E) (K : ℝ), Continuous P ∧ 0 ≤ K ∧ (∀ q, ‖P q‖ ≤ K) ∧
      (∀ q w, P q (mfderiv (𝓡 n) (𝓡 m) e q w) = mfderiv (𝓡 n) (𝓡 m) e q w) ∧
      ∀ q w, P q w ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) := by
  classical
  choose U H hU hp hH hfix hrange using m64ChartReadable_local_projection e he hread
  obtain ⟨rho, hrho⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hU
    (fun q _ => mem_iUnion.mpr ⟨q, hp q⟩)
  let P : M → E →L[ℝ] E := fun q => ∑ᶠ p, rho p q • H p q
  have hP : Continuous P := hrho.continuous_finsum_smul hU hH
  have hbounded : Bornology.IsBounded (range P) := (isCompact_range hP).isBounded
  obtain ⟨A, hA⟩ := hbounded.exists_norm_le
  have heval (q : M) (w : E) :
      P q w = ∑ p ∈ rho.finsupport q, rho p q • H p q w := by
    change (∑ᶠ p, rho p q • H p q) w = _
    rw [← rho.sum_finsupport_smul_eq_finsum H]
    simp only [sum_apply, smul_apply]
  have hmem (q p : M) (hp : p ∈ rho.finsupport q) : q ∈ U p :=
    hrho p (subset_tsupport _ ((rho.mem_finsupport q).mp hp))
  refine ⟨P, max A 0, hP, le_max_right _ _, ?_, ?_, ?_⟩
  · intro q
    exact (hA _ (mem_range_self q)).trans (le_max_left _ _)
  · intro q w
    erw [heval]
    calc
      _ = ∑ p ∈ rho.finsupport q, rho p q • mfderiv (𝓡 n) (𝓡 m) e q w := by
        apply Finset.sum_congr rfl
        intro p hp
        erw [hfix p q (hmem q p hp) w]
        rfl
      _ = _ := by rw [← Finset.sum_smul, rho.sum_finsupport (mem_univ q), one_smul]
  · intro q w
    rw [heval]
    change (∑ p ∈ rho.finsupport q, rho p q • H p q w) ∈
      (mfderiv (𝓡 n) (𝓡 m) e q).toLinearMap.range
    apply Submodule.sum_mem
    intro p hp
    exact Submodule.smul_mem _ _ (hrange p q (hmem q p hp) w)

end PoincareConjecture
