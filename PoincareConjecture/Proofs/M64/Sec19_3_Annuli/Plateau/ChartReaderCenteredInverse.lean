import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ChartReaderMetric

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

theorem m64ChartReadable_centered_inverse {n m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {e : M → EuclideanSpace ℝ (Fin m)}
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (P : EuclideanSpace ℝ (Fin n) → M),
      P 0 = p ∧ ContMDiffAt (𝓡 n) (𝓡 n) ∞ P 0 ∧
        ∀ᶠ q in 𝓝 p, P (T (e q - e p)) = q := by
  obtain ⟨b, hb, T, hT⟩ := hread p
  let c := extChartAt (𝓡 n) b
  have hTp : T (e p) = c p := hT.self_of_nhds
  have hp : p ∈ c.source := hb
  have hcp : c p ∈ c.target := c.map_source hp
  let P : EuclideanSpace ℝ (Fin n) → M := fun y => c.symm (y + T (e p))
  have hP0 : P 0 = p := by
    simp only [P, zero_add, hTp, c.left_inv hp]
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (c p) :=
    (contMDiffOn_extChartAt_symm (n := ∞) b).contMDiffAt
      ((isOpen_extChartAt_target b).mem_nhds hcp)
  refine ⟨T, P, hP0, ?_, ?_⟩
  · have hi' : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (0 + T (e p)) := by
      simpa only [zero_add, hTp] using hi
    exact hi'.comp 0 (contDiff_id.add contDiff_const).contMDiff.contMDiffAt
  · filter_upwards [hT, (isOpen_extChartAt_source b).mem_nhds hp] with q hq hqs
    change c.symm (T (e q - e p) + T (e p)) = q
    rw [map_sub, sub_add_cancel, hq, c.left_inv hqs]

end PoincareConjecture
