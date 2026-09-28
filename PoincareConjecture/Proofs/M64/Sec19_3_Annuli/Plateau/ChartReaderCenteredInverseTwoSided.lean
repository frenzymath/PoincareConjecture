import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ChartReaderCenteredInverse

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

theorem m64ChartReadable_centered_inverse_two_sided {n m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {e : M → EuclideanSpace ℝ (Fin m)}
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (P : EuclideanSpace ℝ (Fin n) → M),
      P 0 = p ∧ ContMDiffAt (𝓡 n) (𝓡 n) ∞ P 0 ∧
        (∀ᶠ q in 𝓝 p, P (T (e q - e p)) = q) ∧
        ∀ᶠ y in 𝓝 0, T (e (P y) - e p) = y := by
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
  have hP : ContMDiffAt (𝓡 n) (𝓡 n) ∞ P 0 := by
    have hi' : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (0 + T (e p)) := by
      simpa only [zero_add, hTp] using hi
    exact hi'.comp 0 (contDiff_id.add contDiff_const).contMDiff.contMDiffAt
  refine ⟨T, P, hP0, hP, ?_, ?_⟩
  · filter_upwards [hT, (isOpen_extChartAt_source b).mem_nhds hp] with q hq hqs
    change c.symm (T (e q - e p) + T (e p)) = q
    rw [map_sub, sub_add_cancel, hq, c.left_inv hqs]
  · have hlim : Tendsto P (𝓝 0) (𝓝 p) := hP0 ▸ hP.continuousAt
    have htarget : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), y + T (e p) ∈ c.target := by
      have hz : 0 + T (e p) ∈ c.target := by simpa only [zero_add, hTp] using hcp
      exact ((continuous_id.add continuous_const).tendsto 0).eventually
        ((isOpen_extChartAt_target b).mem_nhds hz)
    filter_upwards [hlim.eventually hT, htarget] with y hy hyt
    rw [map_sub, hy]
    change c (c.symm (y + T (e p))) - T (e p) = y
    rw [c.right_inv hyt, add_sub_cancel_right]

end PoincareConjecture
