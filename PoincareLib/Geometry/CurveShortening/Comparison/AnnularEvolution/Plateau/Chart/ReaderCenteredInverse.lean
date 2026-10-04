import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Chart.ReaderMetric

/-!
# Centered inverse coordinates from the actual chart reader

The existing finite observation reads a genuine target chart near every
point. Centering its linear reader gives a smooth target reconstruction
at zero and the actual local inverse identity. No boundary regularity is
needed. Source: Morrey ICM pp. 183-185; M64 phase-cone normalization.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareMT

/-- A genuine linear chart reader gives centered smooth inverse coordinates for the original
target, before any competitor is chosen. Proof expansion for Morgan-Tian (2007), Lemma
19.15, pp. 447-449; M64 derivation 2026-09-26-phase-cone-normalization.md. -/
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

end PoincareMT
