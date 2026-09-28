import PoincareConjecture.Proofs.M09.TangentChartPhase








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem tangentChartPhase_contMDiffOn (p : M) :
    ContMDiffOn ((𝓡 n).prod (𝓡 n)) (𝓘(ℝ, V × V)) ∞ (tangentChartPhase (n := n) p)
      {q : TangentBundle (𝓡 n) M | q.proj ∈ (chartAt V p).source} := by
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt V p) (chartAt V p).source :=
    contMDiffOn_chart
  have ht := hc.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt V p).open_source.uniqueMDiffOn
  have hmodel : ContMDiff ((𝓡 n).prod (𝓡 n)) (𝓘(ℝ, V × V)) ∞
      (fun q : TangentBundle (𝓡 n) V ↦ (q.proj, q.2)) := by
    convert! (contMDiff_tangentBundleModelSpaceHomeomorph (I := 𝓡 n) (n := ∞)) using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have h := hmodel.comp_contMDiffOn ht
  apply h.congr
  intro q hq
  change ((chartAt V p) q.proj, (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) q.proj) q.2) =
    ((chartAt V p) q.proj,
      (mfderivWithin (𝓡 n) (𝓡 n) (chartAt V p) (chartAt V p).source q.proj) q.2)
  rw [mfderivWithin_of_isOpen (chartAt V p).open_source hq]

end PoincareConjecture.Proofs.M09
