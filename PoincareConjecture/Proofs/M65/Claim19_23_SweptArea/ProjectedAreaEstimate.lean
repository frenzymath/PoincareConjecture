import PoincareConjecture.Statements.M64Annulus
import PoincareConjecture.Proofs.M60.Filling










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {circumference t : ℝ} {P : M62.CircleProductData F circumference}
  {c0 c1 : ℝ → P.charts.Point}
  {A : M64Annulus (P.flow.metric t) c0 c1}
  {gamma0 gamma1 : C1FreeLoopSpace (M := M)}



theorem m65ProjectedDiskComparison
    (projection : M64AnnulusProjection P t)
    (gluing : M64DiskGluingConclusion P t A gamma0 gamma1)
    (D0 : LipschitzSpanningDisk (F.metric t) gamma0) :
    ∃ _D1 : LipschitzSpanningDisk (F.metric t) gamma1,
      0 ≤ fillingArea (F.metric t) gamma1 ∧
        |fillingArea (F.metric t) gamma1 - fillingArea (F.metric t) gamma0| ≤
          A.area := by
  obtain ⟨D1, _⟩ := gluing.forward 1 zero_lt_one D0
  obtain ⟨_, B, _, harea, _, hle⟩ := projection c0 c1 A
  refine ⟨D1, m60FillingArea_nonneg_of_disk _ _ D1, ?_⟩
  exact (gluing.infimum ⟨D0⟩ ⟨D1⟩).trans (harea.symm.trans_le hle)



theorem m65FillingArea_le_add_annulus
    (projection : M64AnnulusProjection P t)
    (gluing : M64DiskGluingConclusion P t A gamma0 gamma1)
    (D0 : LipschitzSpanningDisk (F.metric t) gamma0) :
    fillingArea (F.metric t) gamma1 ≤ fillingArea (F.metric t) gamma0 + A.area := by
  obtain ⟨_, _, harea⟩ := m65ProjectedDiskComparison projection gluing D0
  exact (sub_le_iff_le_add.mp ((le_abs_self _).trans harea)).trans_eq (add_comm _ _)

end PoincareConjecture
