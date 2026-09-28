import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

theorem squareTime_mem_window {b s : ℝ} (T : ℝ) (hb : 0 < b)
    (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    T - s ^ 2 ∈ Set.Icc (T - b) T := by
  have hprod := mul_pos (sub_pos.mpr hs.1) (sub_pos.mpr hs.2)
  have hsqrt := Real.sq_sqrt hb.le
  constructor <;> nlinarith [sq_nonneg s]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
theorem squareTime_smooth (T : ℝ) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ (T - z.1 ^ 2, z.2)) := by
  have h : ContDiff ℝ ∞ (fun s : ℝ ↦ T - s ^ 2) :=
    contDiff_const.sub (contDiff_id.pow 2)
  exact (h.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd

theorem squareTime_metric_smooth {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J) :
    RiemannianMetric.IsSmoothFamilyOn (fun s ↦ F.metric (T - s ^ 2))
      (Set.Ioo (-Real.sqrt b) (Real.sqrt b)) := by
  exact F.smooth.comp (squareTime_smooth (M := M) T).contMDiffOn
    (fun z hz ↦ ⟨hwindow (squareTime_mem_window T hb hz.1), Set.mem_univ _⟩)

theorem squareTime_scalar_smooth {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × M ↦ (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)
      (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ Set.univ) := by
  exact (hM04.scalar_regular n M J F).comp (squareTime_smooth (M := M) T).contMDiffOn
    (fun z hz ↦ ⟨hwindow (squareTime_mem_window T hb hz.1), Set.mem_univ _⟩)

end PoincareConjecture.Proofs.M09
