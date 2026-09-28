import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Convex.Basic










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.Proofs.M58

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]




noncomputable def chartContraction (c : M) (v : ℝ × (M × M)) : M :=
  (extChartAt I c).symm
    ((1 - v.1) • extChartAt I c v.2.2 + v.1 • extChartAt I c v.2.1)



theorem chartContraction_zero (c p q : M) (hq : q ∈ (extChartAt I c).source) :
    chartContraction I c (0, p, q) = q := by
  simpa [chartContraction] using (extChartAt I c).left_inv hq



theorem chartContraction_one (c p q : M) (hp : p ∈ (extChartAt I c).source) :
    chartContraction I c (1, p, q) = p := by
  simpa [chartContraction] using (extChartAt I c).left_inv hp



theorem chartContraction_diagonal (c p : M) (hp : p ∈ (extChartAt I c).source)
    (t : ℝ) : chartContraction I c (t, p, p) = p := by
  simp only [chartContraction, ← add_smul, sub_add_cancel, one_smul]
  exact (extChartAt I c).left_inv hp



theorem extChartAt_chartContraction (c : M) (v : ℝ × (M × M))
    (hv : (1 - v.1) • extChartAt I c v.2.2 + v.1 • extChartAt I c v.2.1 ∈
      (extChartAt I c).target) :
    extChartAt I c (chartContraction I c v) =
      (1 - v.1) • extChartAt I c v.2.2 + v.1 • extChartAt I c v.2.1 :=
  (extChartAt I c).right_inv hv



theorem chartContraction_mem_convex (c p q : M) {V : Set E}
    (hV : Convex ℝ V) (hsub : V ⊆ (extChartAt I c).target)
    (hp : extChartAt I c p ∈ V) (hq : extChartAt I c q ∈ V)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    chartContraction I c (t, p, q) ∈ (extChartAt I c).source ∧
      extChartAt I c (chartContraction I c (t, p, q)) ∈ V := by
  have hv : (1 - t) • extChartAt I c q + t • extChartAt I c p ∈ V :=
    hV hq hp (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  exact ⟨(extChartAt I c).map_target (hsub hv),
    (extChartAt_chartContraction I c (t, p, q) (hsub hv)) ▸ hv⟩

variable [I.Boundaryless] [IsManifold I ∞ M]




theorem contMDiffAt_chartContraction (c : M) (v : ℝ × (M × M))
    (hp : v.2.1 ∈ (extChartAt I c).source)
    (hq : v.2.2 ∈ (extChartAt I c).source)
    (hv : (1 - v.1) • extChartAt I c v.2.2 + v.1 • extChartAt I c v.2.1 ∈
      (extChartAt I c).target) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞ (chartContraction I c) v := by
  have hp' : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) 𝓘(ℝ, E) ∞
      (fun w : ℝ × (M × M) => extChartAt I c w.2.1) v :=
    (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hp)).comp v
      (contMDiffAt_fst.comp v contMDiffAt_snd)
  have hq' : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) 𝓘(ℝ, E) ∞
      (fun w : ℝ × (M × M) => extChartAt I c w.2.2) v :=
    (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hq)).comp v
      (contMDiffAt_snd.comp v contMDiffAt_snd)
  have hcoord : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) 𝓘(ℝ, E) ∞
      (fun w : ℝ × (M × M) =>
        (1 - w.1) • extChartAt I c w.2.2 + w.1 • extChartAt I c w.2.1) v :=
    ((contMDiffAt_const.sub contMDiffAt_fst).smul hq').add (contMDiffAt_fst.smul hp')
  exact ((contMDiffOn_extChartAt_symm c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hv)).comp v hcoord




theorem contMDiffAt_chartContraction_diagonal (c p : M)
    (hp : p ∈ (extChartAt I c).source) (t : ℝ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod I)) I ∞ (chartContraction I c) (t, p, p) := by
  apply contMDiffAt_chartContraction I c (t, p, p) hp hp
  simp only [← add_smul, sub_add_cancel, one_smul]
  exact (extChartAt I c).map_source hp

end PoincareConjecture.Proofs.M58
