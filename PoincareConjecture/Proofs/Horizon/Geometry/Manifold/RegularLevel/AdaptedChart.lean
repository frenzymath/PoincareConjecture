import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.Straightening
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open Set Filter Function
open scoped Manifold Topology ContDiff

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Poincare.Geometry.Manifold.RegularLevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

def mfderivReal (f : M → ℝ) (q : M) (v : TangentSpace I q) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f q v

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
@[simp] theorem mfderivReal_def (f : M → ℝ) (q : M) (v : TangentSpace I q) :
    mfderivReal (I := I) f q v = mfderiv I 𝓘(ℝ, ℝ) f q v := rfl

omit [FiniteDimensional ℝ E] in

theorem contDiffAt_comp_extChartAt_symm {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (z : M) {y : E}
    (hy : y ∈ (extChartAt I z).target) :
    ContDiffAt ℝ ∞ (f ∘ (extChartAt I z).symm) y := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I z).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z).contMDiffAt
      ((isOpen_extChartAt_target (I := I) z).mem_nhds hy)
  exact contMDiffAt_iff_contDiffAt.mp
    (ContMDiffAt.comp y (hf ((extChartAt I z).symm y)) hsymm)

omit [FiniteDimensional ℝ E] in

theorem contDiffOn_comp_extChartAt_symm {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (z : M) :
    ContDiffOn ℝ ∞ (f ∘ (extChartAt I z).symm) (extChartAt I z).target :=
  fun _ hy => (contDiffAt_comp_extChartAt_symm hf z hy).contDiffWithinAt

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in

theorem hasFDerivAt_comp_extChartAt_symm {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    HasFDerivAt (f ∘ (extChartAt I y).symm) (mfderiv I 𝓘(ℝ, ℝ) f y)
      (extChartAt I y y) := by
  have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt (by simp)
  have h := hmd.hasMFDerivAt.2
  rw [I.range_eq_univ, hasFDerivWithinAt_univ] at h
  have hfun : writtenInExtChartAt I 𝓘(ℝ, ℝ) y f
      = f ∘ (extChartAt I y).symm := by
    simp [writtenInExtChartAt]
  rwa [hfun] at h

theorem exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M)
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    ∃ G : OpenPartialHomeomorph E E,
      G.source ⊆ (extChartAt I y).target ∧
      extChartAt I y y ∈ G.source ∧
      G (extChartAt I y y) = extChartAt I y y ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ G.symm G.target ∧
      ∀ v ∈ G.target, f ((extChartAt I y).symm (G.symm v))
        = f y + mfderivReal (I := I) f y (v - extChartAt I y y) := by
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ :=
    exists_openPartialHomeomorph_comp_symm_eq_affine
      (isOpen_extChartAt_target (I := I) y)
      (contDiffOn_comp_extChartAt_symm hf y)
      (mem_extChartAt_target (I := I) y)
      (hasFDerivAt_comp_extChartAt_symm hf y) hdf
  refine ⟨G, h1, h2, h3, h4, h5, fun v hv => ?_⟩
  have h := h6 v hv
  rw [Function.comp_apply, Function.comp_apply, extChartAt_to_inv] at h
  rw [mfderivReal_def]
  exact h

end Poincare.Geometry.Manifold.RegularLevel

end
