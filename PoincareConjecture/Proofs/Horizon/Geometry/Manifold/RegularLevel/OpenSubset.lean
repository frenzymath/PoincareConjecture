import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.ChartedSpace
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion

open Set Function TopologicalSpace
open scoped Manifold Topology ContDiff

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Poincare.Geometry.Manifold.RegularLevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

abbrev openLevelSet (f : M → ℝ) (U : Opens M) (c : ℝ) :=
  ((fun y : U => f (y : M)) ⁻¹' {c} : Set U)

def openLevelIncl (f : M → ℝ) (U : Opens M) (c : ℝ)
    (z : openLevelSet f U c) : M := ((z : U) : M)

theorem range_openLevelIncl (f : M → ℝ) (U : Opens M) (c : ℝ) :
    range (openLevelIncl f U c) = (U : Set M) ∩ f ⁻¹' {c} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z : U).2, z.2⟩
  · rintro ⟨hxU, hxc⟩
    exact ⟨⟨⟨x, hxU⟩, hxc⟩, rfl⟩

theorem isEmbedding_openLevelIncl (f : M → ℝ) (U : Opens M) (c : ℝ) :
    Topology.IsEmbedding (openLevelIncl f U c) :=
  Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal

variable {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (U : Opens M)
  (hreg : ∀ x ∈ U, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
  (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)] (c : ℝ)

include hf hreg in
theorem openLevelRestrict_regular (x : U) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y : U => f (y : M)) x ≠ 0 := by
  rw [mfderiv_opens_restrict U f ((hf (x : M)).mdifferentiableAt (by simp))]
  exact hreg (x : M) x.2

@[reducible] def openLevelSetChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (openLevelSet f U c) :=
  levelSetChartedSpace (hf.comp contMDiff_subtype_val) n c
    (fun x _ => openLevelRestrict_regular hf U hreg x)

theorem isManifold_openLevelSet :
    letI := openLevelSetChartedSpace hf U hreg n c
    IsManifold (𝓡 n) ∞ (openLevelSet f U c) :=
  isManifold_levelSet (hf.comp contMDiff_subtype_val) n c
    (fun x _ => openLevelRestrict_regular hf U hreg x)

theorem contMDiff_openLevelIncl :
    letI := openLevelSetChartedSpace hf U hreg n c
    ContMDiff (𝓡 n) I ∞ (openLevelIncl f U c) := by
  letI := openLevelSetChartedSpace hf U hreg n c
  exact contMDiff_subtype_val.comp
    (contMDiff_levelSet_val (hf.comp contMDiff_subtype_val) n c
      (fun x _ => openLevelRestrict_regular hf U hreg x))

theorem mfderiv_openLevelIncl (z : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    mfderiv (𝓡 n) I (openLevelIncl f U c) z =
      mfderiv (𝓡 n) I ((↑) : openLevelSet f U c → U) z := by
  letI := openLevelSetChartedSpace hf U hreg n c
  have hv : ContMDiff (𝓡 n) I ∞ ((↑) : openLevelSet f U c → U) :=
    contMDiff_levelSet_val (hf.comp contMDiff_subtype_val) n c
      (fun x _ => openLevelRestrict_regular hf U hreg x)
  have hval : MDifferentiableAt (𝓡 n) I
      ((↑) : openLevelSet f U c → U) z :=
    (hv z).mdifferentiableAt (by simp)
  have h := mfderiv_comp z
    (hasMFDerivAt_opens_subtypeVal U (z : U)).mdifferentiableAt hval
  change mfderiv (𝓡 n) I ((fun y : U => (y : M)) ∘
    ((↑) : openLevelSet f U c → U)) z = _
  rw [h, mfderiv_opens_subtypeVal]
  ext v
  rfl

theorem injective_mfderiv_openLevelIncl (z : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    Injective (mfderiv (𝓡 n) I (openLevelIncl f U c) z) := by
  letI := openLevelSetChartedSpace hf U hreg n c
  rw [mfderiv_openLevelIncl hf U hreg n c]
  exact mfderiv_levelSet_val_injective (hf.comp contMDiff_subtype_val) n c
    (fun x _ => openLevelRestrict_regular hf U hreg x) z

theorem range_mfderiv_openLevelIncl (z : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    (mfderiv (𝓡 n) I (openLevelIncl f U c) z :
      EuclideanSpace ℝ (Fin n) →L[ℝ] E).range =
      (mfderiv I 𝓘(ℝ, ℝ) f (openLevelIncl f U c z) : E →L[ℝ] ℝ).ker := by
  letI := openLevelSetChartedSpace hf U hreg n c
  have hr := range_mfderiv_levelSet_val (hf.comp contMDiff_subtype_val) n c
    (fun x _ => openLevelRestrict_regular hf U hreg x) z
  unfold levelHyperplane levelDifferential at hr
  have hk := congrArg (fun A : E →L[ℝ] ℝ => A.ker)
    (mfderiv_opens_restrict U f ((hf ((z : U) : M)).mdifferentiableAt (by simp)))
  exact (congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] E => A.range)
    (mfderiv_openLevelIncl hf U hreg n c z)).trans (hr.trans hk)

end Poincare.Geometry.Manifold.RegularLevel
