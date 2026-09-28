import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenSubset







open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false

namespace Poincare.Geometry.Manifold.RegularLevel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
  (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)] (c : ℝ)
  (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)

theorem contMDiffAt_into_levelSet_iff (F : N → (f ⁻¹' {c} : Set M)) (x : N) :
    letI := levelSetChartedSpace hf n c hreg
    ContMDiffAt J (𝓡 n) ∞ F x ↔
      ContMDiffAt J I ∞ (fun y => (F y : M)) x := by
  letI := levelSetChartedSpace hf n c hreg
  constructor
  · intro hF
    exact (contMDiff_levelSet_val hf n c hreg (F x)).comp x hF
  · intro hF
    rw [contMDiffAt_iff_target]
    refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hF.continuousAt, ?_⟩
    let y : M := (F x : M)
    let hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0 := hreg y (F x).2
    have hchart : ContMDiffAt J 𝓘(ℝ, E) ∞
        (fun z => extChartAt I y (F z : M)) x :=
      contMDiffAt_extChartAt.comp x hF
    have hG : ContDiffAt ℝ ∞ (adaptedStraightening hf y hdf) (extChartAt I y y) :=
      (contDiffOn_adaptedStraightening hf y hdf).contDiffAt
        ((adaptedStraightening hf y hdf).open_source.mem_nhds
          (mem_adaptedStraightening_source hf y hdf))
    have hcomp := hG.contMDiffAt.comp x hchart
    have hsub : ContMDiffAt J 𝓘(ℝ, E) ∞
        (fun z => adaptedStraightening hf y hdf (extChartAt I y (F z : M)) -
          extChartAt I y y) x :=
      (contDiff_id.sub (contDiff_const (c := extChartAt I y y))).contDiffAt.contMDiffAt.comp x hcomp
    have hproj := (sliceProj (I := I) n hdf).contDiff.contDiffAt.contMDiffAt.comp x hsub
    convert! hproj using 1

theorem contMDiffAt_into_openLevelSet_iff (U : Opens M)
    (hregU : ∀ x ∈ U, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (F : N → openLevelSet f U c) (x : N) :
    letI := openLevelSetChartedSpace hf U hregU n c
    ContMDiffAt J (𝓡 n) ∞ F x ↔
      ContMDiffAt J I ∞ (openLevelIncl f U c ∘ F) x := by
  letI := openLevelSetChartedSpace hf U hregU n c
  have h := contMDiffAt_into_levelSet_iff (J := J)
    (hf.comp contMDiff_subtype_val) n c
    (fun y _ => openLevelRestrict_regular hf U hregU y) F x
  exact h.trans (ContMDiffAt.subtypeVal_comp_iff U
    (fun y => (F y : U)) x).symm

end Poincare.Geometry.Manifold.RegularLevel
