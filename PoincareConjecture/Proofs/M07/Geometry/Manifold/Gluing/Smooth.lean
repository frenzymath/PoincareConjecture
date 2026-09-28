import PoincareConjecture.Proofs.M07.Geometry.Manifold.Gluing.Charts
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas








open Set Topology Manifold IsManifold
open scoped ContDiff

noncomputable section

namespace Poincare.Gluing
universe u v

variable {I : Type u} {E : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (U : I → Set E) (hU : ∀ i, IsOpen (U i))
variable [∀ i, Nonempty (Piece U i)]

include hU in
def SmoothOverlap (D : OverlapSystem (fun i => Piece U i)) : Prop :=
  ∀ i j,
    letI : ChartedSpace E (Piece U i) :=
      (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ChartedSpace E (Piece U j) :=
      (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
    ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞
      (D.transition i j) (D.transition i j).source

theorem quotient_isManifold
    (D : OverlapSystem (fun i => Piece U i))
    (hsmooth : SmoothOverlap U hU D) :
    letI := quotientChartedSpace U hU D
    IsManifold (𝓘(ℝ, E)) ∞ (Quotient D.setoid) := by
  letI := quotientChartedSpace U hU D
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨i, rfl⟩
  rcases he' with ⟨j, rfl⟩
  let ci := quotientChart U hU D i
  let cj := quotientChart U hU D j
  let ei := (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  letI : ChartedSpace E (Piece U i) :=
    (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI : ChartedSpace E (Piece U j) :=
    (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hc : ContDiffOn ℝ ∞ (ci.symm.trans cj) (ci.symm.trans cj).source := by
    have hs : ContDiffOn ℝ ∞
        (fun z => ((D.transition i j (ei.symm z) : Piece U j) : E))
        (ci.symm.trans cj).source := by
      intro x hx
      have hxi : x ∈ ei.target := by
        simpa [ci, ei, quotientChart] using hx.1
      have hxt : ei.symm x ∈ (D.transition i j).source := by
        exact quotientChart_comp_mem_transition_source U hU D i j hx
      have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ei.symm x := by
        apply (contMDiffOn_isOpenEmbedding_symm
          (I := 𝓘(ℝ, E)) (n := ∞) (hU i).isOpenEmbedding_subtypeVal).contMDiffAt
        simpa [ei] using ei.open_target.mem_nhds hxi
      have ht := (hsmooth i j).contMDiffAt
        ((D.transition i j).open_source.mem_nhds hxt)
      have hj := (contMDiff_isOpenEmbedding
        (I := 𝓘(ℝ, E)) (n := ∞) (hU j).isOpenEmbedding_subtypeVal).contMDiffAt
          (x := D.transition i j (ei.symm x))
      exact ((hj.comp x (ht.comp x hi)).contDiffAt).contDiffWithinAt
    apply hs.congr
    intro x hx
    exact quotientChart_comp_apply U hU D i j hx
  simpa only [mfld_simps] using hc

theorem include_isLocalDiffeomorph
    (D : OverlapSystem (fun i => Piece U i))
    (hsmooth : SmoothOverlap U hU D) (i : I) :
    letI : ChartedSpace E (Piece U i) :=
      (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := quotientChartedSpace U hU D
    IsLocalDiffeomorph (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (D.include i) := by
  letI : ChartedSpace E (Piece U i) :=
    (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI := quotientChartedSpace U hU D
  letI := quotient_isManifold U hU D hsmooth
  let ei := (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let ci := quotientChart U hU D i
  have hci : ci ∈ maximalAtlas 𝓘(ℝ, E) ∞ (Quotient D.setoid) :=
    subset_maximalAtlas ⟨i, rfl⟩
  let de : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (Piece U i) E ∞ :=
    { toPartialEquiv := ei.toPartialEquiv
      open_source := ei.open_source
      open_target := ei.open_target
      contMDiffOn_toFun :=
        (contMDiff_isOpenEmbedding (I := 𝓘(ℝ, E))
          (n := ∞) (hU i).isOpenEmbedding_subtypeVal).contMDiffOn
      contMDiffOn_invFun := by
        simpa [ei] using contMDiffOn_isOpenEmbedding_symm
          (I := 𝓘(ℝ, E)) (n := ∞) (hU i).isOpenEmbedding_subtypeVal }
  let dc : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (Quotient D.setoid) E ∞ :=
    { toPartialEquiv := ci.toPartialEquiv
      open_source := ci.open_source
      open_target := ci.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hci
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hci }
  intro x
  refine ⟨de.trans dc.symm, ?_, ?_⟩
  · change x ∈ ei.source ∧ ei x ∈ ci.target
    constructor
    · simp [ei]
    · simpa [ei, ci, quotientChart_target] using x.property
  · intro y hy
    change D.include i y = ci.symm (y : E)
    exact (quotientChart_symm_apply U hU D i y.property).symm

end Poincare.Gluing
