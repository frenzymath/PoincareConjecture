import Mathlib.Geometry.Manifold.Diffeomorph
open Set
open scoped Manifold ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false







namespace Poincare.Manifold
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup E'] [NormedSpace ℝ E']
 {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

@[instance_reducible]
def linearRechart (A : E ≃L[ℝ] E') : ChartedSpace E' M where
  atlas := (fun e : OpenPartialHomeomorph M E =>
    e.trans A.toHomeomorph.toOpenPartialHomeomorph) '' atlas E M
  chartAt x := (chartAt E x).trans A.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp only [OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ, mem_chart_source]
  chart_mem_atlas x := ⟨chartAt E x, chart_mem_atlas E x, rfl⟩

theorem isManifold_linearRechart (A : E ≃L[ℝ] E') :
    let := linearRechart (M := M) A
    IsManifold 𝓘(ℝ,E') ∞ M := by
  let := linearRechart (M := M) A
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  have h := (𝓘(ℝ,E)).contDiffOn_extendCoordChange
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) he) (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) he')
  have h' := A.contDiff.comp_contDiffOn
    (h.comp A.symm.contDiff.contDiffOn (by intro x hx; exact hx))
  convert h' using 1 <;> simp [mfld_simps, Function.comp_def]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem contMDiff_linearRechart_id (A : E ≃L[ℝ] E') :
    let := linearRechart (M := M) A
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E') ∞ (id : M → M) := by
  let := linearRechart (M := M) A
  dsimp only
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  apply ContDiffAt.contDiffWithinAt
  apply A.contDiff.contDiffAt.congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds (mem_chart_target E x)] with z hz
  simp only [extChartAt, mfld_simps]
  change A (chartAt E x ((chartAt E x).symm z)) = A z
  rw [(chartAt E x).right_inv hz]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem contMDiff_linearRechart_id_symm (A : E ≃L[ℝ] E') :
    let := linearRechart (M := M) A
    ContMDiff 𝓘(ℝ,E') 𝓘(ℝ,E) ∞ (id : M → M) := by
  let := linearRechart (M := M) A
  dsimp only
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  apply ContDiffAt.contDiffWithinAt
  apply A.symm.contDiff.contDiffAt.congr_of_eventuallyEq
  have hnh : ∀ᶠ z in nhds (A (chartAt E x x)),
      A.symm z ∈ (chartAt E x).target :=
    A.symm.continuous.tendsto _ |>.eventually
      ((chartAt E x).open_target.mem_nhds (by simp))
  filter_upwards [hnh] with z hz
  simp only [extChartAt, mfld_simps]
  change chartAt E x ((chartAt E x).symm (A.symm z)) = A.symm z
  rw [(chartAt E x).right_inv hz]

def linearRechartDiffeomorph (A : E ≃L[ℝ] E') :
    let := linearRechart (M := M) A
    M ≃ₘ⟮𝓘(ℝ,E),𝓘(ℝ,E')⟯ M := by
  let := linearRechart (M := M) A
  exact { toEquiv := Equiv.refl M
          contMDiff_toFun := contMDiff_linearRechart_id A
          contMDiff_invFun := contMDiff_linearRechart_id_symm A }

end Poincare.Manifold
