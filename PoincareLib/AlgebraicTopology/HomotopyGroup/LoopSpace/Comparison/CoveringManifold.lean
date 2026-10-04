import Mathlib.Topology.Covering.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Manifold structures pulled back through local homeomorphisms

A local homeomorphism pulls a charted atlas back to its domain. Transition
maps agree with restrictions of the original transitions, so every
restriction-closed structure groupoid, in particular the smooth one, pulls
back as well. Covering maps also preserve the Hausdorff condition.
Source: Hatcher, Section 1.3, printed pp. 63-65; MT Claim 18.16, p. 430.
-/

set_option autoImplicit false

open Set Topology OpenPartialHomeomorph
open scoped Manifold ContDiff

universe u v w

namespace IsCoveringMap

/-- A covering of a Hausdorff base is Hausdorff: separate points in different
fibers downstairs and points in the same fiber by sheets.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
theorem t2Space {E : Type u} {X : Type v} [TopologicalSpace E]
    [TopologicalSpace X] [T2Space X] {p : E → X} (hp : IsCoveringMap p) : T2Space E where
  t2 a b hab := by
    by_cases h : p a = p b
    · exact hp.isSeparatedMap a b h hab
    · obtain ⟨U, V, hU, hV, ha, hb, hUV⟩ := t2_separation h
      exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous, hV.preimage hp.continuous,
        ha, hb, hUV.preimage p⟩

end IsCoveringMap

namespace IsLocalHomeomorph

variable {E : Type u} {M : Type v} {H : Type w}
  [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace H]
  [ChartedSpace H M] {p : E → M}

/-- Pull back the chart at the image of a point along a local inverse sheet.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
noncomputable def pullbackChart (hp : IsLocalHomeomorph p) (a : E) :
    OpenPartialHomeomorph E H :=
  (hp.localInverseAt a).symm.trans (chartAt H (p a))

/-- The chosen point lies in the pulled-back chart domain.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
theorem mem_pullbackChart_source (hp : IsLocalHomeomorph p) (a : E) :
    a ∈ (hp.pullbackChart (H := H) a).source := by
  change a ∈ (hp.localInverseAt a).target ∧
    (hp.localInverseAt a).symm a ∈ (chartAt H (p a)).source
  simp

/-- The manifold atlas pulled back along a local homeomorphism.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
@[instance_reducible] noncomputable def pullbackChartedSpace (hp : IsLocalHomeomorph p) :
    ChartedSpace H E where
  atlas := Set.range (hp.pullbackChart (H := H))
  chartAt := hp.pullbackChart
  mem_chart_source := hp.mem_pullbackChart_source
  chart_mem_atlas a := Set.mem_range_self a

private theorem pullback_transition
    (hp : IsLocalHomeomorph p) (a b : E) :
    let T := (hp.pullbackChart (H := H) a).symm.trans (hp.pullbackChart b)
    let B := (chartAt H (p a)).symm.trans (chartAt H (p b))
    T.source ⊆ B.source ∧ Set.EqOn B T T.source := by
  intro T B
  have h (z : H) (hz : z ∈ T.source) :
      p ((hp.localInverseAt a) ((chartAt H (p a)).symm z)) =
        (chartAt H (p a)).symm z := by
    apply hp.apply_localInverseAt_of_mem
    exact hz.1.2
  constructor
  · intro z hz
    refine ⟨hz.1.1, ?_⟩
    change (chartAt H (p a)).symm z ∈ (chartAt H (p b)).source
    have hb := hz.2.2
    change (hp.localInverseAt b).symm
      ((hp.localInverseAt a) ((chartAt H (p a)).symm z)) ∈ (chartAt H (p b)).source at hb
    simpa only [hp.localInverseAt_symm, h z hz] using hb
  · intro z hz
    change (chartAt H (p b)) ((chartAt H (p a)).symm z) =
      (chartAt H (p b)) ((hp.localInverseAt b).symm
        ((hp.localInverseAt a) ((chartAt H (p a)).symm z)))
    rw [hp.localInverseAt_symm, h z hz]

/-- Restriction-closed chart compatibility pulls back along local
homeomorphisms. Source: Hatcher, Section 1.3, printed pp. 63-65. -/
theorem pullback_hasGroupoid (hp : IsLocalHomeomorph p)
    (G : StructureGroupoid H) [HasGroupoid M G] [ClosedUnderRestriction G] :
    @HasGroupoid H _ E _ (hp.pullbackChartedSpace (H := H)) G := by
  let := hp.pullbackChartedSpace (H := H)
  constructor
  rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
  let T := (hp.pullbackChart (H := H) a).symm.trans (hp.pullbackChart (H := H) b)
  have h := hp.pullback_transition (H := H) a b
  have hG := G.compatible (chart_mem_atlas H (p a)) (chart_mem_atlas H (p b))
  have ht := G.restr_mem_of_eqOn hG T.open_source h.2
    (inter_subset_left.trans h.1)
  change T.restr T.source ∈ G at ht
  rw [OpenPartialHomeomorph.restr_eq_of_source_subset (subset_refl T.source)] at ht
  exact ht

/-- A smooth atlas pulls back to a smooth atlas on every covering space.
Source: Hatcher, Section 1.3, printed pp. 63-65; MT Claim 18.16, p. 430. -/
theorem pullback_isManifold
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (I : ModelWithCorners 𝕜 V H) (n : ℕ∞ω) [IsManifold I n M]
    (hp : IsLocalHomeomorph p) :
    @IsManifold 𝕜 _ V _ _ H _ I n E _ (hp.pullbackChartedSpace (H := H)) := by
  let := hp.pullbackChartedSpace (H := H)
  let := hp.pullback_hasGroupoid (contDiffGroupoid n I)
  exact IsManifold.mk' I n E

end IsLocalHomeomorph
