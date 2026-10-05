import PoincareLib.Topology.Manifold.Diffeomorph.ChartGluing
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Models
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Sphere identification from matching stereographic charts

Adapted from Mapher, `PoincareMT/Proofs/M25/Topology3D/Gluing/SphereGluing.lean`,
commit `e174c64e77c06b19667268c1dbb3cb87e0c25c4c`. Proof bodies are unchanged;
imports, namespace, and the local Euclidean-space abbreviation are reorganized.
See `references/ricci-flow/mapher/compact-cap-gluing.md`.

Two actual smooth charts onto three-space identify a manifold with the
standard three-sphere when their complete overlap is the exact antipodal
stereographic transition. Both local formulas and inverse formulas are
retained. This is the chart-gluing input for Morgan--Tian Proposition A.21,
pp. 510-514; see `tasks/M25/gluing-collar/sphere-gluing-plan.md`, sections
2-4. No formula for stereographic inversion is assumed: Mathlib's chosen
orthogonal normalizations and its transition domain remain explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace PoincareMT.SphereCharts

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The exact stereographic chart of the frozen standard three-sphere,
with the canonical dimension witness. This is the target chart for the
L1(iii) gluing step of MT A.21, pp. 510-514. -/
noncomputable def threeSphereStereographic (v : UnitThreeSphere) :
    OpenPartialHomeomorph UnitThreeSphere E3 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  exact stereographic' 3 v

/-- A stereographic chart omits precisely its pole; the L1(iii) gluing
step for MT A.21, pp. 510-514. -/
@[simp] theorem threeSphereStereographic_source (v : UnitThreeSphere) :
    (threeSphereStereographic v).source = {v}ᶜ := by
  simp [threeSphereStereographic]

/-- Each standard stereographic chart has the whole three-space as its
target; the L1(iii) gluing step for MT A.21, pp. 510-514. -/
@[simp] theorem threeSphereStereographic_target (v : UnitThreeSphere) :
    (threeSphereStereographic v).target = univ := by
  simp [threeSphereStereographic]

/-- The chosen stereographic chart belongs to the existing smooth atlas
of the frozen three-sphere; the L1(iii) step for MT A.21, pp. 510-514. -/
theorem threeSphereStereographic_mem_maximalAtlas (v : UnitThreeSphere) :
    threeSphereStereographic v ∈ maximalAtlas (𝓡 3) ∞ UnitThreeSphere := by
  apply IsManifold.subset_maximalAtlas
  exact ⟨v, rfl⟩

/-- The two antipodal charts cover the sphere; the L1(iii) gluing step
for MT A.21, pp. 510-514. -/
theorem threeSphereStereographic_source_union_antipode (v : UnitThreeSphere) :
    (threeSphereStereographic v).source ∪ (threeSphereStereographic (-v)).source = univ := by
  rw [threeSphereStereographic_source, threeSphereStereographic_source]
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = v
  · right
    simpa only [hx, mem_compl_iff, mem_singleton_iff] using ne_neg_of_mem_unit_sphere ℝ v
  · exact Or.inl hx

/-- The antipode has zero coordinate in the exact standard chart,
independently of its chosen orthogonal basis; MT A.21, pp. 510-514,
`gluing-collar/sphere-gluing-plan.md`, section 3. -/
@[simp] theorem threeSphereStereographic_apply_antipode (v : UnitThreeSphere) :
    threeSphereStereographic v (-v) = 0 := by
  simp [threeSphereStereographic, stereographic', stereographic_apply_neg]

/-- Zero in the chart maps back to the antipode; this keeps the excluded
coordinate point explicit in the L1(iii) construction for MT A.21,
pp. 510-514. -/
@[simp] theorem threeSphereStereographic_symm_zero (v : UnitThreeSphere) :
    (threeSphereStereographic v).symm 0 = -v := by
  have hv : -v ∈ (threeSphereStereographic v).source := by
    rw [threeSphereStereographic_source]
    simpa only [mem_compl_iff, mem_singleton_iff, ne_comm] using
      ne_neg_of_mem_unit_sphere ℝ v
  simpa only [threeSphereStereographic_apply_antipode] using
    (threeSphereStereographic v).left_inv hv

/-- The antipodal coordinate transition is defined precisely away from
zero. No totalized chart value at the pole is used in the L1(iii) gluing
step for MT A.21, pp. 510-514. -/
theorem threeSphereStereographic_transition_source (v : UnitThreeSphere) :
    ((threeSphereStereographic v).symm.trans (threeSphereStereographic (-v))).source =
      ({0} : Set E3)ᶜ := by
  ext x
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    threeSphereStereographic_target, threeSphereStereographic_source]
  simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, mem_compl_iff,
    mem_singleton_iff]
  constructor
  · intro hx hzero
    exact hx (hzero ▸ threeSphereStereographic_symm_zero v)
  · intro hx heq
    apply hx
    have h := congrArg (threeSphereStereographic v) heq
    rw [(threeSphereStereographic v).right_inv (by simp),
      threeSphereStereographic_apply_antipode] at h
    exact h

/-- The antipodal transition also has exactly punctured three-space as
target; the L1(iii) gluing step for MT A.21, pp. 510-514. -/
theorem threeSphereStereographic_transition_target (v : UnitThreeSphere) :
    ((threeSphereStereographic v).symm.trans (threeSphereStereographic (-v))).target =
      ({0} : Set E3)ᶜ := by
  rw [← OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  simpa only [neg_neg] using threeSphereStereographic_transition_source (-v)

/-- Two smooth charts onto the whole three-space, whose complete
coordinate overlap is the exact antipodal stereographic transition,
identify the existing manifold with the standard three-sphere. All
forward and inverse chart formulas are retained. This is L1(iii) for
MT A.21, pp. 510-514; `gluing-collar/sphere-gluing-plan.md`, section 3. -/
theorem exists_diffeomorph_unitThreeSphere_of_stereographic
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace E3 Y]
    (e₀ e₁ : OpenPartialHomeomorph Y E3) (v : UnitThreeSphere)
    (hcover : e₀.source ∪ e₁.source = univ)
    (htarget₀ : e₀.target = univ) (htarget₁ : e₁.target = univ)
    (he₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₀ e₀.source)
    (he₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₁ e₁.source)
    (hei₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₀.symm e₀.target)
    (hei₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₁.symm e₁.target)
    (htrans : OpenPartialHomeomorph.EqOnSource (e₀.symm.trans e₁)
      ((threeSphereStereographic v).symm.trans (threeSphereStereographic (-v)))) :
    ∃ d : Diffeomorph (𝓡 3) (𝓡 3) Y UnitThreeSphere ∞,
      EqOn d ((threeSphereStereographic v).symm ∘ e₀) e₀.source ∧
      EqOn d ((threeSphereStereographic (-v)).symm ∘ e₁) e₁.source ∧
      EqOn d.symm (e₀.symm ∘ threeSphereStereographic v)
        (threeSphereStereographic v).source ∧
      EqOn d.symm (e₁.symm ∘ threeSphereStereographic (-v))
        (threeSphereStereographic (-v)).source := by
  have hc₀ := threeSphereStereographic_mem_maximalAtlas v
  have hc₁ := threeSphereStereographic_mem_maximalAtlas (-v)
  exact OpenPartialHomeomorph.exists_diffeomorph_of_chart_transition e₀ e₁
    (threeSphereStereographic v) (threeSphereStereographic (-v)) hcover
    (threeSphereStereographic_source_union_antipode v)
    (htarget₀.trans (threeSphereStereographic_target v).symm)
    (htarget₁.trans (threeSphereStereographic_target (-v)).symm)
    he₀ he₁ hei₀ hei₁ (contMDiffOn_of_mem_maximalAtlas hc₀)
    (contMDiffOn_of_mem_maximalAtlas hc₁) (contMDiffOn_symm_of_mem_maximalAtlas hc₀)
    (contMDiffOn_symm_of_mem_maximalAtlas hc₁) htrans

end PoincareMT.SphereCharts

