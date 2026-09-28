import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.ChartGluing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace PoincareConjecture.SphereCharts

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable def threeSphereStereographic (v : UnitThreeSphere) :
    OpenPartialHomeomorph UnitThreeSphere E3 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  exact stereographic' 3 v

@[simp] theorem threeSphereStereographic_source (v : UnitThreeSphere) :
    (threeSphereStereographic v).source = {v}ᶜ := by
  simp [threeSphereStereographic]

@[simp] theorem threeSphereStereographic_target (v : UnitThreeSphere) :
    (threeSphereStereographic v).target = univ := by
  simp [threeSphereStereographic]

theorem threeSphereStereographic_mem_maximalAtlas (v : UnitThreeSphere) :
    threeSphereStereographic v ∈ maximalAtlas (𝓡 3) ∞ UnitThreeSphere := by
  apply IsManifold.subset_maximalAtlas
  exact ⟨v, rfl⟩

theorem threeSphereStereographic_source_union_antipode (v : UnitThreeSphere) :
    (threeSphereStereographic v).source ∪ (threeSphereStereographic (-v)).source = univ := by
  rw [threeSphereStereographic_source, threeSphereStereographic_source]
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = v
  · right
    simpa only [hx, mem_compl_iff, mem_singleton_iff] using ne_neg_of_mem_unit_sphere ℝ v
  · exact Or.inl hx

@[simp] theorem threeSphereStereographic_apply_antipode (v : UnitThreeSphere) :
    threeSphereStereographic v (-v) = 0 := by
  simp [threeSphereStereographic, stereographic', stereographic_apply_neg]

@[simp] theorem threeSphereStereographic_symm_zero (v : UnitThreeSphere) :
    (threeSphereStereographic v).symm 0 = -v := by
  have hv : -v ∈ (threeSphereStereographic v).source := by
    rw [threeSphereStereographic_source]
    simpa only [mem_compl_iff, mem_singleton_iff, ne_comm] using
      ne_neg_of_mem_unit_sphere ℝ v
  simpa only [threeSphereStereographic_apply_antipode] using
    (threeSphereStereographic v).left_inv hv

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

theorem threeSphereStereographic_transition_target (v : UnitThreeSphere) :
    ((threeSphereStereographic v).symm.trans (threeSphereStereographic (-v))).target =
      ({0} : Set E3)ᶜ := by
  rw [← OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  simpa only [neg_neg] using threeSphereStereographic_transition_source (-v)

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

end PoincareConjecture.SphereCharts
