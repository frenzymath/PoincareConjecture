import PoincareConjecture.Proofs.M76.Mathlib.ParametricConvexExtension
import PoincareConjecture.Proofs.M76.Mathlib.ConvexCoreCollar
import Mathlib.Topology.ContinuousOn

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace ContinuousMap

variable {E B Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace B] [LocallyCompactSpace B] [TopologicalSpace Z]

theorem exists_parametric_convexCore_replacement {D : Set E}
    (hD : IsCompact D) (hc : Convex ℝ D) (hi : (interior D).Nonempty)
    (f : C(E × B, Z)) (T : Set Z) [ContractibleSpace T]
    (hfront : ∀ x ∈ frontier D, ∀ b : B, f (x, b) ∈ T) :
    ∃ g : C(E × B, Z),
      (∀ x ∉ interior D, ∀ b : B, g (x, b) = f (x, b)) ∧
      ∀ x ∈ D, ∀ b : B, g (x, b) ∈ T := by
  classical
  let b : C(frontier D × B, T) :=
    ⟨fun z => ⟨f (z.1, z.2), hfront z.1 z.1.property z.2⟩,
      (f.continuous.comp (continuous_subtype_val.prodMap continuous_id)).subtype_mk _⟩
  obtain ⟨e, he⟩ := exists_convexBody_parametric_extension hD.isClosed hc hi hD.isBounded b
  let g : E × B → Z := fun z =>
    if hx : z.1 ∈ D then (e (⟨z.1, hx⟩, z.2) : Z) else f z
  have hfix : EqOn g f (Prod.fst ⁻¹' (interior D)ᶜ) := by
    intro z hz
    by_cases hzd : z.1 ∈ D
    · have hzf : z.1 ∈ frontier D := by
        rw [frontier, hD.isClosed.closure_eq]
        exact ⟨hzd, hz⟩
      change (if hx : z.1 ∈ D then (e (⟨z.1, hx⟩, z.2) : Z) else f z) = f z
      rw [dif_pos hzd]
      exact congrArg Subtype.val (he ⟨z.1, hzf⟩ z.2)
    · simp only [g, dif_neg hzd]
  have hcontD : ContinuousOn g (Prod.fst ⁻¹' D) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let k : (Prod.fst ⁻¹' D : Set (E × B)) → D × B :=
      fun z => (⟨z.1.1, z.2⟩, z.1.2)
    have hk : Continuous k :=
      (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
    convert (continuous_subtype_val.comp e.continuous).comp hk using 1
    ext z
    have hz : z.1.1 ∈ D := z.property
    simp only [domRestrict_apply, g, dif_pos hz]
    rfl
  have hcover : (Prod.fst ⁻¹' D : Set (E × B)) ∪
      Prod.fst ⁻¹' (interior D)ᶜ = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z.1 ∈ D
    · exact Or.inl hz
    · exact Or.inr (fun h => hz (interior_subset h))
  have hg : Continuous g := by
    have h := hcontD.union_of_isClosed (f.continuous.continuousOn.congr hfix)
      (hD.isClosed.preimage continuous_fst) (isOpen_interior.isClosed_compl.preimage
        continuous_fst)
    rw [hcover] at h
    exact continuousOn_univ.mp h
  refine ⟨⟨g, hg⟩, fun x hx b => hfix hx, ?_⟩
  intro x hx b
  change (if hy : x ∈ D then (e (⟨x, hy⟩, b) : Z) else f (x, b)) ∈ T
  rw [dif_pos hx]
  exact (e (⟨x, hx⟩, b)).property

theorem exists_parametric_convexCore_replacement_near_compl {C U : Set E}
    (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    (hU : IsOpen U) (hfront : frontier C ⊆ U)
    (f : C(E × B, Z)) (T : Set Z) [ContractibleSpace T]
    (hmem : ∀ x ∈ C ∩ U, ∀ b : B, f (x, b) ∈ T) :
    ∃ g : C(E × B, Z),
      (∀ᶠ x in 𝓝ˢ ((interior C)ᶜ), ∀ b : B, g (x, b) = f (x, b)) ∧
      ∀ x ∈ C, ∀ b : B, g (x, b) ∈ T := by
  obtain ⟨D, hD, hDc, hDi, hDC, hcollar⟩ := hC.exists_convex_innerCore hc hi hU hfront
  have hDf : frontier D ⊆ C ∩ U := by
    intro x hx
    have hxd : x ∈ D := hD.isClosed.frontier_subset hx
    have hxc : x ∈ C := interior_subset (hDC hxd)
    exact ⟨hxc, hcollar ⟨hxc, hx.2⟩⟩
  obtain ⟨g, hfix, hgm⟩ := f.exists_parametric_convexCore_replacement hD hDc hDi T
    (fun x hx => hmem x (hDf hx))
  refine ⟨g, ?_, ?_⟩
  · have hnear : Dᶜ ∈ 𝓝ˢ ((interior C)ᶜ) :=
      hD.isClosed.isOpen_compl.mem_nhdsSet.mpr (compl_subset_compl.mpr hDC)
    filter_upwards [hnear] with x hx b
    exact hfix x (fun hxi => hx (interior_subset hxi)) b
  · intro x hx b
    by_cases hxd : x ∈ D
    · exact hgm x hxd b
    · have hxi : x ∉ interior D := fun h => hxd (interior_subset h)
      rw [hfix x hxi b]
      exact hmem x ⟨hx, hcollar ⟨hx, hxi⟩⟩ b

end ContinuousMap
