import PoincareConjecture.Proofs.M38.ProjectiveBallRegions
import PoincareConjecture.Proofs.M38.ProjectiveInteriorCut
import PoincareConjecture.Proofs.M38.FullCutLocalModels
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38


theorem projectiveDouble_regular_sides
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace StandardCapSpace Q]
    (C : SmoothProjectiveDoubleModel Q) :
    interior (closure C.first_region) = C.first_region ∧
      interior (closure C.second_region) = C.second_region := by
  have hfirst : closure C.first_region = C.second_regionᶜ :=
    (projectiveDouble_region_closures C).1.trans (projectiveDouble_side_complements C).1
  have hsecond : closure C.second_region = C.first_regionᶜ :=
    (projectiveDouble_region_closures C).2.trans (projectiveDouble_side_complements C).2
  constructor
  · rw [hfirst, interior_compl, hsecond, compl_compl]
  · rw [hsecond, interior_compl, hfirst, compl_compl]




theorem exists_projectiveDouble_first_cut_domain
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier)
    {O : Set projectiveCarrier.{u}.carrier} (hO : IsOpen O)
    (hp : ULift.up C.first_puncture ∈ O) :
    let E := puncturedProjectiveRegionEquivalence A C.first_model
    ∃ (e : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
      (H : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞)
      (K : Set projectiveCarrier.{u}.carrier),
      StrictMono e ∧ e 0 ∈ Ioo (-1 : ℝ) 0 ∧
      (∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-1 : ℝ) 1 →
        H (C.collar (z, s)) = C.collar (z, e s)) ∧
      H '' closure C.first_region ⊆ C.first_region ∧
      IsCompact K ∧ K ⊆ O ∧ closure (interior K) = K ∧
      ULift.up C.first_puncture ∈ interior K ∧
      Kᶜ = E.inverse '' (H '' C.first_region) ∧
      frontier K = E.inverse '' (H '' C.sphere) := by
  classical
  let E := puncturedProjectiveRegionEquivalence A C.first_model
  let f := (regionPartialDiffeomorph E isClosed_singleton.isOpen_compl
    C.first_open).toOpenPartialHomeomorph
  have hOs : Oᶜ ⊆ f.source := by
    intro x hx hxp
    exact hx (hxp ▸ hp)
  let core := f '' Oᶜ
  let : CompactSpace projectiveCarrier.{u}.carrier :=
    isCompact_univ_iff.mp projectiveSpaceform.compact
  have hcore : IsCompact core :=
    hO.isClosed_compl.isCompact.image_of_continuousOn (f.continuousOn.mono hOs)
  have hcoreU : core ⊆ C.first_region := by
    rintro _ ⟨x, hx, rfl⟩
    exact f.map_source (hOs hx)
  have hS : C.sphere ⊆ coreᶜ := by
    intro x hx hc
    exact disjoint_left.mp C.sphere_disjoint hx (Or.inl (hcoreU hc))
  obtain ⟨e, H, he, he0, hH, hHU, hfix⟩ :=
    exists_projectiveDouble_first_interior_cut C hcore.isClosed.isOpen_compl hS
  let D := H '' C.first_region
  have hD : IsOpen D := H.toHomeomorph.isOpenMap _ C.first_open
  have hclD : closure D = H '' closure C.first_region :=
    (H.toHomeomorph.image_closure _).symm
  have hDc : IsCompact (closure D) := by
    rw [hclD]
    exact (projectiveDouble_closed_sides_compact C).1.image H.contMDiff.continuous
  have hDs : closure D ⊆ f.target := hclD ▸ hHU
  have hDregular : interior (closure D) = D := by
    rw [hclD]
    change interior (H.toHomeomorph '' closure C.first_region) =
      H.toHomeomorph '' C.first_region
    rw [← H.toHomeomorph.image_interior,
      (projectiveDouble_regular_sides C).1]
  let L := f.symm '' D
  obtain ⟨hL, hLc, hclL, hfrontL⟩ :=
    f.symm.image_region_of_isCompact_closure hD hDc hDs
  have hLs : closure L ⊆ f.source := by
    rw [hclL]
    rintro _ ⟨x, hx, rfl⟩
    exact f.map_target (hDs hx)
  have hLregular : interior (closure L) = L := by
    have h := (f.symm.isImage_image_of_subset_source
      (subset_closure.trans hDs)).closure.interior.image_eq
    simp only [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_target] at h
    rw [hDregular, inter_eq_right.mpr (subset_closure.trans hDs),
      inter_eq_right.mpr (interior_subset.trans hLs)] at h
    exact h.symm
  let K := Lᶜ
  have hKO : K ⊆ O := by
    intro x hx
    by_contra hxo
    have hxs : x ∈ f.source := hOs hxo
    have hfx : f x ∈ core := mem_image_of_mem f hxo
    have hfixed : H (f x) = f x := hfix _ (by simpa using hfx)
    apply hx
    exact ⟨f x, ⟨f x, f.map_source hxs, hfixed⟩, f.left_inv hxs⟩
  have hpK : ULift.up C.first_puncture ∈ interior K := by
    rw [show K = Lᶜ from rfl, interior_compl]
    exact fun h => hLs h rfl
  refine ⟨e, H, K, he, he0, hH, hHU, hL.isClosed_compl.isCompact, hKO, ?_,
    hpK, by simp only [K, compl_compl]; rfl, ?_⟩
  · rw [show K = Lᶜ from rfl, interior_compl, closure_compl, hLregular]
  · rw [show K = Lᶜ from rfl, frontier_compl, hfrontL]
    have hfrontD : frontier D = H '' C.sphere := by
      change frontier (H.toHomeomorph '' C.first_region) = H.toHomeomorph '' C.sphere
      rw [← H.toHomeomorph.image_frontier, (projectiveDouble_region_frontiers C).1]
    rw [hfrontD]
    rfl

end PoincareConjecture.M38
