import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.AllEdgeSigns
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.CompatibleChartLabels

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains
open AbstractSimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

theorem exists_chart_labels_of_global_chart
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (i : ι) (hi : (e i).source = univ) (S : Set X) :
    ∃ label : ∀ j, LocallyConstant {z : S | (z : X) ∈ (e j).source} PLOrientationSheet,
      ∀ j k (z : S) (hj : (z : X) ∈ (e j).source)
        (hk : (z : X) ∈ (e k).source),
        (label k ⟨z, hk⟩).val =
          plAtlasTransitionSign e hcompat j k ⟨z, hj, hk⟩ * (label j ⟨z, hj⟩).val := by
  have hi' (z : X) : z ∈ (e i).source := hi ▸ mem_univ z
  let q (j : ι) : {z : S | (z : X) ∈ (e j).source} →
      ((e i).source ∩ (e j).source : Set X) := fun z ↦ ⟨z.val, hi' z.val, z.property⟩
  have hq (j : ι) : Continuous (q j) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let sign (j : ι) := plAtlasTransitionSign e hcompat i j ∘ q j
  have hc (j : ι) : Continuous (sign j) :=
    ((isLocallyConstant_plAtlasTransitionSign e hcompat i j).comp_continuous (hq j)).continuous
  let label (j : ι) :
      LocallyConstant {z : S | (z : X) ∈ (e j).source} PLOrientationSheet :=
    ⟨fun z ↦ ⟨sign j z, plAtlasTransitionSign_ne_zero e hcompat i j (q j z)⟩,
      (IsLocallyConstant.iff_continuous _).mpr ((hc j).subtype_mk _)⟩
  refine ⟨label, ?_⟩
  intro j k z hj hk
  exact (plAtlasTransitionSign_cocycle e hcompat i j k z (hi' z) hj hk).symm

theorem exists_standard_frontier_all_edge_signs
    (K A : SimplicialComplex ℝ V3) (hAK : A ≤ K) (hA : A.faces.Finite)
    (R : Set V3) (hfront : A.space ⊆ frontier R)
    (hstars : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph V3 V3,
      C ∈ piecewiseAffineGroupoid V3 ∧ (K.closedStar p).space ⊆ C.source ∧
      (K.closedStar p).AffineOnFaces C ∧
      (C.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ C.source, y ∈ R ↔ 0 ≤ ell (C y))) :
    ∃ (number : A.vertices ↪ ℕ)
      (sigma : Triangle A.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2),
      ∀ (t u : Triangle A.vertexAbstractComplex.toPreAbstractSimplicialComplex), t ≠ u →
        ∀ s : Edge A.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          s.val ⊆ t.val → s.val ⊆ u.val →
          (sigma t + boundaryFaceParity number t.val s.val) +
            (sigma u + boundaryFaceParity number u.val s.val) = 1 := by
  classical
  let e : Unit → OpenPartialHomeomorph V3 V3 := fun _ ↦ OpenPartialHomeomorph.refl V3
  let charts := {H : OpenPartialHomeomorph V3 V3 |
    ∀ k, (e k).symm.trans H ∈ piecewiseAffineGroupoid V3}
  let q : charts → OpenPartialHomeomorph V3 V3 := Subtype.val
  have hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3 := by
    intro i j
    simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans]
      using (piecewiseAffineGroupoid V3).id_mem
  have hq : ∀ H J, (q H).symm.trans (q J) ∈ piecewiseAffineGroupoid V3 :=
    fun H J ↦ compatiblePLCharts_trans e (fun x ↦ ⟨(), mem_univ x⟩)
      hcompat H J H.property J.property
  let base : charts := ⟨e (), fun j ↦ hcompat j ()⟩
  obtain ⟨label, hlabel⟩ := exists_chart_labels_of_global_chart q hq base rfl A.space
  apply exists_frontier_all_edge_signs_of_chart_labels e K A hAK hA id R
    (fun _ _ _ _ h ↦ h) hfront ?_ hq label hlabel
  intro p hp
  obtain ⟨C, hC, hsource, hfaces, hregion⟩ := hstars p hp
  refine ⟨C, ?_, hsource, hfaces, hregion⟩
  intro j
  simpa only [e, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] using hC

end PoincareConjecture.M76.Dehn
