import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.SelectedComponent
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.RawChart









set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "V3" => (Fin 3 → ℝ)

theorem RawSourceCrossing.double_image_axis
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X} {x y : E}
    (C : RawSourceCrossing e f S R x y) (z : X) (hz : z ∈ C.chart.source) :
    z ∈ f '' doubleLocusOn f S ↔ z ∈ R ∧ C.chart z 0 = 0 ∧ C.chart z 1 = 0 := by
  have hpair : z ∈ f '' doubleLocusOn f S ↔ z ∈ f '' C.left ∧ z ∈ f '' C.right := by
    constructor
    · rintro ⟨a, ⟨ha, b, hb, hab, hne⟩, haz⟩
      have hbz : f b = z := hab.symm.trans haz
      have ha' := C.whole_preimage.subset ⟨ha, by change f a ∈ C.chart.source; rwa [haz]⟩
      have hb' := C.whole_preimage.subset ⟨hb, by change f b ∈ C.chart.source; rwa [hbz]⟩
      rcases ha' with haL | haR <;> rcases hb' with hbL | hbR
      · exact (hne (congrArg Subtype.val (C.left_embedding.injective
          (a₁ := ⟨a, haL⟩) (a₂ := ⟨b, hbL⟩) hab))).elim
      · exact ⟨⟨a, haL, haz⟩, ⟨b, hbR, hbz⟩⟩
      · exact ⟨⟨b, hbL, hbz⟩, ⟨a, haR, haz⟩⟩
      · exact (hne (congrArg Subtype.val (C.right_embedding.injective
          (a₁ := ⟨a, haR⟩) (a₂ := ⟨b, hbR⟩) hab))).elim
    · rintro ⟨⟨a, ha, haz⟩, b, hb, hbz⟩
      refine ⟨a, ⟨C.left_subset ha, b, C.right_subset hb, haz.trans hbz.symm, ?_⟩, haz⟩
      rintro rfl
      exact disjoint_left.mp C.disjoint ha hb
  rw [hpair, C.left_image z hz, C.right_image z hz]
  tauto



theorem SourceCircleDecomposition.exists_isolated_component_target
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E} [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X}
    (M : SourceCircleDecomposition f S) (hf : PolyhedralPLInCharts e f S)
    (i : M.Index) {W : Set X} (hW : IsOpen W) (hAW : f '' M.pieces i ⊆ W) :
    ∃ O : Set X, IsOpen O ∧ f '' M.pieces i ⊆ O ∧ O ⊆ W ∧
      O ∩ (f '' doubleLocusOn f S) = f '' M.pieces i := by
  classical
  have : Finite M.Index := M.finite_components
  let C : Set E := ⋃ j : {j : M.Index // j ≠ i ∧ j ≠ M.mate i}, M.pieces j.val
  have hCc : IsCompact C := isCompact_iUnion (fun j ↦ M.pieces_isCompact j.val)
  have hCD : C ⊆ S := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact (M.piece_subset_double j.val hj).1
  have hCf : IsClosed (f '' C) :=
    (hCc.image_of_continuousOn (hf.continuousOn.mono hCD)).isClosed
  let O := W \ (f '' C)
  have hAO : f '' M.pieces i ⊆ O := by
    intro z hz
    refine ⟨hAW hz, ?_⟩
    rintro ⟨x, hx, hxz⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hxim := (M.piece_image_preimage i x (M.piece_subset_double j.val hj).1).mp
      (hxz.symm ▸ hz)
    exact hxim.elim (disjoint_left.mp (M.disjoint j.property.1) hj)
      (disjoint_left.mp (M.disjoint j.property.2) hj)
  refine ⟨O, hW.sdiff hCf, hAO, sdiff_subset, ?_⟩
  apply Subset.antisymm
  · rintro z ⟨hzO, x, hx, hxz⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (M.cover.subset (M.space.symm.subset hx))
    by_cases hji : j = i
    · exact ⟨x, hji ▸ hj, hxz⟩
    by_cases hjm : j = M.mate i
    · exact (M.image_mate i).subset ⟨x, hjm ▸ hj, hxz⟩
    · exact (hzO.2 ⟨x, mem_iUnion.mpr ⟨⟨j, hji, hjm⟩, hj⟩, hxz⟩).elim
  · intro z hz
    exact ⟨hAO hz, image_mono (M.piece_subset_double i) hz⟩




theorem SourceCircleDecomposition.exists_component_axis_charts
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E} [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    (M : SourceCircleDecomposition f S) (hf : PolyhedralPLInCharts e f S)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y))
    (i : M.Index) {W : Set X} (hW : IsOpen W) (hAW : f '' M.pieces i ⊆ W) :
    ∃ (O : Set X) (B : f '' M.pieces i → OpenPartialHomeomorph X V3),
      IsOpen O ∧ f '' M.pieces i ⊆ O ∧ O ⊆ W ∧
      O ∩ (f '' doubleLocusOn f S) = f '' M.pieces i ∧
      ∀ z : f '' M.pieces i,
        (z : X) ∈ (B z).source ∧ (B z).source ⊆ O ∧
        (∀ k, (e k).symm.trans (B z) ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ (B z).source,
          y ∈ f '' M.pieces i ↔ y ∈ R ∧ B z y 0 = 0 ∧ B z y 1 = 0) ∧
        ∃ (x y : E) (C : RawSourceCrossing e f S R x y),
          f x = z ∧ (B z : X → V3) = C.chart ∧ (B z).source ⊆ C.chart.source := by
  classical
  obtain ⟨O, hO, hAO, hOW, hisolated⟩ := M.exists_isolated_component_target hf i hW hAW
  have hcharts (z : f '' M.pieces i) : ∃ B : OpenPartialHomeomorph X V3,
      (z : X) ∈ B.source ∧ B.source ⊆ O ∧
      (∀ k, (e k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ B.source,
        y ∈ f '' M.pieces i ↔ y ∈ R ∧ B y 0 = 0 ∧ B y 1 = 0) ∧
      ∃ (x y : E) (C : RawSourceCrossing e f S R x y),
        f x = z ∧ (B : X → V3) = C.chart ∧ B.source ⊆ C.chart.source := by
    obtain ⟨x, hx, hxz⟩ := z.property
    let a : M.graph.space := ⟨x, M.space.symm.subset (M.piece_subset_double i hx)⟩
    obtain ⟨C⟩ := hcross x (M.piece_subset_source i hx) (M.partner a)
      (M.space.subset (M.partner a).property).1 (M.free a).symm (M.value a).symm
    let B := C.chart.restrOpen O hO
    refine ⟨B, ⟨hxz ▸ C.point, hAO z.property⟩, fun _ hy ↦ hy.2, ?_, ?_,
      x, M.partner a, C, hxz, rfl, fun _ hy ↦ hy.1⟩
    · intro k
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (C.compatible k)).mono
        ((e k).symm.trans B).open_source (fun _ hy ↦ ⟨hy.1, hy.2.1⟩)
    · intro y hy
      rw [← hisolated, mem_inter_iff, and_iff_right hy.2]
      exact C.double_image_axis y hy.1
  choose B hB using hcharts
  exact ⟨O, B, hO, hAO, hOW, hisolated, hB⟩

end PoincareConjecture.M76.Dehn.Annuli
