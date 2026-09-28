import PoincareConjecture.Proofs.M76.Rigidity.SourceInteriorPairChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Charts.TangentialAtlas







set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

private theorem mixed_transition_PL
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (H J : OpenPartialHomeomorph X C3)
    (hH : ∀ i, LocallyPiecewiseAffineOn (H.symm.trans (e i))
      (H.symm.trans (e i)).source)
    (hJ : ∀ i, LocallyPiecewiseAffineOn ((e i).symm.trans J)
      ((e i).symm.trans J).source) :
    LocallyPiecewiseAffineOn (H.symm.trans J) (H.symm.trans J).source := by
  apply LocallyPiecewiseAffineOn.locality
  intro z hz
  obtain ⟨i, hi⟩ := hcover (H.symm z)
  let T := (H.symm.trans (e i)).trans ((e i).symm.trans J)
  have hzT : z ∈ T.source := by
    refine ⟨⟨hz.1, hi⟩, (e i).map_source hi, ?_⟩
    change (e i).symm (e i (H.symm z)) ∈ J.source
    rw [(e i).left_inv hi]
    exact hz.2
  have hT := (hJ i).comp (hH i)
  have hlocal : LocallyPiecewiseAffineOn (H.symm.trans J) T.source := by
    apply hT.congr
    intro y hy
    change J ((e i).symm (e i (H.symm y))) = J (H.symm y)
    have hyi : H.symm y ∈ (e i).source := hy.1.2
    rw [(e i).left_inv hyi]
  exact ⟨T.source, hzT, hlocal.mono
    ((H.symm.trans J).open_source.inter T.open_source) inter_subset_right⟩

theorem exists_original_planar_interior_flattening_atlas
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    (j : V2 → X) (hj : PolyhedralPLInCharts e j K.space)
    (hi : IsEmbedding (fun z : K.space => j z)) :
    ∃ A : BrownCollar.FlatteningAtlas P2 (j '' interior K.space)
        (j '' interior K.space),
      A.indexAt = id ∧
      (∀ x, A.chart x x = 0) ∧
      (∀ i x, LocallyPiecewiseAffineOn ((e i).symm.trans (A.chart x))
          ((e i).symm.trans (A.chart x)).source ∧
        LocallyPiecewiseAffineOn ((A.chart x).symm.trans (e i))
          ((A.chart x).symm.trans (e i)).source) ∧
      ∀ x y, A.transition x y ∈ piecewiseAffineGroupoid C3 := by
  classical
  let S := j '' interior K.space
  have hjinj : InjOn j K.space := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hi.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw)
  have hfront : frontier K.space ⊆ K.space :=
    (K.isCompact_space_of_finite hK).isClosed.frontier_subset
  have hclosed : IsClosed (j '' frontier K.space) :=
    ((K.isCompact_space_of_finite hK).of_isClosed_subset isClosed_frontier hfront).image_of_continuousOn
      (hj.continuousOn.mono hfront) |>.isClosed
  have hchart (x : S) : ∃ H : OpenPartialHomeomorph X C3,
      (x : X) ∈ H.source ∧ H x = 0 ∧
      (∀ y ∈ H.source, y ∈ S ↔ (H y).2 = 0) ∧
      ∀ i, LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source ∧
        LocallyPiecewiseAffineOn (H.symm.trans (e i)) (H.symm.trans (e i)).source := by
    obtain ⟨z, hz, hzx⟩ := x.property
    obtain ⟨i, hxi⟩ := hcover x
    have hzavoid : j z ∈ (j '' frontier K.space)ᶜ := by
      rintro ⟨w, hw, hwz⟩
      have heq := hjinj (hfront hw) (interior_subset hz) hwz
      exact (heq ▸ hw).2 hz
    obtain ⟨H, hxH, hHs, _, hHx, hHS, hH⟩ :=
      exists_original_interior_disk_pair_chart K hK hj hi (e i) (fun k => he k i)
        ⟨z, interior_subset hz⟩ hz (hzx.symm ▸ hxi) hclosed.isOpen_compl hzavoid
    refine ⟨H, hzx ▸ hxH, hzx ▸ hHx, ?_, hH⟩
    intro y hy
    refine Iff.trans ?_ (hHS y hy)
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact mem_image_of_mem j (interior_subset hw)
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, ?_, rfl⟩
      by_contra hn
      exact (hHs hy).1 ⟨w, ⟨subset_closure hw, hn⟩, rfl⟩
  choose H hxH hHx hHS hH using hchart
  let A : BrownCollar.FlatteningAtlas P2 S S :=
    { chart := H
      pair := hHS
      indexAt := id
      mem_source_at := hxH }
  refine ⟨A, rfl, hHx, fun i x => hH x i, ?_⟩
  intro x y
  exact ⟨mixed_transition_PL e hcover (H x) (H y) (fun i => (hH x i).2)
      (fun i => (hH y i).1),
    mixed_transition_PL e hcover (H y) (H x) (fun i => (hH y i).2)
      (fun i => (hH x i).1)⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
