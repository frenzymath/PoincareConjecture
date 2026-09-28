import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Endpoint










set_option autoImplicit false

open Set Metric Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ V} {j : V → t.Carrier} {R : Set M} {boundary : Set V}

namespace OriginalRelativeNormalization

variable (D : OriginalRelativeNormalization step K j R boundary)

def comparisonOpen (i : Fin D.length) : Set V3 :=
  interior (D.activeBox i).support.space ∩ (D.motions i).protectedSource.spaceᶜ

omit [FiniteDimensional ℝ V] in
theorem comparisonOpen_open (i : Fin D.length) : IsOpen (D.comparisonOpen i) :=
  isOpen_interior.inter ((D.motions i).protectedSource.isCompact_space_of_finite
    (D.motions i).protected_finite).isClosed.isOpen_compl

omit [FiniteDimensional ℝ V] in
theorem successor_agreement (i : Fin D.length) :
    EqOn D.endpoint ((D.motions i).ambient 1 ∘ (D.states i.val).map)
      (D.prior (i.val + 1)).space := by
  intro x hx
  exact (D.stable (i.val + 1) D.length (by omega) le_rfl hx).trans
    (congrFun (D.transition i) x)

omit [FiniteDimensional ℝ V] in
theorem active_intrinsicInterior (i : Fin D.length) {x : V}
    (hx : x ∈ convexHull ℝ (D.face i : Set V)) (hxold : x ∉ (D.prior i.val).space) :
    x ∈ intrinsicInterior ℝ (convexHull ℝ (D.face i : Set V)) := by
  by_contra hn
  apply hxold (D.prefix_frontier i ?_)
  rw [← intrinsicClosure_sdiff_intrinsicInterior]
  exact ⟨subset_intrinsicClosure hx, hn⟩

omit [FiniteDimensional ℝ V] in
theorem active_coordinate_value (i : Fin D.length) {x : V}
    (hx : x ∈ convexHull ℝ (D.face i : Set V)) :
    (D.activeBox i).upper (D.endpoint x) = (D.motions i).coordinates.map 1
      ((D.activeBox i).upper ((D.states i.val).map x)) := by
  have hretain := (D.states i.val).retained
    ⟨D.face i, (D.face_range.subset ⟨i, rfl⟩).1⟩ hx
  have hsupport := (D.activeBox i).neighborhood_support hretain
  exact (D.motions i).coordinate_of_successor_agreement (D.activeBox i).support_target
    (D.successor_agreement i) ((D.prefix_succ i).symm.subset (Or.inr hx))
    hsupport.1 (interior_subset hsupport.2)

omit [FiniteDimensional ℝ V] in
theorem active_coordinate_mem_open (i : Fin D.length) {x : V}
    (hx : x ∈ convexHull ℝ (D.face i : Set V)) (hxold : x ∉ (D.prior i.val).space) :
    (D.activeBox i).upper (D.endpoint x) ∈ D.comparisonOpen i := by
  have hxK := D.source.convexHull_subset_space (D.face_range.subset ⟨i, rfl⟩).1 hx
  have hretain := (D.states i.val).retained
    ⟨D.face i, (D.face_range.subset ⟨i, rfl⟩).1⟩ hx
  have hsupport := (D.activeBox i).neighborhood_support hretain
  have hcoord := D.active_coordinate_value i hx
  refine ⟨?_, ?_⟩
  · rw [hcoord]
    have himage := ((D.motions i).coordinates.map 1).image_interior
      (D.activeBox i).support.space
    have himage' := himage.trans (congrArg interior ((D.motions i).coordinates.carrier 1))
    exact himage'.subset (mem_image_of_mem _ hsupport.2)
  · intro hw
    have hfixed := (D.motions i).coordinates.fixed_protected 1 _ hw
    have hsame := ((D.motions i).coordinates.map 1).injective
      (hcoord.symm.trans hfixed.symm)
    rw [(D.motions i).protected_space] at hw
    obtain ⟨⟨_, ⟨⟨y, hy, rfl⟩, hyQ⟩, hyval⟩, _⟩ := hw
    have hmapsame := (D.activeBox i).upper.injOn hsupport.1 hyQ (hsame.trans hyval.symm)
    have hxy : x = y := congrArg Subtype.val ((D.states i.val).embedding.injective
      (a₁ := ⟨x, hxK⟩)
      (a₂ := ⟨y, SimplicialComplex.space_subset_of_le (D.prefix_le i.val) hy⟩) hmapsame)
    exact hxold (hxy.symm ▸ hy)

omit [FiniteDimensional ℝ V] in


theorem active_carrier_iff (i : Fin D.length) {z : V3} (hz : z ∈ D.comparisonOpen i) :
    z ∈ (D.motions i).coordinates.map 1 '' (D.motions i).freeComplex.space ↔
      z ∈ (D.activeBox i).lower ''
        (D.projected '' convexHull ℝ (D.face i : Set V) ∩ (D.activeBox i).lower.source) := by
  let m := D.motions i
  let box := D.activeBox i
  rw [m.free_space]
  constructor
  · rintro ⟨w, hw, hwz⟩
    rw [m.source_space] at hw
    obtain ⟨⟨_, ⟨⟨q, hqnext, rfl⟩, hqQ⟩, hqw⟩, hwJ⟩ := hw
    have hqnot : q ∉ (D.prior i.val).space := by
      intro hqold
      have hwfixed : w ∈ m.protectedSource.space := by
        rw [m.protected_space]
        exact ⟨⟨(D.states i.val).map q,
          ⟨mem_image_of_mem _ hqold, hqQ⟩, hqw⟩, hwJ⟩
      exact hz.2 ((m.coordinates.fixed_protected 1 w hwfixed).symm.trans hwz ▸ hwfixed)
    have hqface := ((D.prefix_succ i).subset hqnext).resolve_left hqnot
    have hqcoord : box.upper (D.endpoint q) = z :=
      (D.active_coordinate_value i hqface).trans ((congrArg (m.coordinates.map 1) hqw).trans hwz)
    have hqfinalQ : D.endpoint q ∈ box.upper.source :=
      ((D.states D.length).retained
        ⟨D.face i, (D.face_range.subset ⟨i, rfl⟩).1⟩ hqface).1
    exact ⟨D.projected q, ⟨mem_image_of_mem _ hqface, box.projection_maps hqfinalQ⟩,
      (box.projection_value (D.endpoint q)).symm.trans hqcoord⟩
  · rintro ⟨_, ⟨⟨q, hqface, rfl⟩, _⟩, hqz⟩
    have hqnext := (D.prefix_succ i).symm.subset (Or.inr hqface)
    have hretain := (D.states i.val).retained
      ⟨D.face i, (D.face_range.subset ⟨i, rfl⟩).1⟩ hqface
    have hsupport := box.neighborhood_support hretain
    have hcoord : m.coordinates.map 1 (box.upper ((D.states i.val).map q)) = z :=
      (D.active_coordinate_value i hqface).symm.trans
        ((box.projection_value (D.endpoint q)).trans hqz)
    refine ⟨box.upper ((D.states i.val).map q), ?_, hcoord⟩
    rw [m.source_space]
    exact ⟨⟨(D.states i.val).map q, ⟨mem_image_of_mem _ hqnext, hsupport.1⟩, rfl⟩,
      interior_subset hsupport.2⟩

omit [FiniteDimensional ℝ V] in
theorem prior_carrier_iff (i : Fin D.length) (old : (D.prior i.val).faces)
    {z : V3} (hz : z ∈ D.comparisonOpen i) :
    z ∈ ((D.motions i).targets old).space ↔
      z ∈ (D.activeBox i).lower ''
        (D.projected '' convexHull ℝ (old.val : Set V) ∩ (D.activeBox i).lower.source) := by
  rw [(D.motions i).targets_space_of_prefix_agreement
    (D.stable i.val D.length i.isLt.le le_rfl) old]
  exact and_iff_left (interior_subset hz.1)

end OriginalRelativeNormalization
end Geometry.OriginalPLTower
