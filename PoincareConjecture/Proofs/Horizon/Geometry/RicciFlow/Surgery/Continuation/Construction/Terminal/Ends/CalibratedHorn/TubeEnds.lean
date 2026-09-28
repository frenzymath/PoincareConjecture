import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Frontier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.HalfNormalization
import Mathlib.Topology.Maps.Proper.Basic









noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} (Q : OpenCylinderModel U)

theorem isProperMap_coordinate_restrict {D : Set RoundCylinderSpace}
    (hD : D ⊆ univ ×ˢ Ioo (0 : ℝ) 1)
    (hclosed : IsClosed (Q.coordinate '' D)) :
    IsProperMap (fun z : D => Q.coordinate z.val) := by
  let f : D → U := fun z => ⟨Q.coordinate z.val, Q.coordinate_mem (hD z.property)⟩
  have hf : Continuous f :=
    (Q.coordinate_smooth.continuousOn.mono hD).domRestrict.subtype_mk _
  have hg : Continuous (fun x : U => Q.inverse x.val) :=
    Q.inverse_smooth.continuousOn.domRestrict
  have hcomp : (fun x : U => Q.inverse x.val) ∘ f = (Subtype.val : D → RoundCylinderSpace) := by
    funext z
    exact Q.left_inverse (hD z.property)
  have hfemb : Topology.IsEmbedding f :=
    Topology.IsEmbedding.of_comp hf hg (hcomp ▸ Topology.IsEmbedding.subtypeVal)
  have hemb : Topology.IsEmbedding (fun z : D => Q.coordinate z.val) :=
    Topology.IsEmbedding.subtypeVal.comp hfemb
  have hrange : range (fun z : D => Q.coordinate z.val) = Q.coordinate '' D := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  exact (show Topology.IsClosedEmbedding (fun z : D => Q.coordinate z.val) from
    ⟨hemb, hrange ▸ hclosed⟩).isProperMap

private theorem tail_subset_closed_of_meets (side : Bool) {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) {X : Set M} (hX : IsClosed X)
    (hmeet : (Q.tail side a ∩ X).Nonempty)
    (havoid : Disjoint (Q.tail side a) (frontier X)) : Q.tail side a ⊆ X := by
  have hsub : Q.tail side a ⊆ interior X ∪ Xᶜ := by
    intro x hx
    by_cases hxX : x ∈ X
    · exact Or.inl ((mem_interior_iff_notMem_frontier hxX).mpr
        (fun h => disjoint_left.mp havoid hx h))
    · exact Or.inr hxX
  have hmeet' : (Q.tail side a ∩ interior X).Nonempty := by
    obtain ⟨x, hx, hxX⟩ := hmeet
    exact ⟨x, hx, (mem_interior_iff_notMem_frontier hxX).mpr
      (fun h => disjoint_left.mp havoid hx h)⟩
  have hdis : Disjoint (interior X) Xᶜ :=
    disjoint_left.mpr fun _ hx hn => hn (interior_subset hx)
  exact ((Q.isConnected_tail side ha).isPreconnected.subset_left_of_subset_union
    isOpen_interior hX.isOpen_compl hdis hsub hmeet').trans interior_subset

end PoincareConjecture.OpenCylinderModel

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}



theorem exists_proper_closed_tube_tail (e : TerminalEnd K)
    {X : Set (E.extended.slice T).carrier} (hX : IsClosed X)
    (hfront : IsCompact (frontier X))
    (tube : EpsilonTubeCertificate (E.extended.metric T) X)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ X) :
    ∃ (side : Bool) (a : ℝ) (k : ℕ), a ∈ Ioo (0 : ℝ) 1 ∧ n ≤ k ∧
      tube.cylinder.closedTail side a ⊆ X ∧
      IsClosed (tube.cylinder.closedTail side a) ∧
      IsProperMap (fun z : (univ ×ˢ if side then Ico a 1 else Ioc 0 a) =>
        tube.cylinder.coordinate z.val) ∧
      ∀ m : ℕ, k ≤ m → Subtype.val '' e.tail m ⊆ tube.cylinder.tail side a := by
  let tube' : EpsilonTubeCertificate (E.extended.metric T) (Subtype.val '' e.tail n) :=
    { tube with contains_X := htail.trans tube.contains_X }
  obtain ⟨side, hside⟩ := e.exists_tube_direction n tube'
  obtain ⟨a, ha, hfalse, htrue, _, _⟩ :=
    tube.cylinder.exists_tails_disjoint_of_isCompact hfront
      (hX.frontier_subset.trans tube.contains_X)
  have hcontained (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) 1)
      (havoid : Disjoint (tube.cylinder.tail side b) (frontier X)) :
      tube.cylinder.tail side b ⊆ X := by
    obtain ⟨k, hnk, hk⟩ := hside b hb
    obtain ⟨x, hx⟩ := (e.tail_image_connected k).nonempty
    have hxX := htail (image_mono (e.nested hnk) hx)
    exact tube.cylinder.tail_subset_closed_of_meets side hb hX
      ⟨x, hk k le_rfl hx, hxX⟩ havoid
  cases side
  · have ha1 : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, ha.2.trans (by norm_num)⟩
    have hb : a / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [ha.1, ha.2]
    have hsub : tube.cylinder.closedTail false (a / 2) ⊆ X := by
      intro x hx
      have hx' := (tube.cylinder.mem_closedTail_iff false hb).mp hx
      exact hcontained a ha1 hfalse ((tube.cylinder.mem_tail_iff false ha1).mpr
        ⟨hx'.1, lt_of_le_of_lt hx'.2 (by linarith [ha.1])⟩)
    have hclosed := tube.cylinder.isClosed_closedTail_of_subset false hb hX tube.contains_X hsub
    obtain ⟨k, hnk, hk⟩ := hside (a / 2) hb
    refine ⟨false, a / 2, k, hb, hnk, hsub, hclosed, ?_, hk⟩
    exact tube.cylinder.isProperMap_coordinate_restrict
      (fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans_lt hb.2⟩) hclosed
  · have ha1 : 1 - a ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [ha.1, ha.2]
    have hb : 1 - a / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [ha.1, ha.2]
    have hsub : tube.cylinder.closedTail true (1 - a / 2) ⊆ X := by
      intro x hx
      have hx' := (tube.cylinder.mem_closedTail_iff true hb).mp hx
      exact hcontained (1 - a) ha1 htrue ((tube.cylinder.mem_tail_iff true ha1).mpr
        ⟨hx'.1, lt_of_lt_of_le (by linarith [ha.1]) hx'.2⟩)
    have hclosed := tube.cylinder.isClosed_closedTail_of_subset true hb hX tube.contains_X hsub
    obtain ⟨k, hnk, hk⟩ := hside (1 - a / 2) hb
    refine ⟨true, 1 - a / 2, k, hb, hnk, hsub, hclosed, ?_, hk⟩
    exact tube.cylinder.isProperMap_coordinate_restrict
      (fun _ hz => ⟨hz.1, hb.1.trans_le hz.2.1, hz.2.2⟩) hclosed

end PoincareConjecture.TerminalEnd
