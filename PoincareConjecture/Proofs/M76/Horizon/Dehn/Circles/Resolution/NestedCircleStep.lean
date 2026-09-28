import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.NestedInsertion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.NestedSourceRestriction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.OriginalRetention
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.OrdinaryModel

set_option autoImplicit false

open Set Metric Geometry
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
  {D : OrdinaryIntervalMarkedModel old i} {L d : ℝ}

theorem PairedCircleCollars.exists_nested_circle_resolution
    (G : PairedCircleCollars D L d) (hd : 0 < d) (hwidth : 4 * d < L)
    {b : ℝ} (hb : 0 < b) (hbd : b < d)
    (hf : PolyhedralPLInCharts e f D2)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (j : Fin 2)
    (hnest : closure (G.collar j.rev).outer.inside ⊆ (G.collar j).inner.inside) :
    ∃ g : V2 → X, PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧ EqOn g f Q2 ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 < doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) := by
  let P := (G.collar j).outer
  let I := (G.collar j).inner
  let Q := (G.collar j.rev).inner
  have hQI : closure Q.inside ⊆ I.inside :=
    (G.collar j.rev).nested.trans (subset_closure.trans hnest)
  obtain ⟨H, J, a, g, hH, hJ, hJH, hJimage, haemb, haPL, hgPL, hglocal,
    hJvalue, houtside, hrim, hcollar, hfullimage, hcross, hpreimage,
    hproper, hball, hasub, haperiod⟩ :=
    G.exists_nested_insertion hd hwidth hb hbd hf hcompat j hnest
  have hkeep (x : closure Q.inside) : g (H x) = f x := by
    rw [← hJH x]
    exact hJvalue x x.property
  obtain ⟨copy, facts, hcopyQ, hcopyO, hcopyPL⟩ :=
    _root_.Dehn.exists_nested_retained_fibers P I Q
      (G.collar j).outer_simplicial (G.collar j).outer_injective
      (G.collar j).inner_simplicial (G.collar j).inner_injective
      (G.collar j.rev).inner_simplicial (G.collar j.rev).inner_injective
      (G.boundaries_interior j).1 (G.boundaries_interior j.rev).2
      (G.collar j).nested hQI H hH (G.collar j).regionChart f g a
      haemb.injective hkeep houtside hcollar hcross
  obtain ⟨hwhole, _, hremoved, _, havoid⟩ := G.nested_retention hd j hnest
  obtain ⟨Hopen⟩ := _root_.Dehn.nested_retained_open_source_restriction P I Q
    (G.collar j).outer_simplicial (G.collar j).outer_injective
    (G.collar j).inner_simplicial (G.collar j).inner_injective
    (G.collar j.rev).inner_simplicial (G.collar j.rev).inner_injective
    (G.boundaries_interior j).1 (G.collar j).nested hQI H hH copy facts
    hcopyQ hcopyO (fun x hx hg => disjoint_left.mp havoid ⟨hx, hg⟩)
  obtain ⟨Mnew, hboundaryCount, hinteriorCount⟩ :=
    facts.ordinary_circle_resolution old hf.continuousOn hgPL.continuousOn hcopyPL Hopen
      hwhole (if j = 0 then i else old.mate i) (G.selected_disjoint_rim j) hremoved
  have hPsq : closure P.inside ⊆ ball 0 1 := by
    obtain ⟨_, _, _, h⟩ := _root_.Dehn.polygon_source_region P
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
      (G.collar j).outer_simplicial (G.collar j).outer_injective
      (convex_ball _ _) (G.boundaries_interior j).1
    exact h
  have hQsq : closure Q.inside ⊆ D2 :=
    (hQI.trans (subset_closure.trans (G.collar j).nested)).trans
      (subset_closure.trans (hPsq.trans ball_subset_closedBall))
  have hgR : MapsTo g D2 R := by
    intro x hx
    rcases hfullimage.subset (mem_image_of_mem g hx) with (hQ | hO) | hA
    · obtain ⟨y, hy, heq⟩ := hQ
      exact heq ▸ hin (hQsq hy)
    · obtain ⟨y, hy, heq⟩ := hO
      exact heq ▸ hin hy.1
    · obtain ⟨z, hz, heq⟩ := hasub hA
      exact heq ▸ interior_subset (G.tube_interior hz)
  have htube : Disjoint (G.tube '' _root_.Dehn.identityTube L d) (frontier R) := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    exact disjoint_left.mp disjoint_interior_frontier (G.tube_interior hz) hx
  exact ⟨g, hgPL, hgR, hrim, (hproper (frontier R) hfront htube).1,
    hboundaryCount, hinteriorCount, Mnew⟩

end PoincareConjecture.M76.Dehn
