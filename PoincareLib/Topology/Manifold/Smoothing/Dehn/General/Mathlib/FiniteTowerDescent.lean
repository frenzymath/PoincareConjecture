import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.OriginalPLSuccessor
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.MarkedBoundaryPLLoopDisk
import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleArc.Mathlib.FiniteDoubleArcSurgery
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.WhiskeredLoopSplit

/-!
# Backward folding of one marked disk through a finite PL tower

This file supplies the conditional section-12 bookkeeping and a conversion
from a selected section-11 candidate to a typed stage disk. The conversion
uses the exact inverse-class convention of derivation 022, section 2.
Candidate geometry and the one-step descent remain unproved; in particular,
there is no asserted homotopy between the old and the selected new rim.
See corrected derivation 037.
-/

set_option autoImplicit false

universe u

open Set Metric Geometry Topology
open PoincareMT.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- An embedded disk at an actual tower stage, with a typed marked rim and
an actual path from the fixed basepoint. The region, mark and subgroup are
fixed in `M`; the map, rim and path can all change under surgery. -/
structure StageMarkedDisk
    (st : Stage e S f r C) (R Fmark : Set M) (base : Fmark)
    (J : Subgroup (FundamentalGroup Fmark base)) where
  map : V2 → st.Carrier
  rim : C(Q, Fmark)
  piecewiseAffine : PolyhedralPLInCharts st.charts map D
  embedding : Topology.IsEmbedding (fun x : D => map x.val)
  inside : MapsTo map D (st.projection ⁻¹' R)
  boundary_values : ∀ x : Q, st.projection (map x.val) = (rim x : M)
  whole_boundary_iff : ∀ x : D,
    map x.val ∈ frontier (st.projection ⁻¹' R) ↔ (x : V2) ∈ Q
  basepath : Path base (rim squareRimBase)
  outside : basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J

/-- Convert a selected candidate with proved geometry to a stage disk.
The context sets, subgroup and inverse word are identified explicitly.
This derives the outside-subgroup conclusion from the selector, without
assuming it again or imposing a homotopy with the pre-surgery rim.
See derivation 037, sections 3 and 5. -/
def stageMarkedDiskOfCandidate
    {st : Stage e S f r C} {R Fmark : Set M} {base : Fmark}
    {J : Subgroup (FundamentalGroup Fmark base)}
    (ctx : DoubleArcContext V2 st.Carrier (FundamentalGroup Fmark base))
    (candidate : DoubleArcCandidate ctx)
    (hsource : ctx.source = D) (hboundary : ctx.boundary = Q)
    (hregion : ctx.region = st.projection ⁻¹' R)
    (hfrontier : ctx.frontier = frontier (st.projection ⁻¹' R))
    (hnormal : ctx.normal = J)
    (hpl : PolyhedralPLInCharts st.charts candidate.map D)
    (hembedding : Topology.IsEmbedding (fun x : D => candidate.map x.val))
    (rim : C(Q, Fmark))
    (hrim : ∀ x : Q, st.projection (candidate.rim x.val) = (rim x : M))
    (basepath : Path base (rim squareRimBase))
    (hword : candidate.word =
      (basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous))⁻¹)
    (houtside : candidate.word ∉ ctx.normal) : StageMarkedDisk st R Fmark base J where
  map := candidate.map
  rim := rim
  piecewiseAffine := hpl
  embedding := hembedding
  inside := by
    intro x hx
    simpa only [hregion] using candidate.image_mem x (hsource.symm ▸ hx)
  boundary_values := by
    intro x
    rw [candidate.rim_eq x.val (hboundary.symm ▸ x.property)]
    exact hrim x
  whole_boundary_iff := by
    intro x
    simpa only [hfrontier, hboundary] using
      candidate.proper x.val (hsource.symm ▸ x.property)
  basepath := basepath
  outside := by
    intro h
    apply houtside
    rw [hnormal, hword]
    exact J.inv_mem h

/-- Backward induction over the finite reflexive-transitive tower relation.
The predecessor operation is the exact one-step geometric obligation; the
induction itself introduces no additional geometric premise. -/
theorem backward_fold_reaches
    {α : Type u} {rel : α → α → Prop} {P : α → Prop}
    (back : ∀ {a b}, rel a b → P b → P a)
    {a b : α} (h : Relation.ReflTransGen rel a b) (hb : P b) : P a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hb
  | head hab htail ih => exact back hab ih

/-- Conditional finite-chain induction on actual tower steps. The premise
`one_step` is the still-open geometric descent, not a theorem provided here.
Its output permits unchanged disks and circle-only histories as well as
arc surgery. See derivation 037, section 5. -/
theorem nonempty_stage_marked_disk_of_reaches
    {s0 st : Stage e S f r C} {R Fmark : Set M} {base : Fmark}
    {J : Subgroup (FundamentalGroup Fmark base)}
    (hreach : Reaches s0 st)
    (terminal : Nonempty (StageMarkedDisk st R Fmark base J))
    (one_step : ∀ {s t : Stage e S f r C}, Nonempty (Step s t) →
      StageMarkedDisk t R Fmark base J → Nonempty (StageMarkedDisk s R Fmark base J)) :
    Nonempty (StageMarkedDisk s0 R Fmark base J) := by
  refine backward_fold_reaches (P := fun s =>
    Nonempty (StageMarkedDisk s R Fmark base J))
    (rel := fun a b => Nonempty (Step a b)) ?_ hreach terminal
  intro s t hstep hstate
  rcases hstate with ⟨upper⟩
  exact one_step hstep upper

end Geometry.OriginalPLTower
