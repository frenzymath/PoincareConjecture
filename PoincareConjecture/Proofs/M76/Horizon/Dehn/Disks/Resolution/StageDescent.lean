import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Resolution.StageProjectionReduction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.CircleTermination










set_option autoImplicit false
open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1



theorem Step.nonempty_descended_marked_disk
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
    {f : V2 → M} {r : M → ℝ} {C : Set M}
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {J : Subgroup (FundamentalGroup Fmark base)} [J.Normal]
    (old : StageMarkedDisk t R Fmark base J) :
    Nonempty (StageMarkedDisk s R Fmark base J) := by
  obtain ⟨_initial, g, rim, path, model, _hmodel, hg, hgR, hgRim, _hgF,
    hgFront, hgOut, hgZero, _hgCount, _hgEmb, _hgSelf⟩ :=
    step.exists_marked_projection_with_self_paired_components he hF hopen old
  have heS : PoincareConjecture.M76.PLDomain s.charts (s.projection ⁻¹' R) :=
    ⟨s.cover, s.compatible, he.closed.preimage s.projection.continuous,
      s.halfspace_boundary he.halfspace⟩
  obtain ⟨a, modelA, ha, haR, haRim, haFront, haBoundary, haZero⟩ :=
    model.exists_disk_without_interior_double_curves hg heS hgR hgFront
  have haBoundaryZero : doubleBoundaryComponentCount a D2 Q2 = 0 :=
    Nat.eq_zero_of_le_zero (haBoundary.trans_eq hgZero)
  exact ⟨{ map := a
           rim := rim
           piecewiseAffine := ha
           embedding := modelA.isEmbedding_of_PL_counts_zero ha haBoundaryZero haZero
           inside := haR
           boundary_values := fun x ↦
             (congrArg s.projection (haRim x.property)).trans (hgRim x)
           whole_boundary_iff := fun x ↦ haFront x x.property
           basepath := path
           outside := hgOut }⟩



theorem nonempty_folded_stage_marked_disk
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
    {f : V2 → M} {r : M → ℝ} {C : Set M}
    {s0 st : Stage e S f r C} {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {J : Subgroup (FundamentalGroup Fmark base)} [J.Normal]
    (hreach : Reaches s0 st) (terminal : StageMarkedDisk st R Fmark base J) :
    Nonempty (StageMarkedDisk s0 R Fmark base J) := by
  apply nonempty_stage_marked_disk_of_reaches hreach ⟨terminal⟩
  intro s t hstep upper
  obtain ⟨step⟩ := hstep
  exact step.nonempty_descended_marked_disk he hF hopen upper

end Geometry.OriginalPLTower
