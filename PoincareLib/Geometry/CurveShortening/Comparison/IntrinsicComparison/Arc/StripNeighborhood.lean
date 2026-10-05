import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Two.ArcStripSeparation

/-! A fixed strip can be made uniformly thin inside any open neighborhood
of its compact axis. The original map and physical cuts are retained.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, including Claim 19.40,
pp. 470-471. These project constructions provide actual fitted boundary pieces and
contacts for the regional Gauss--Bonnet arguments.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology
open Poincare.Topology.Plane.Curves

namespace PoincareMT

/-- A fixed strip has a positive uniform width whose whole image lies in any open
neighborhood of its compact axis. Source:
`proof-work/tasks/M64/derivations/2026-09-27-joined-orientation-and-attachments.md`, Section
7. -/
theorem m64Intrinsic_exists_strip_neighborhood_width
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsource : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ F.source)
    {O : Set AnnulusCoordinates} (hO : IsOpen O)
    (haxis : ∀ t ∈ Icc (0 : ℝ) 1, F (t, (0 : ℝ)) ∈ O) :
    ∃ delta > 0, Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ F.source ∧
      F '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta) ⊆ O := by
  let H := F.restrOpen (F.source ∩ F ⁻¹' O) (F.isOpen_inter_preimage hO)
  have hs : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ H.source :=
    fun t ht => ⟨hsource t ht, hsource t ht, haxis t ht⟩
  obtain ⟨delta, hdelta, hstrip⟩ := exists_strip_source_width H hs
  refine ⟨delta, hdelta, fun q hq => (hstrip hq).1, ?_⟩
  rintro z ⟨q, hq, rfl⟩
  exact (hstrip hq).2.2

end PoincareMT
