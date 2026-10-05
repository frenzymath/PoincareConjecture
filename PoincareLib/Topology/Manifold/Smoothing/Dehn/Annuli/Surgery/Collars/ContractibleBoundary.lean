import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surgery.Collars.SourceAlternatives
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Circles.Resolution.BoundaryCorrespondence

/-! # Whole boundary correspondence from the actual contractible collar -/

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareMT.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

/-- Reflect only the depth coordinate of the actual collar. This constructs
the full inner-to-outer boundary map and preserves the complete periodic
circle parameter, including the closing point. -/
theorem exists_collar_inner_outer_boundary_homeomorph
    {A : Set P2} {l r : ℝ} (B : OrientedPolygonCollar l r A)
    (hr : 0 < r) (hwidth : 4 * r < l) :
    ∃ eb : B.inner.boundary ℝ ≃ₜ B.outer.boundary ℝ,
      eb.IsFinitePL ∧
      ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * l)),
        (eb ⟨B.chart ⟨annulusMap l (by linarith)
          ((s : AddCircle (4 * l)), r), annulus_period_point_mem hr hwidth _
            ⟨r, by constructor <;> linarith⟩⟩,
          (B.inner_depth _).mpr (depth_annulusMap (by linarith)
            (by simpa only [abs_of_pos hr] using hwidth) _)⟩ : P2) =
        B.chart ⟨annulusMap l (by linarith)
          ((s : AddCircle (4 * l)), -r), annulus_period_point_mem hr hwidth _
            ⟨-r, by constructor <;> linarith⟩⟩ := by
  obtain ⟨R, hR, hdepth, hperiod⟩ := exists_square_annulus_depth_reflection hr hwidth
  have hb := oriented_collar_boundary_subsets B
  let c := R.trans B.chart
  have hc : c.IsFinitePL := hR.trans B.chart_PL
  have hlevel (p : squareAnnulus l r) : (c p : P2) ∈ B.outer.boundary ℝ ↔ depth l p = r := by
    change (B.chart (R p) : P2) ∈ B.outer.boundary ℝ ↔ _
    rw [B.outer_depth, hdepth]
    exact neg_inj
  obtain ⟨eb, heb, _, _, hvalue⟩ := exists_synchronized_collar_boundary_homeomorph
    B.inner B.outer B.inner_simplicial B.inner_injective hb.2 hb.1
    B.chart c B.chart_PL hc B.inner_depth hlevel
  refine ⟨eb, heb, ?_⟩
  intro s hs
  rw [hvalue]
  · change (B.chart (R _) : P2) = _
    apply congrArg (fun p ↦ (B.chart p : P2))
    apply Subtype.ext
    exact hperiod s hs ⟨r, by constructor <;> linarith⟩
  · exact depth_annulusMap (by linarith) (by simpa only [abs_of_pos hr] using hwidth) _

end PoincareMT.M76.Dehn.Annuli
