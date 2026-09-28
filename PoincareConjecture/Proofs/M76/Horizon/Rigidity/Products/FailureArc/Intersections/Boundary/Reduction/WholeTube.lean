import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Construction

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem nonempty_original_whole_intersection_tube
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X} (he : PLDomain e R)
    {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann) (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfp : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgp : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hboundary : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
      ∃ B : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false))
    (hball : IsFinitePLBallPair ℝ (Ann ∩ g ⁻¹' (f '' Ann))
      ((Ann ∩ g ⁻¹' (f '' Ann)) ∩ frontier Ann))
    (hW : IsOpen W) (hCW : f '' Ann ∩ g '' Ann ⊆ W) :
    Nonempty (OriginalIntervalTube e R W Ann Ann
      (Ann ∩ g ⁻¹' (f '' Ann)) (Ann ∩ f ⁻¹' (g '' Ann)) g f) := by
  have hb : ∀ y ∈ Ann, g y ∈ f '' Ann → g y ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (g y) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0 := by
    intro y hy hxy hyfront
    obtain ⟨x, hx, hxy⟩ := hxy
    obtain ⟨B, hBR, hBF⟩ := hboundary x ⟨hx, (hfp x hx).mp (hxy.symm ▸ hyfront)⟩
      ⟨y, hy, hxy.symm⟩
    exact hxy ▸ ⟨B, hBR, hBF⟩
  have hi : ∀ y ∈ Ann, g y ∈ f '' Ann → g y ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (g y) false) := by
    intro y hy hxy hyint
    obtain ⟨x, hx, hxy⟩ := hxy
    have hxfront : x ∉ frontier Ann := fun hh ↦
      ((hfp x hx).mpr hh).2 (hxy.symm ▸ hyint)
    exact hxy ▸ hinterior x ⟨hx, hxfront⟩ ⟨y, hy, hxy.symm⟩
  have himage : g '' (Ann ∩ g ⁻¹' (f '' Ann)) = f '' (Ann ∩ f ⁻¹' (g '' Ann)) := by
    ext z
    constructor
    · rintro ⟨y, ⟨hy, x, hx, hxy⟩, rfl⟩
      exact ⟨x, ⟨hx, y, hy, hxy.symm⟩, hxy⟩
    · rintro ⟨x, ⟨hx, y, hy, hyx⟩, rfl⟩
      exact ⟨y, ⟨hy, x, hx, hyx.symm⟩, hyx⟩
  have hQ : frontier Ann ⊆ Ann := isCompact_planar_annulus.isClosed.frontier_subset
  obtain ⟨J, hJ, hJs⟩ := exists_planar_annulus_complex
  have hresult := nonempty_originalIntervalTube he J J hJ hJ g f
    (hJs.symm ▸ hg) (hJs.symm ▸ hf) (hJs.symm ▸ hgi) (hJs.symm ▸ hfi)
    (hJs.symm ▸ hgR) (hJs.symm ▸ hfR) (frontier Ann) (frontier Ann)
    (hJs.symm ▸ hQ) (hJs.symm ▸ hQ) (hJs.symm ▸ hgp) (hJs.symm ▸ hfp)
    (hJs.symm ▸ hb) (hJs.symm ▸ hi)
    (Ann ∩ g ⁻¹' (f '' Ann)) (Ann ∩ f ⁻¹' (g '' Ann))
    (hJs.symm ▸ inter_subset_left) (hJs.symm ▸ inter_subset_left) hball himage
    (by rw [hJs, sdiff_self]; exact isClosed_empty) hW
    (fun z hz ↦ by
      obtain ⟨y, hy, rfl⟩ := hz
      exact hCW ⟨hy.2, y, hy.1, rfl⟩)
  rw [hJs] at hresult
  exact hresult

end PoincareConjecture.M76.Dehn.Annuli
