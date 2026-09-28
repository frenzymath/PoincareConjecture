import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.LateralCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.RelativeGeometry
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeConvexChartSides
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Mathlib.CompatibleSignedPairHalfspace



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem OriginalIntervalTube.exists_exterior_lateral_halfspace
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {z : C3} (hz : z ∈ lateral r) :
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ U.map z ∈ B.source ∧ ell (B (U.map z)) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ x ∈ B.source, x ∈ R \ U.map '' openTube r ↔ 0 ≤ ell (B x) := by
  obtain ⟨H, hzH, hHt, hHz, hcompat, hpair⟩ :=
    OriginalIntervalTube.exists_lateral_pair_chart U he hr hr1.le hz
  have hcv : Convex ℝ H.target := by
    rw [hHt]
    exact (((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).prod
      (convex_Icc (-1 : ℝ) 1)).interior
  have hpR : U.map z ∈ R := U.mapsTo_region (closedTube_subset hr1.le (lateral_subset r hz))
  have hpfront : (⟨U.map z, hpR⟩ : R) ∈
      frontier ((Subtype.val : R → X) ⁻¹' (R \ U.map '' openTube r)) := by
    rw [OriginalIntervalTube.relative_frontier_exterior U he hr hr1.le]
    exact ⟨z, hz, rfl⟩
  have hclosed : IsClosed ((Subtype.val : R → X) ⁻¹' (R \ U.map '' openTube r)) :=
    (OriginalIntervalTube.isCompact_exterior U hR he hr hr1.le).isClosed.preimage
      continuous_subtype_val
  have hselect (M : Set C3) (himage : H.IsImage R M)
      (hconvex : Convex ℝ (H.target ∩ M))
      (hfront : ∀ x : R, (x : X) ∈ H.source →
        (x ∈ frontier ((Subtype.val : R → X) ⁻¹' (R \ U.map '' openTube r)) ↔
          (H x).2 = 0)) :
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ x ∈ H.source, x ∈ R \ U.map '' openTube r ↔ x ∈ R ∧ 0 ≤ ε * (H x).2 := by
    rcases relative_halfspace_of_convex_frontier_chart sdiff_subset hclosed
        (OriginalIntervalTube.relative_regular_closed_exterior U hR he hr hr1)
        hpfront H hzH himage hconvex hfront with h | h
    · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_mul, neg_nonneg] using h⟩
  rcases hpair with ⟨hinside, hplane⟩ | ⟨hregion, hplane⟩
  · have himage : H.IsImage R univ := fun x hx =>
      ⟨fun _ => interior_subset (hinside hx), fun _ => mem_univ _⟩
    have hconvex : Convex ℝ (H.target ∩ (univ : Set C3)) := by
      simpa only [inter_univ] using hcv
    have hfront : ∀ x : R, (x : X) ∈ H.source →
        (x ∈ frontier ((Subtype.val : R → X) ⁻¹' (R \ U.map '' openTube r)) ↔
          (H x).2 = 0) := by
      intro x hx
      rw [OriginalIntervalTube.relative_frontier_exterior U he hr hr1.le]
      exact hplane x hx
    obtain ⟨ε, hε, hside⟩ := hselect univ himage hconvex hfront
    apply exists_compatible_halfspace_of_signed_pair e H hzH hHz
      (fun i => (hcompat i).1) ε hε
    exact Or.inl (fun x hx => (hside x hx).trans
      (and_iff_right (interior_subset (hinside hx))))
  · let a : C3 →ₗ[ℝ] ℝ :=
      (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ P2 ℝ)
    let M : Set C3 := {y | 0 ≤ y.1.1}
    have himage : H.IsImage R M := fun _ hx => (hregion _ hx).symm
    have hconvex : Convex ℝ (H.target ∩ M) :=
      hcv.inter ((convex_Ici (0 : ℝ)).linear_preimage a)
    have hfront : ∀ x : R, (x : X) ∈ H.source →
        (x ∈ frontier ((Subtype.val : R → X) ⁻¹' (R \ U.map '' openTube r)) ↔
          (H x).2 = 0) := by
      intro x hx
      rw [OriginalIntervalTube.relative_frontier_exterior U he hr hr1.le]
      exact (hplane x hx).trans (and_iff_right ((hregion x hx).mp x.property))
    obtain ⟨ε, hε, hside⟩ := hselect M himage hconvex hfront
    apply exists_compatible_halfspace_of_signed_pair e H hzH hHz
      (fun i => (hcompat i).1) ε hε
    exact Or.inr (fun x hx => (hside x hx).trans ((hregion x hx).and Iff.rfl))

theorem OriginalIntervalTube.plDomain_exterior
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PLDomain e (R \ U.map '' openTube r) := by
  have hK := OriginalIntervalTube.isCompact_exterior U hR he hr hr1.le
  have hclosed : IsClosed (U.map '' closedTube r) :=
    ((isCompact_closedTube r).image_of_continuousOn
      (OriginalIntervalTube.restrict_closedTube U hr hr1.le).1.continuousOn).isClosed
  refine ⟨he.cover, he.compatible, hK.isClosed, ?_⟩
  intro x hx
  by_cases hxC : x ∈ U.map '' closedTube r
  · have hxlat : x ∈ U.map '' lateral r :=
      (OriginalIntervalTube.closedTube_inter_exterior U hr hr1.le).subset
        ⟨hxC, hK.isClosed.frontier_subset hx⟩
    obtain ⟨z, hz, rfl⟩ := hxlat
    exact OriginalIntervalTube.exists_exterior_lateral_halfspace U hR he hr hr1 hz
  · have hxR : x ∈ frontier R := by
      rw [OriginalIntervalTube.frontier_exterior U hR he hr hr1.le] at hx
      rcases hx with hx | hx
      · exact hx.1
      · exact False.elim (hxC (image_mono (lateral_subset r) hx))
    obtain ⟨ell, v, H, hv, hxH, hzero, hcompat, hhalf⟩ := he.halfspace x hxR
    let B := H.restrOpen (U.map '' closedTube r)ᶜ hclosed.isOpen_compl
    refine ⟨ell, v, B, hv, ⟨hxH, hxC⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right H (hcompat i) hclosed.isOpen_compl
    · intro y hy
      change y ∈ R \ U.map '' openTube r ↔ 0 ≤ ell (H y)
      exact ⟨fun h => (hhalf y hy.1).mp h.1, fun h =>
        ⟨(hhalf y hy.1).mpr h, fun hyU => hy.2 (image_mono (openTube_subset r) hyU)⟩⟩

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
