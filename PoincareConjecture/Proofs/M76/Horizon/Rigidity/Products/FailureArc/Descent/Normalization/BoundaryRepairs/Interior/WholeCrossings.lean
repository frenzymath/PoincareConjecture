import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Interior.CarrierCrossings

set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ A} {j : A → t.Carrier} {R Fmark : Set M}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}
  {a b : PLAnnularStrip.squareAnnulus 8 1} {W : Set s.Carrier} {ε : ℝ}
  (N : PlanarAnnulusBoundaryMotion step D.endpoint R Fmark a b W ε)
  (hAnn : D.K.space = PLAnnularStrip.squareAnnulus 8 1)

include hAnn

theorem exists_positive_whole_crossing
    (hW : W ∩ ((fun z : A × A => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    (B : SimplicialComplex ℝ V3)
    (hfaces : B.faces = (fun face ↦ face.image (N.motion.map 1)) '' N.branchComplex.faces)
    {z : V3} (hz : z ∈ B.space)
    (hzJ : z ∈ interior N.support.space) (hzpos : 0 < (N.coordinates z).1.1)
    (hz0 : (N.coordinates z).2 = 0)
    (V : Set s.Carrier) (hV : IsOpen V) (hzV : N.chart.symm z ∈ V) :
    ∃ T : OpenPartialHomeomorph s.Carrier V3,
      N.chart.symm z ∈ T.source ∧ T (N.chart.symm z) = 0 ∧
      T.source ⊆ V ∩ (N.chart.source ∩ interior (s.projection ⁻¹' R)) ∧
      (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (step.projection ∘ step.inclusion) ⁻¹' T.source =
        (N.window.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
          (N.window.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
      (∀ y ∈ T.source, y ∈ (step.projection ∘ step.inclusion) ''
        ((N.ambient 1 ∘ D.endpoint) '' PLAnnularStrip.squareAnnulus 8 1 ∩ N.window.left.source) ↔
          (N.coordinates (T y)).1.1 = 0) ∧
      ∀ y ∈ T.source, y ∈ (step.projection ∘ step.inclusion) ''
        ((N.ambient 1 ∘ D.endpoint) '' PLAnnularStrip.squareAnnulus 8 1 ∩ N.window.right.source) ↔
          (N.coordinates (T y)).2 = 0 := by
  let O := (interior N.support.space ∩ (N.chart.target ∩ N.chart.symm ⁻¹' V)) ∩
    {x | 0 < (N.coordinates x).1.1}
  have hO : IsOpen O := (isOpen_interior.inter
    (N.chart.symm.isOpen_inter_preimage hV)).inter
      (isOpen_lt continuous_const N.coordinates.continuous.fst.fst)
  have hzO : z ∈ O := ⟨⟨hzJ, N.support_target (interior_subset hzJ), hzV⟩, hzpos⟩
  obtain ⟨H, hzH, hHO, hH0, hHPL, hflat, hbranch⟩ :=
    N.exists_positive_carrier_crossing hAnn hW B hfaces z hz hzJ hzpos hz0 O hO hzO
  have hH : N.branchComplex.AffineOnFaces (N.motion.map 1) :=
    fun face hf ↦ N.endpoint_affine face (N.branch_le hf)
  have hBimage : B = hH.embeddedImage (N.motion.map 1).injective.injOn := by
    ext1
    exact hfaces.trans (hH.embeddedImage_faces _).symm
  have hBs : B.space = N.motion.map 1 '' N.source.space := by
    rw [hBimage, hH.embeddedImage_space, N.branch_space]
  have hleftimage : (N.ambient 1 ∘ D.endpoint) '' PLAnnularStrip.squareAnnulus 8 1 ∩
      N.window.left.source =
      D.endpoint '' PLAnnularStrip.squareAnnulus 8 1 ∩ N.window.left.source := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hx⟩
      have he : N.ambient 1 (D.endpoint y) = x := hyx
      have hold : D.endpoint y = x :=
        (N.ambient 1).injective (he.trans (N.left_fixed 1 hx).symm)
      exact ⟨⟨y, hy, hold⟩, hx⟩
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨⟨y, hy, N.left_fixed 1 hx⟩, hx⟩
  apply exists_two_branch_chart_of_local_carrier_chart s.charts
    (step.projection ∘ step.inclusion) N.window
    ((N.ambient 1 ∘ D.endpoint) '' PLAnnularStrip.squareAnnulus 8 1) N.chart N.coordinates
    N.support.space B.space (interior (s.projection ⁻¹' R)) V
    (fun y hy ↦ (N.chart_inside hy).2) N.lower_PL N.support_target
    ((N.source_image 1).trans hBs.symm) hzJ H hzH hH0
    (fun _ hx ↦ (hHO hx).1) hHPL ?_ ?_ hbranch
  · intro y hy hyH
    have hpos := (hHO hyH).2
    have hyR := (N.lower_region y hy).mpr hpos.le
    have hn : y ∉ _root_.frontier (s.projection ⁻¹' R) :=
      fun h ↦ hpos.ne' ((N.lower_frontier y hy).mp h)
    by_contra hi
    exact hn ⟨subset_closure hyR, hi⟩
  · intro y hy hyH
    rw [hleftimage, N.left_halfplane y hy]
    exact (and_iff_right (hHO hyH).2.le).trans (hflat (N.chart y) hyH)

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
