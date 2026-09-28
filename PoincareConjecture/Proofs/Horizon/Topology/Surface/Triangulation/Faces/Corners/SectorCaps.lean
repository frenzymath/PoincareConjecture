import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.CornerCaps
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.Right
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Coordinates

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology Matrix
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface
namespace ChartCircleArrangementVertexPatch

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  {r : M → ℝ} {p : M}

private theorem sectorCoordinates_mem_sector
    (P : ChartCircleArrangementVertexPatch r p) (i : Bool × Bool) {q : ℝ × ℝ}
    (hq : q ∈ Ioo (0 : ℝ) P.width ×ˢ Ioo (0 : ℝ) P.width) :
    P.sectorCoordinates i q ∈ P.sector i := by
  refine ⟨sectorParameterEquiv P.center i q, ?_, rfl⟩
  rw [sectorParameterEquiv_apply]
  rcases i with ⟨i, j⟩
  cases i <;> cases j <;> constructor <;>
    dsimp [sectorBox, sectorInterval] <;> constructor <;>
    linarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]

variable [IsManifold (𝓡 2) ∞ M]

private theorem exists_sector_cap_coordinates
    (P : ChartCircleArrangementVertexPatch r p) (i : Bool × Bool) (x : M)
    (hchart : P.closedSector i ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) :
    ∃ δ > 0, δ ≤ P.width ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source ∧
        F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).target ∧
        ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
        (∀ s ∈ Icc (0 : ℝ) ε, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
          (F (s, 0)) = P.sectorCoordinates i (s, 0)) ∧
        (∀ t ∈ Icc (0 : ℝ) ε, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
          (F (0, t)) = P.sectorCoordinates i (0, t)) ∧
        (∀ t : ℝ, F (t * ε, (1 - t) * ε) =
          (1 - t) • chartAt (EuclideanSpace ℝ (Fin 2)) x (P.sectorCoordinates i (0, ε)) +
          t • chartAt (EuclideanSpace ℝ (Fin 2)) x (P.sectorCoordinates i (ε, 0))) ∧
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε}) ⊆ P.closedSector i ∧
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε}) ⊆
          P.sector i ∪ P.sectorCoordinates i ''
            ((Icc (0 : ℝ) ε ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) ε)) ∧
        ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ∩ P.closedSector i ⊆
          (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
            (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε}) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let A := P.sectorCoordinates i
  let S := Ioo (-P.width) P.width ×ˢ Ioo (-P.width) P.width
  have hS : IsOpen S := isOpen_Ioo.prod isOpen_Ioo
  let H := (P.chartSectorCoordinates x i).restrOpen S hS
  have hH0 : (0 : ℝ × ℝ) ∈ H.source := by
    refine ⟨P.chartSectorCoordinates_square_source x i hchart ?_, ?_⟩
    · exact ⟨⟨le_rfl, P.width_pos.le⟩, ⟨le_rfl, P.width_pos.le⟩⟩
    · exact ⟨⟨neg_lt_zero.mpr P.width_pos, P.width_pos⟩,
        ⟨neg_lt_zero.mpr P.width_pos, P.width_pos⟩⟩
  have hH : ContDiffOn ℝ ∞ H H.source :=
    (P.chartSectorCoordinates_smooth x i).mono (fun _ hz => hz.1)
  have hHI : ContDiffOn ℝ ∞ H.symm H.target :=
    (P.chartSectorCoordinates_smooth_symm x i).mono (fun _ hz => hz.1)
  have hHtarget : H.target ⊆ c.target := fun _ hz => hz.1.1
  have hHmap (q : ℝ × ℝ) : H q = c (A q) := rfl
  have hHp : H 0 = c p := P.chartSectorCoordinates_zero x i
  obtain ⟨ρ, hρ, hcaps⟩ := exists_smooth_coordinate_corner_caps H hH0 hH hHI
  let δ := min ρ P.width
  have hδ : 0 < δ := lt_min hρ P.width_pos
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro ε hε hεδ
  have hερ : ε < ρ := hεδ.trans_le (min_le_left _ _)
  have hεwidth : ε < P.width := hεδ.trans_le (min_le_right _ _)
  have hsmall {s : ℝ} (hs : s ∈ Icc (0 : ℝ) ε) : |s| < ρ := by
    rw [abs_of_nonneg hs.1]
    exact hs.2.trans_lt hερ
  have hsquare {s : ℝ} (hs : s ∈ Icc (0 : ℝ) ε) : s ∈ Icc (0 : ℝ) P.width :=
    ⟨hs.1, hs.2.trans hεwidth.le⟩
  obtain ⟨F, hsource, htarget, hF, hFI, hfirst, hsecond, hchord, hsign, hsector, V,
    hVopen, hVp, hVtarget, hVcover⟩ := hcaps ε hε hερ
  have hfirst' {s : ℝ} (hs : s ∈ Icc (0 : ℝ) ε) : c.symm (F (s, 0)) = A (s, 0) := by
    rw [hfirst s (hsmall hs), hHmap]
    exact c.left_inv (hchart (by
      rw [← P.sectorCoordinates_image_square i]
      exact mem_image_of_mem A ⟨hsquare hs, ⟨le_rfl, P.width_pos.le⟩⟩))
  have hsecond' {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ε) : c.symm (F (0, t)) = A (0, t) := by
    rw [hsecond t (hsmall ht), hHmap]
    exact c.left_inv (hchart (by
      rw [← P.sectorCoordinates_image_square i]
      exact mem_image_of_mem A ⟨⟨le_rfl, P.width_pos.le⟩, hsquare ht⟩))
  refine ⟨F, hsource, htarget.trans hHtarget, hF, hFI,
    fun _ hs => hfirst' hs, fun _ ht => hsecond' ht, hchord, ?_, ?_, ?_⟩
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨q, ⟨hqH, hqpos⟩, rfl⟩ := hsector hw
    have hcq : A q ∈ c.source := by simpa [A] using hqH.1.2
    change c.symm (H q) ∈ P.closedSector i
    rw [hHmap, c.left_inv hcq, ← P.sectorCoordinates_image_square i]
    exact mem_image_of_mem A
      ⟨⟨hqpos.1, hqH.2.1.2.le⟩, ⟨hqpos.2, hqH.2.2.2.le⟩⟩
  · rintro z ⟨w, ⟨q, hq, rfl⟩, rfl⟩
    have hq₁ : q.1 ∈ Icc (0 : ℝ) ε := ⟨hq.1, by linarith [hq.2.1, hq.2.2]⟩
    have hq₂ : q.2 ∈ Icc (0 : ℝ) ε := ⟨hq.2.1, by linarith [hq.1, hq.2.2]⟩
    by_cases hq1 : q.1 = 0
    · apply Or.inr
      refine ⟨(0, q.2), Or.inr ⟨rfl, hq₂⟩, ?_⟩
      have he : q = (0, q.2) := Prod.ext hq1 rfl
      rw [he]
      exact (hsecond' hq₂).symm
    by_cases hq2 : q.2 = 0
    · apply Or.inr
      refine ⟨(q.1, 0), Or.inl ⟨hq₁, rfl⟩, ?_⟩
      have he : q = (q.1, 0) := Prod.ext rfl hq2
      rw [he]
      exact (hfirst' hq₁).symm
    have hwH : F q ∈ H.target := htarget (F.map_source (hsource hq))
    have hvH := H.map_target hwH
    have hv₁ : 0 < (H.symm (F q)).1 :=
      (hsign q.1 q.2 (hsmall hq₁) (hsmall hq₂)).1.1.mpr (lt_of_le_of_ne hq.1 (Ne.symm hq1))
    have hv₂ : 0 < (H.symm (F q)).2 :=
      (hsign q.1 q.2 (hsmall hq₁) (hsmall hq₂)).2.1.mpr (lt_of_le_of_ne hq.2.1 (Ne.symm hq2))
    have hvchart : A (H.symm (F q)) ∈ c.source := by simpa [A] using hvH.1.2
    have he : A (H.symm (F q)) = c.symm (F q) := by
      calc
        _ = c.symm (c (A (H.symm (F q)))) := (c.left_inv hvchart).symm
        _ = c.symm (H (H.symm (F q))) := rfl
        _ = c.symm (F q) := congrArg c.symm (H.right_inv hwH)
    apply Or.inl
    rw [← he]
    exact sectorCoordinates_mem_sector P i
      ⟨⟨hv₁, hvH.2.1.2⟩, ⟨hv₂, hvH.2.2.2⟩⟩
  · refine ⟨c.symm '' V, c.symm.isOpen_image_of_subset_source hVopen
      (hVtarget.trans hHtarget), ?_, ?_⟩
    · exact ⟨H 0, hVp, by rw [hHp, c.left_inv (hchart (P.mem_closedSector i))]⟩
    · rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      have hwH : w ∈ H.target := hVtarget hw
      have hquad : w ∈ H '' (H.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
        rw [← P.sectorCoordinates_image_square i] at hz
        obtain ⟨q, hq, heq⟩ := hz
        have hinv : H.symm w = q := by
          change A.symm (c.symm w) = q
          rw [← heq, A.left_inv (P.sectorCoordinates_square_source i hq)]
        refine ⟨H.symm w, ⟨H.map_target hwH, ?_⟩, H.right_inv hwH⟩
        rw [hinv]
        exact ⟨hq.1.1, hq.2.1⟩
      exact ⟨w, hVcover ⟨hw, hquad⟩, rfl⟩

variable [T2Space M]

theorem exists_smoothFace_sector_caps
    (P : ChartCircleArrangementVertexPatch r p) (i : Bool × Bool) (x : M)
    (hchart : P.closedSector i ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) :
    ∃ δ > 0, δ ≤ P.width ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε < δ →
      ∃ (F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)))
        (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M) (face : SmoothFace M),
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source ∧
        F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).target ∧
        ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
        (∀ s ∈ Icc (0 : ℝ) ε, F (s, 0) =
          chartAt (EuclideanSpace ℝ (Fin 2)) x (P.sectorCoordinates i (s, 0))) ∧
        (∀ t ∈ Icc (0 : ℝ) ε, F (0, t) =
          chartAt (EuclideanSpace ℝ (Fin 2)) x (P.sectorCoordinates i (0, t))) ∧
        (∀ t : ℝ, F ((1 - t) * ε, t * ε) =
          (1 - t) • F (ε, 0) + t • F (0, ε)) ∧
        (∀ z, C z = (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
          (F (collarParameterEquiv z))) ∧
        convexHull ℝ (range (rightTriangleBasis hε)) ⊆ C.source ∧
        C.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
        face.map = C ∧ face.source = convexHull ℝ (range (rightTriangleBasis hε)) ∧
        face.carrier = C '' convexHull ℝ (range (rightTriangleBasis hε)) ∧
        face.carrier = (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε}) ∧
        InjOn face.map face.source ∧
        (∀ k : Fin 3, (face.boundary k).map = C ∘
          affineChartSegment (rightTriangleBasis hε (k.succAbove 0))
            (rightTriangleBasis hε (k.succAbove 1))) ∧
        (∀ k, InjOn (face.boundary k).map (Icc (0 : ℝ) 1)) ∧
        (∀ t : ℝ, (face.boundary 0).map t =
          (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
            ((1 - t) • chartAt (EuclideanSpace ℝ (Fin 2)) x (P.sectorCoordinates i (ε, 0)) +
              t • chartAt (EuclideanSpace ℝ (Fin 2)) x (P.sectorCoordinates i (0, ε)))) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 1).map t = P.sectorCoordinates i (0, t * ε)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 2).map t = P.sectorCoordinates i (t * ε, 0)) ∧
        (face.boundary 0).map '' Icc (0 : ℝ) 1 =
          (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' affineSegment ℝ
            (chartAt (EuclideanSpace ℝ (Fin 2)) x (P.sectorCoordinates i (ε, 0)))
            (chartAt (EuclideanSpace ℝ (Fin 2)) x (P.sectorCoordinates i (0, ε))) ∧
        (face.boundary 1).map '' Icc (0 : ℝ) 1 =
          P.sectorCoordinates i '' ({0} ×ˢ Icc (0 : ℝ) ε) ∧
        (face.boundary 2).map '' Icc (0 : ℝ) 1 =
          P.sectorCoordinates i '' (Icc (0 : ℝ) ε ×ˢ {0}) ∧
        face.carrier ⊆ P.closedSector i ∧
        face.carrier ⊆ P.sector i ∪ P.sectorCoordinates i ''
          ((Icc (0 : ℝ) ε ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) ε)) ∧
        ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ∩ P.closedSector i ⊆ face.carrier := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let A := P.sectorCoordinates i
  obtain ⟨δ, hδ, hδwidth, hcaps⟩ := exists_sector_cap_coordinates P i x hchart
  refine ⟨δ, hδ, hδwidth, ?_⟩
  intro ε hε hεδ
  obtain ⟨F, hFsource, hFtarget, hF, hFI, hfirst, hsecond, hchord, hsector, haxes,
    V, hVopen, hVp, hVcover⟩ := hcaps ε hε hεδ
  have hplanar_first (s : ℝ) (hs : s ∈ Icc (0 : ℝ) ε) :
      F (s, 0) = c (A (s, 0)) := by
    have hsF : (s, (0 : ℝ)) ∈ F.source := hFsource ⟨hs.1, le_rfl, by simpa using hs.2⟩
    exact (c.right_inv (hFtarget (F.map_source hsF))).symm.trans (congrArg c (hfirst s hs))
  have hplanar_second (t : ℝ) (ht : t ∈ Icc (0 : ℝ) ε) :
      F (0, t) = c (A (0, t)) := by
    have htF : ((0 : ℝ), t) ∈ F.source := hFsource ⟨le_rfl, ht.1, by simpa using ht.2⟩
    exact (c.right_inv (hFtarget (F.map_source htF))).symm.trans (congrArg c (hsecond t ht))
  have hplanar_chord (t : ℝ) : F ((1 - t) * ε, t * ε) =
      (1 - t) • F (ε, 0) + t • F (0, ε) := by
    rw [hplanar_first ε (right_mem_Icc.mpr hε.le), hplanar_second ε (right_mem_Icc.mpr hε.le)]
    have h := hchord (1 - t)
    rw [show 1 - (1 - t) = t by ring, add_comm] at h
    exact h
  let L := collarParameterEquiv
  let G := L.toHomeomorph.toOpenPartialHomeomorph.trans F
  let C := G.trans c.symm
  have hG : ContDiffOn ℝ ∞ G G.source :=
    hF.comp L.contDiff.contDiffOn (fun _ hz => hz.2)
  have hGI : ContDiffOn ℝ ∞ G.symm G.target :=
    L.symm.contDiff.comp_contDiffOn (hFI.mono (fun _ hz => hz.1))
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := x)).comp
      (hG.contMDiffOn.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hCI : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    hGI.contMDiffOn.comp
      ((contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := x)).mono (fun _ hz => hz.1))
      (fun _ hz => hz.2)
  have hCtarget : C.target ⊆ c.source := fun _ hz => hz.1
  have hsub : convexHull ℝ (range (rightTriangleBasis hε)) ⊆ C.source := by
    intro z hz
    have hzF : L z ∈ F.source := hFsource ((mem_rightTriangleBasis_convexHull hε z).mp hz)
    exact ⟨⟨mem_univ _, hzF⟩, hFtarget (F.map_source hzF)⟩
  have hCchart : C '' convexHull ℝ (range (rightTriangleBasis hε)) ⊆ c.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact hCtarget (C.map_source (hsub hz))
  obtain ⟨face, hmap, hsource, hcarrier, hinj, hboundary⟩ :=
    exists_smoothFace_of_smooth_coordinates C hC hCI (rightTriangleBasis hε) hsub x hCchart
  have hproduct : L '' convexHull ℝ (range (rightTriangleBasis hε)) =
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (mem_rightTriangleBasis_convexHull hε z).mp hz
    · intro hq
      refine ⟨L.symm q, (mem_rightTriangleBasis_convexHull hε _).mpr ?_, L.apply_symm_apply q⟩
      exact hq
  have hcarrier' : face.carrier = c.symm ''
      (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε}) := by
    rw [hcarrier, ← hproduct, image_image, image_image]
    rfl
  have hscale (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t * ε ∈ Icc (0 : ℝ) ε :=
    ⟨mul_nonneg ht.1 hε.le, by simpa using mul_le_mul_of_nonneg_right ht.2 hε.le⟩
  have hboundary0 (t : ℝ) : (face.boundary 0).map t =
      c.symm ((1 - t) • c (A (ε, 0)) + t • c (A (0, ε))) := by
    rw [hboundary]
    change c.symm (F (L (affineChartSegment !₂[ε, 0] !₂[0, ε] t))) = _
    have harg : L (affineChartSegment !₂[ε, 0] !₂[0, ε] t) = ((1 - t) * ε, t * ε) := by
      ext <;> simp [L, collarParameterEquiv_apply, affineChartSegment]
      ring
    rw [harg]
    have h := hchord (1 - t)
    rw [show 1 - (1 - t) = t by ring, add_comm] at h
    exact congrArg c.symm h
  have hboundary1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (face.boundary 1).map t = A (0, t * ε) := by
    rw [hboundary]
    change c.symm (F (L (affineChartSegment !₂[0, 0] !₂[0, ε] t))) = _
    have harg : L (affineChartSegment !₂[0, 0] !₂[0, ε] t) = (0, t * ε) := by
      ext <;> simp [L, collarParameterEquiv_apply, affineChartSegment]
    rw [harg]
    exact hsecond _ (hscale t ht)
  have hboundary2 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (face.boundary 2).map t = A (t * ε, 0) := by
    rw [hboundary]
    change c.symm (F (L (affineChartSegment !₂[0, 0] !₂[ε, 0] t))) = _
    have harg : L (affineChartSegment !₂[0, 0] !₂[ε, 0] t) = (t * ε, 0) := by
      ext <;> simp [L, collarParameterEquiv_apply, affineChartSegment]
    rw [harg]
    exact hfirst _ (hscale t ht)
  have hscale_image : (fun t : ℝ => t * ε) '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) ε := by
    simpa using image_mul_right_Icc' (0 : ℝ) 1 hε
  refine ⟨F, C, face, hFsource, hFtarget, hF, hFI, hplanar_first, hplanar_second,
    hplanar_chord, fun _ => rfl, hsub, hCtarget, hC, hCI,
    hmap, hsource, hcarrier, hcarrier', hinj, hboundary, ?_, hboundary0, hboundary1, hboundary2,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k u hu v hv huv
    let a := rightTriangleBasis hε (k.succAbove 0)
    let b := rightTriangleBasis hε (k.succAbove 1)
    have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : affineChartSegment a b t ∈ C.source := by
      apply hsub
      apply segment_subset_convexHull (mem_range_self (k.succAbove 0))
        (mem_range_self (k.succAbove 1))
      convert lineMap_mem_segment ℝ a b ht using 1
      simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
    have hab : b - a ≠ 0 := by
      intro h
      have he := (rightTriangleBasis hε).ind.injective (sub_eq_zero.mp h)
      have h10 : (1 : Fin 2) = 0 := Fin.succAbove_right_injective he
      norm_num at h10
    rw [hboundary] at huv
    have heq := C.injOn (hseg u hu) (hseg v hv) huv
    exact smul_left_injective ℝ hab (add_left_cancel heq)
  · rw [affineSegment, image_image]
    apply image_congr
    intro t _
    rw [hboundary0]
    exact congrArg c.symm (AffineMap.lineMap_apply_module (c (A (ε, 0))) (c (A (0, ε))) t).symm
  · rw [singleton_prod, ← hscale_image, image_image, image_image]
    exact image_congr hboundary1
  · rw [prod_singleton, ← hscale_image, image_image, image_image]
    exact image_congr hboundary2
  · rw [hcarrier']
    exact hsector
  · rw [hcarrier']
    exact haxes
  · exact ⟨V, hVopen, hVp, hcarrier'.symm ▸ hVcover⟩

end ChartCircleArrangementVertexPatch
end PoincareConjecture.Topology.Surface
