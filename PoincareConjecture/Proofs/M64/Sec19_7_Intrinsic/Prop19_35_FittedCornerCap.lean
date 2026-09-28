import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopCornerChart
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.CornerCaps
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Coordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Triangles Poincare.Topology.Plane.Curves
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_fitted_corner_cap_coordinates
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    {K : Set AnnulusCoordinates}
    (hside : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ K ↔ 0 ≤ z.1 ∧ 0 ≤ z.2) :
    ∃ r : ℝ, 0 < r ∧
      ∃ (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
        (W : Set AnnulusCoordinates),
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source ∧
        ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
        (∀ s ∈ Icc (0 : ℝ) r, F (s, 0) = H (s, 0)) ∧
        (∀ s ∈ Icc (0 : ℝ) r, F (0, s) = H (0, s)) ∧
        (∀ t : ℝ, F ((1 - t) * r, t * r) =
          (1 - t) • H (r, 0) + t • H (0, r)) ∧
        F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ K ∧
        IsOpen W ∧ H 0 ∈ W ∧ W ∩ K ⊆
          F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hside
  let J := H.restrOpen (ball (0 : ℝ × ℝ) R) isOpen_ball
  have hJ0 : (0 : ℝ × ℝ) ∈ J.source := ⟨h0, mem_ball_self hR⟩
  have hJ : ContDiffOn ℝ ∞ J J.source := hH.mono (fun _ hz => hz.1)
  have hJi : ContDiffOn ℝ ∞ J.symm J.target := hHi.mono (fun _ hz => hz.1)
  have hquad : J '' (J.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ⊆ K := by
    rintro z ⟨q, hq, rfl⟩
    exact (hball hq.1.2).mpr hq.2
  have htarget : J.target ∩ K ⊆
      J '' (J.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
    intro z hz
    have hi := J.map_target hz.1
    refine ⟨J.symm z, ⟨hi, ?_⟩, J.right_inv hz.1⟩
    apply (hball hi.2).mp
    change J (J.symm z) ∈ K
    simpa only [J.right_inv hz.1] using hz.2
  obtain ⟨rho, hrho, hcaps⟩ := exists_smooth_coordinate_corner_caps J hJ0 hJ hJi
  let r := rho / 2
  have hr : 0 < r := half_pos hrho
  have hrrho : r < rho := half_lt_self hrho
  obtain ⟨F, hsource, _, hF, hFi, hfirst, hsecond, hchord, _, hsub,
      W, hW, hpW, hWt, hcover⟩ := hcaps r hr hrrho
  refine ⟨r, hr, F, W, hsource, hF, hFi, ?_, ?_, ?_, hsub.trans hquad, hW, hpW, ?_⟩
  · intro s hs
    exact hfirst s (by rw [abs_of_nonneg hs.1]; exact hs.2.trans_lt hrrho)
  · intro s hs
    exact hsecond s (by rw [abs_of_nonneg hs.1]; exact hs.2.trans_lt hrrho)
  · intro t
    have h := hchord (1 - t)
    rw [show 1 - (1 - t) = t by ring, add_comm] at h
    exact h
  · intro z hz
    exact hcover ⟨hz.1, htarget ⟨hWt hz.1, hz.2⟩⟩

theorem m64Intrinsic_exists_fitted_corner_face
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    {K : Set AnnulusCoordinates}
    (hside : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ K ↔ 0 ≤ z.1 ∧ 0 ≤ z.2) :
    ∃ (r : ℝ) (face : SmoothFace AnnulusCoordinates) (W : Set AnnulusCoordinates),
      0 < r ∧ face.carrier ⊆ K ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 1).map t = H (0, t * r)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 2).map t = H (t * r, 0)) ∧
      (∀ t : ℝ, (face.boundary 0).map t =
        (1 - t) • H (r, 0) + t • H (0, r)) ∧
      H (r, 0) ≠ H (0, r) ∧
      IsOpen W ∧ H 0 ∈ W ∧ W ∩ K ⊆ face.carrier := by
  obtain ⟨r, hr, F, W, hsource, hF, hFi, hfirst, hsecond, hchord,
      hsub, hW, hpW, hcover⟩ :=
    m64Intrinsic_exists_fitted_corner_cap_coordinates H h0 hH hHi hside
  let C := collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans F
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    contMDiffOn_iff_contDiffOn.mpr
      (hF.comp collarParameterEquiv.contDiff.contDiffOn (fun _ hz => hz.2))
  have hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    contMDiffOn_iff_contDiffOn.mpr
      (collarParameterEquiv.symm.contDiff.comp_contDiffOn (hFi.mono (fun _ hz => hz.1)))
  have htriangle : convexHull ℝ (range (rightTriangleBasis hr)) ⊆ C.source := by
    intro z hz
    exact ⟨mem_univ _, hsource ((mem_rightTriangleBasis_convexHull hr z).mp hz)⟩
  obtain ⟨face, _, _, hcarrier, _, hboundary⟩ :=
    exists_smoothFace_of_smooth_coordinates C hC hCi (rightTriangleBasis hr) htriangle
      (0 : AnnulusCoordinates) (by intro z _; simp)
  have hface : face.carrier =
      F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
    rw [hcarrier]
    ext z
    constructor
    · rintro ⟨q, hq, heq⟩
      exact ⟨collarParameterEquiv q, (mem_rightTriangleBasis_convexHull hr q).mp hq, heq⟩
    · rintro ⟨q, hq, heq⟩
      refine ⟨collarParameterEquiv.symm q,
        (mem_rightTriangleBasis_convexHull hr _).mpr hq, ?_⟩
      change F (collarParameterEquiv (collarParameterEquiv.symm q)) = z
      rwa [collarParameterEquiv.apply_symm_apply]
  have hfirst' (t : ℝ) : (face.boundary 2).map t = F (t * r, 0) := by
    rw [hboundary]
    rw [show Fin.succAbove (2 : Fin 3) 1 = 1 by decide]
    simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
      collarParameterEquiv, mul_comm]
  have hsecond' (t : ℝ) : (face.boundary 1).map t = F (0, t * r) := by
    rw [hboundary]
    simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
      collarParameterEquiv, mul_comm]
  have hchord' (t : ℝ) : (face.boundary 0).map t = F ((1 - t) * r, t * r) := by
    rw [hboundary]
    simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
      collarParameterEquiv, mul_comm]
    congr 1
    ring
  have ht (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ Icc (0 : ℝ) r :=
    ⟨mul_nonneg ht.1 hr.le, (mul_le_mul_of_nonneg_right ht.2 hr.le).trans_eq (one_mul r)⟩
  refine ⟨r, face, W, hr, hface ▸ hsub, ?_, ?_, ?_, ?_, hW, hpW, hface ▸ hcover⟩
  · intro t ht'
    rw [hsecond', hsecond _ (ht t ht')]
  · intro t ht'
    rw [hfirst', hfirst _ (ht t ht')]
  · intro t
    rw [hchord', hchord]
  · intro heq
    have hfirst0 := hfirst r (right_mem_Icc.mpr hr.le)
    have hsecond0 := hsecond r (right_mem_Icc.mpr hr.le)
    have heq' := F.injOn (hsource ⟨hr.le, le_rfl, by simp⟩)
      (hsource ⟨le_rfl, hr.le, by simp⟩) (hfirst0.trans (heq.trans hsecond0.symm))
    exact hr.ne' (congrArg Prod.fst heq')

theorem m64Intrinsic_exists_fitted_corner_cap_coordinates_le
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    {K : Set AnnulusCoordinates}
    (hside : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ K ↔ 0 ≤ z.1 ∧ 0 ≤ z.2)
    {T : ℝ} (hT : 0 < T) :
    ∃ r : ℝ, 0 < r ∧ r ≤ T ∧
      ∃ (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
        (W : Set AnnulusCoordinates),
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source ∧
        ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
        (∀ s ∈ Icc (0 : ℝ) r, F (s, 0) = H (s, 0)) ∧
        (∀ s ∈ Icc (0 : ℝ) r, F (0, s) = H (0, s)) ∧
        (∀ t : ℝ, F ((1 - t) * r, t * r) =
          (1 - t) • H (r, 0) + t • H (0, r)) ∧
        F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ K ∧
        IsOpen W ∧ H 0 ∈ W ∧ W ∩ K ⊆
          F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hside
  let J := H.restrOpen (ball (0 : ℝ × ℝ) R) isOpen_ball
  have hJ0 : (0 : ℝ × ℝ) ∈ J.source := ⟨h0, mem_ball_self hR⟩
  have hJ : ContDiffOn ℝ ∞ J J.source := hH.mono (fun _ hz => hz.1)
  have hJi : ContDiffOn ℝ ∞ J.symm J.target := hHi.mono (fun _ hz => hz.1)
  have hquad : J '' (J.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ⊆ K := by
    rintro z ⟨q, hq, rfl⟩
    exact (hball hq.1.2).mpr hq.2
  have htarget : J.target ∩ K ⊆
      J '' (J.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
    intro z hz
    have hi := J.map_target hz.1
    refine ⟨J.symm z, ⟨hi, ?_⟩, J.right_inv hz.1⟩
    apply (hball hi.2).mp
    change J (J.symm z) ∈ K
    simpa only [J.right_inv hz.1] using hz.2
  obtain ⟨rho, hrho, hcaps⟩ := exists_smooth_coordinate_corner_caps J hJ0 hJ hJi
  let r := min (rho / 2) (T / 2)
  have hr : 0 < r := lt_min (half_pos hrho) (half_pos hT)
  have hrrho : r < rho := (min_le_left _ _).trans_lt (half_lt_self hrho)
  have hrT : r ≤ T := (min_le_right _ _).trans (half_le_self hT.le)
  obtain ⟨F, hsource, _, hF, hFi, hfirst, hsecond, hchord, _, hsub,
      W, hW, hpW, hWt, hcover⟩ := hcaps r hr hrrho
  refine ⟨r, hr, hrT, F, W, hsource, hF, hFi, ?_, ?_, ?_, hsub.trans hquad,
    hW, hpW, ?_⟩
  · intro s hs
    exact hfirst s (by rw [abs_of_nonneg hs.1]; exact hs.2.trans_lt hrrho)
  · intro s hs
    exact hsecond s (by rw [abs_of_nonneg hs.1]; exact hs.2.trans_lt hrrho)
  · intro t
    have h := hchord (1 - t)
    rw [show 1 - (1 - t) = t by ring, add_comm] at h
    exact h
  · intro z hz
    exact hcover ⟨hz.1, htarget ⟨hWt hz.1, hz.2⟩⟩

theorem m64Intrinsic_exists_fitted_corner_face_le
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target)
    {K : Set AnnulusCoordinates}
    (hside : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ K ↔ 0 ≤ z.1 ∧ 0 ≤ z.2)
    {T : ℝ} (hT : 0 < T) :
    ∃ (r : ℝ) (face : SmoothFace AnnulusCoordinates) (W : Set AnnulusCoordinates),
      0 < r ∧ r ≤ T ∧ face.carrier ⊆ K ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 1).map t = H (0, t * r)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (face.boundary 2).map t = H (t * r, 0)) ∧
      (∀ t : ℝ, (face.boundary 0).map t =
        (1 - t) • H (r, 0) + t • H (0, r)) ∧
      H (r, 0) ≠ H (0, r) ∧
      IsOpen W ∧ H 0 ∈ W ∧ W ∩ K ⊆ face.carrier := by
  obtain ⟨r, hr, hrT, F, W, hsource, hF, hFi, hfirst, hsecond, hchord,
      hsub, hW, hpW, hcover⟩ :=
    m64Intrinsic_exists_fitted_corner_cap_coordinates_le H h0 hH hHi hside hT
  let C := collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans F
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    contMDiffOn_iff_contDiffOn.mpr
      (hF.comp collarParameterEquiv.contDiff.contDiffOn (fun _ hz => hz.2))
  have hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    contMDiffOn_iff_contDiffOn.mpr
      (collarParameterEquiv.symm.contDiff.comp_contDiffOn (hFi.mono (fun _ hz => hz.1)))
  have htriangle : convexHull ℝ (range (rightTriangleBasis hr)) ⊆ C.source := by
    intro z hz
    exact ⟨mem_univ _, hsource ((mem_rightTriangleBasis_convexHull hr z).mp hz)⟩
  obtain ⟨face, _, _, hcarrier, _, hboundary⟩ :=
    exists_smoothFace_of_smooth_coordinates C hC hCi (rightTriangleBasis hr) htriangle
      (0 : AnnulusCoordinates) (by intro z _; simp)
  have hface : face.carrier =
      F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
    rw [hcarrier]
    ext z
    constructor
    · rintro ⟨q, hq, heq⟩
      exact ⟨collarParameterEquiv q, (mem_rightTriangleBasis_convexHull hr q).mp hq, heq⟩
    · rintro ⟨q, hq, heq⟩
      refine ⟨collarParameterEquiv.symm q,
        (mem_rightTriangleBasis_convexHull hr _).mpr hq, ?_⟩
      change F (collarParameterEquiv (collarParameterEquiv.symm q)) = z
      rwa [collarParameterEquiv.apply_symm_apply]
  have hfirst' (t : ℝ) : (face.boundary 2).map t = F (t * r, 0) := by
    rw [hboundary]
    rw [show Fin.succAbove (2 : Fin 3) 1 = 1 by decide]
    simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
      collarParameterEquiv, mul_comm]
  have hsecond' (t : ℝ) : (face.boundary 1).map t = F (0, t * r) := by
    rw [hboundary]
    simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
      collarParameterEquiv, mul_comm]
  have hchord' (t : ℝ) : (face.boundary 0).map t = F ((1 - t) * r, t * r) := by
    rw [hboundary]
    simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
      collarParameterEquiv, mul_comm]
    congr 1
    ring
  have ht (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ Icc (0 : ℝ) r :=
    ⟨mul_nonneg ht.1 hr.le, (mul_le_mul_of_nonneg_right ht.2 hr.le).trans_eq (one_mul r)⟩
  refine ⟨r, face, W, hr, hrT, hface ▸ hsub, ?_, ?_, ?_, ?_, hW, hpW, hface ▸ hcover⟩
  · intro t ht'
    rw [hsecond', hsecond _ (ht t ht')]
  · intro t ht'
    rw [hfirst', hfirst _ (ht t ht')]
  · intro t
    rw [hchord', hchord]
  · intro heq
    have hfirst0 := hfirst r (right_mem_Icc.mpr hr.le)
    have hsecond0 := hsecond r (right_mem_Icc.mpr hr.le)
    have heq' := F.injOn (hsource ⟨hr.le, le_rfl, by simp⟩)
      (hsource ⟨le_rfl, hr.le, by simp⟩) (hfirst0.trans (heq.trans hsecond0.symm))
    exact hr.ne' (congrArg Prod.fst heq')

end PoincareConjecture
