import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

theorem morseRadialDisc_geometry (r : ℝ) (hr : 0 < r) :
    IsOpen {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2} ∧
      IsCompact {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} ∧
      closure {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2} =
        {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} := by
  let e : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have he (x : E2) : ‖x‖ ^ 2 = (e x).1 ^ 2 + (e x).2 ^ 2 := by
    change ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2
    simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  have hball : e '' ball (0 : E2) r =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2} := by
    ext s
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (e x).1 ^ 2 + (e x).2 ^ 2 < r ^ 2
      rw [← he]
      exact (sq_lt_sq₀ (norm_nonneg x) hr.le).mpr (mem_ball_zero_iff.mp hx)
    · intro hs
      change s.1 ^ 2 + s.2 ^ 2 < r ^ 2 at hs
      refine ⟨e.symm s, mem_ball_zero_iff.mpr ?_, e.apply_symm_apply s⟩
      apply (sq_lt_sq₀ (norm_nonneg _) hr.le).mp
      simpa only [he, e.apply_symm_apply] using hs
  have hclosed : e '' closedBall (0 : E2) r =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} := by
    ext s
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (e x).1 ^ 2 + (e x).2 ^ 2 ≤ r ^ 2
      rw [← he]
      exact (sq_le_sq₀ (norm_nonneg x) hr.le).mpr (mem_closedBall_zero_iff.mp hx)
    · intro hs
      change s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2 at hs
      refine ⟨e.symm s, mem_closedBall_zero_iff.mpr ?_, e.apply_symm_apply s⟩
      apply (sq_le_sq₀ (norm_nonneg _) hr.le).mp
      simpa only [he, e.apply_symm_apply] using hs
  refine ⟨hball ▸ e.toHomeomorph.isOpenMap _ isOpen_ball,
    hclosed ▸ (isCompact_closedBall (0 : E2) r).image e.continuous, ?_⟩
  rw [← hball, ← e.image_closure, closure_ball _ hr.ne', hclosed]

theorem morseRadialChart_geometry
    (P : OpenPartialHomeomorph (ℝ × ℝ) E2) (R : ℝ) (hR : 0 < R)
    (hsource : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ R ^ 2} ⊆ P.source) :
    (∀ r : ℝ, 0 < r → r ≤ R →
      IsOpen (P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}) ∧
      IsCompact (closure (P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2})) ∧
      closure (P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}) =
        P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}) ∧
    (∀ r t : ℝ, 0 < r → r < t → t ≤ R →
      closure (P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}) ⊆
        P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < t ^ 2}) := by
  have hgeom (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
      IsOpen (P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}) ∧
      IsCompact (closure (P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2})) ∧
      closure (P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}) =
        P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} := by
    obtain ⟨hopen, hcompact, hclosure⟩ := morseRadialDisc_geometry r hr
    have hB : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} ⊆ P.source := by
      intro s hs
      exact hsource (hs.trans ((sq_le_sq₀ hr.le hR.le).mpr hrR))
    have hDB : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2} ⊆
        {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} := by
      intro s hs
      exact (show s.1 ^ 2 + s.2 ^ 2 < r ^ 2 from hs).le
    have himage := hcompact.image_of_continuousOn (P.continuousOn.mono hB)
    have heq : closure (P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}) =
        P '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} := by
      apply Subset.antisymm
      · exact closure_minimal (image_mono hDB) himage.isClosed
      · rintro y ⟨s, hs, rfl⟩
        exact mem_closure_image
          (P.continuousOn.continuousAt (P.open_source.mem_nhds (hB hs)))
          (hclosure.symm ▸ hs)
    exact ⟨P.isOpen_image_of_subset_source hopen (hDB.trans hB),
      heq.symm ▸ himage, heq⟩
  refine ⟨hgeom, ?_⟩
  intro r t hr hrt htR
  rw [(hgeom r hr (hrt.le.trans htR)).2.2]
  exact image_mono (fun _ hs => hs.trans_lt ((sq_lt_sq₀ hr.le (hr.trans hrt).le).mpr hrt))

end PoincareConjecture.M25.Topology3D
