import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInteriorChart
import PoincareConjecture.Proofs.M76.Mathlib.CompactParameterThickening
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd
import PoincareConjecture.Proofs.M76.Triangulation.PLCubeCompression
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonHandleBoundaryGluing











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {T N E : Type*}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_cubical_collar_width
    {D : Set T} (h : closedBall (0 : T) 1 ≃ₜ D) (hh : h.IsFinitePL)
    (Phi : (T × N) ≃ᴬ[ℝ] E)
    {U V P : Set E} (hU : IsOpen U) (hV : IsOpen V) (hP : IsClosed P)
    (hDV : ∀ x ∈ D, Phi (x, 0) ∈ V)
    (hDP : ∀ x ∈ interior D, Phi (x, 0) ∉ P)
    (hfront : ∀ x : closedBall (0 : T) 1,
      ‖(x : T)‖ = 1 → Phi ((h x : T), 0) ∈ U) :
    ∃ (H : OpenPartialHomeomorph T T) (a b delta : ℝ),
      H.source = ball 0 1 ∧ H.target = interior D ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x : closedBall (0 : T) 1, H x = (h x : T)) ∧
      a ∈ Ioo 0 b ∧ b < 1 ∧ 0 < delta ∧
      (∀ x ∈ closedBall (0 : T) 1, a ≤ ‖x‖ → Phi (H x, 0) ∈ U) ∧
      Phi '' ((H '' closedBall (0 : T) b) ×ˢ closedBall (0 : N) (2 * delta)) ⊆ V \ P ∧
      Phi '' ((H '' sphere (0 : T) a) ×ˢ closedBall (0 : N) (2 * delta)) ⊆ U := by
  classical
  let C := closedBall (0 : T) 1
  let : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let f : C → E := fun x => Phi ((h x : T), 0)
  have hf : Continuous f := Phi.continuous.comp
    ((continuous_subtype_val.comp h.continuous).prodMk continuous_const)
  let B : Set C := f ⁻¹' Uᶜ
  have hB : IsCompact B := (hU.isClosed_compl.preimage hf).isCompact
  have hnorm (x : C) (hx : x ∈ B) : ‖(x : T)‖ < 1 := by
    have hle := mem_closedBall_zero_iff.mp x.property
    apply lt_of_le_of_ne hle
    intro heq
    exact hx (hfront x heq)
  obtain ⟨a, ha, haU⟩ : ∃ a : ℝ, a ∈ Ioo 0 1 ∧
      ∀ x : C, a ≤ ‖(x : T)‖ → f x ∈ U := by
    rcases B.eq_empty_or_nonempty with hBempty | hBne
    · refine ⟨1 / 2, by norm_num, ?_⟩
      intro x _
      by_contra hx
      have hxB : x ∈ B := hx
      rw [hBempty] at hxB
      exact hxB
    · obtain ⟨x, hx, hmax⟩ := hB.exists_isMaxOn hBne
        (continuous_norm.comp continuous_subtype_val).continuousOn
      obtain ⟨a, hxa, ha1⟩ := exists_between (hnorm x hx)
      refine ⟨a, ⟨lt_of_le_of_lt (norm_nonneg _) hxa, ha1⟩, ?_⟩
      intro y hay
      by_contra hy
      have hyB : y ∈ B := hy
      exact (not_lt_of_ge (hay.trans (hmax hyB))) hxa
  obtain ⟨H, hHs, hHt, hH, hHi, _, _, hHval, _⟩ := hh.exists_interior_chart rfl
  rw [interior_closedBall (0 : T) one_ne_zero] at hHs
  let b : ℝ := (a + 1) / 2
  have hab : a < b := by dsimp only [b]; linarith [ha.2]
  have hb1 : b < 1 := by dsimp only [b]; linarith [ha.2]
  have hclosedSource : closedBall (0 : T) b ⊆ H.source := by
    intro x hx
    rw [hHs, mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp hx).trans_lt hb1
  have hsphereSource : sphere (0 : T) a ⊆ H.source := by
    intro x hx
    rw [hHs, mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hx]
    exact ha.2
  have hclosed : IsCompact (H '' closedBall (0 : T) b) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (H.continuousOn_toFun.mono hclosedSource)
  have hsphere : IsCompact (H '' sphere (0 : T) a) :=
    (isCompact_sphere _ _).image_of_continuousOn
      (H.continuousOn_toFun.mono hsphereSource)
  have hclosedGood : ∀ y ∈ H '' closedBall (0 : T) b, Phi (y, 0) ∈ V \ P := by
    rintro _ ⟨x, hx, rfl⟩
    have hxD : H x ∈ interior D := hHt ▸ H.map_source (hclosedSource hx)
    exact ⟨hDV _ (interior_subset hxD), hDP _ hxD⟩
  have hleftover (x : T) (hx : x ∈ closedBall (0 : T) 1)
      (hax : a ≤ ‖x‖) : Phi (H x, 0) ∈ U := by
    rw [hHval ⟨x, hx⟩]
    exact haU ⟨x, hx⟩ hax
  have hsphereGood : ∀ y ∈ H '' sphere (0 : T) a, Phi (y, 0) ∈ U := by
    rintro _ ⟨x, hx, rfl⟩
    have hxa := mem_sphere_zero_iff_norm.mp hx
    exact hleftover x (mem_closedBall_zero_iff.mpr (hxa.trans_le ha.2.le)) hxa.ge
  obtain ⟨rV, hrV, hwidthV⟩ := Phi.continuous.exists_pos_closedBall_thickening
    hclosed (hV.inter hP.isOpen_compl) hclosedGood
  obtain ⟨rU, hrU, hwidthU⟩ := Phi.continuous.exists_pos_closedBall_thickening
    hsphere hU hsphereGood
  let delta : ℝ := min rV rU / 4
  have hd : 0 < delta := div_pos (lt_min hrV hrU) (by norm_num)
  have hdV : 2 * delta ≤ rV := by
    dsimp only [delta]
    nlinarith [min_le_left rV rU, min_le_right rV rU]
  have hdU : 2 * delta ≤ rU := by
    dsimp only [delta]
    nlinarith [min_le_left rV rU, min_le_right rV rU]
  refine ⟨H, a, b, delta, hHs, hHt, hH, hHi, hHval,
    ⟨ha.1, hab⟩, hb1, hd, hleftover, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hwidthV ⟨hx.1, closedBall_subset_closedBall hdV hx.2⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hwidthU ⟨hx.1, closedBall_subset_closedBall hdU hx.2⟩

end PoincareConjecture.M76
