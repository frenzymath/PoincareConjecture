import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V" => ((ℝ × ℝ) × ℝ)

theorem exists_disk_patch_of_plane_chart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (H : OpenPartialHomeomorph E V)
    (hH : LocallyPiecewiseAffineOn H.symm H.target)
    (hS : ∀ x ∈ H.source, x ∈ S ↔ (H x).2 = 0)
    {p : E} (hp : p ∈ S) (hpH : p ∈ H.source) :
    ∃ d q : Set E, IsFinitePLBallPair (ℝ × ℝ) d q ∧ d ⊆ S ∧ p ∈ d \ q ∧
      IsOpen ((Subtype.val : S → E) ⁻¹' (d \ q)) := by
  let u : ℝ × ℝ := (H p).1
  let a : (ℝ × ℝ) →ᴬ[ℝ] V :=
    ((ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) u).toContinuousAffineMap).prod
      (ContinuousAffineMap.const ℝ (ℝ × ℝ) (0 : ℝ))
  have ha (x : ℝ × ℝ) : a x = (u + x, 0) := rfl
  have hplane : (H p).2 = 0 := (hS p hpH).mp hp
  have ha0 : a 0 = H p := by
    rw [ha, add_zero]
    exact Prod.ext rfl hplane.symm
  have hzero : (0 : ℝ × ℝ) ∈ a ⁻¹' H.target := by
    change a 0 ∈ H.target
    rw [ha0]
    exact H.map_source hpH
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp
    (H.open_target.preimage a.continuous) 0 hzero
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hbase := base_ballPair hr
  have hbaseball : base r = Metric.closedBall (0 : ℝ × ℝ) r := by
    ext x
    simp only [base, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right,
      Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
  have haT : MapsTo a (base r) H.target := by
    intro x hx
    apply hεsub
    rw [hbaseball] at hx
    exact Metric.closedBall_subset_ball (half_lt_self hε) hx
  have hcopy := hbase
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have haPL : FinitePiecewiseAffineOn a (base r) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine a⟩
  let f : (ℝ × ℝ) → E := H.symm ∘ a
  have hfPL : FinitePiecewiseAffineOn f (base r) :=
    hH.comp_finitePiecewiseAffineOn haPL haT
  have hfi : InjOn f (base r) := by
    intro x hx y hy hxy
    have haxy := congrArg H hxy
    change H (H.symm (a x)) = H (H.symm (a y)) at haxy
    rw [H.right_inv (haT hx), H.right_inv (haT hy), ha, ha] at haxy
    exact add_left_cancel (congrArg Prod.fst haxy)
  have hfs (x : ℝ × ℝ) (hx : x ∈ base r) : f x ∈ H.source :=
    H.map_target (haT hx)
  have hfS (x : ℝ × ℝ) (hx : x ∈ base r) : f x ∈ S := by
    apply (hS _ (hfs x hx)).mpr
    change (H (H.symm (a x))).2 = 0
    rw [H.right_inv (haT hx), ha]
  have hfr : frontier (base r) = baseBoundary r :=
    hbase.frontier_eq_of_finrank_eq rfl
  have hint : base r \ baseBoundary r = interior (base r) := by
    rw [← hfr, frontier, hbase.isCompact.isClosed.closure_eq]
    ext x
    simp only [mem_sdiff]
    have hx : x ∈ interior (base r) → x ∈ base r := fun h => interior_subset h
    tauto
  have himage : f '' base r \ f '' baseBoundary r = f '' interior (base r) := by
    rw [← hfi.image_sdiff_subset hbase.1, hint]
  have hzeroI : (0 : ℝ × ℝ) ∈ interior (base r) := by
    rw [hbaseball]
    exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr)
  have hfp : f 0 = p := by
    change H.symm (a 0) = p
    rw [ha0, H.left_inv hpH]
  refine ⟨f '' base r, f '' baseBoundary r, hbase.image hfPL hfi, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hfS x hx
  · rw [himage]
    exact ⟨0, hzeroI, hfp⟩
  · let b : E → (ℝ × ℝ) := fun x => (H x).1 - u
    let U : Set E := H.source ∩ b ⁻¹' interior (base r)
    have hbcont : ContinuousOn b H.source :=
      (continuous_fst.comp_continuousOn H.continuousOn).sub continuousOn_const
    have hU : IsOpen U := hbcont.isOpen_inter_preimage H.open_source isOpen_interior
    have heq : (Subtype.val : S → E) ⁻¹' (f '' interior (base r)) =
        (Subtype.val : S → E) ⁻¹' U := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hyb := interior_subset hy
        have hxval : (x : E) = f y := hxy.symm
        change (x : E) ∈ U
        rw [hxval]
        refine ⟨hfs y hyb, ?_⟩
        change (H (H.symm (a y))).1 - u ∈ interior (base r)
        rw [H.right_inv (haT hyb), ha]
        simpa only [add_sub_cancel_left] using hy
      · rintro ⟨hxH, hxb⟩
        refine ⟨b x, hxb, ?_⟩
        change H.symm (a (b x)) = (x : E)
        have hax : a (b x) = H x := by
          rw [ha]
          apply Prod.ext
          · change u + ((H x).1 - u) = (H x).1
            abel
          · exact ((hS x hxH).mp x.property).symm
        rw [hax, H.left_inv hxH]
    rw [himage, heq]
    exact hU.preimage continuous_subtype_val

end PoincareConjecture.M76.HamiltonIndexOne
