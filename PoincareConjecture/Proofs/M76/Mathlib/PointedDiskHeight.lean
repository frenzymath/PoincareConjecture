import PoincareConjecture.Proofs.M76.Mathlib.TriangularPointedRim
import PoincareConjecture.Proofs.M76.Mathlib.MarkedFinitePLBallCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPreimages
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineHeightSigns

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_pointed_height_with_rim_intervals_and_signs {d b : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (q : b) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      (∀ x ∈ d,
        (0 < r x → x ∈ closure (d ∩ {y | r y < r x})) ∧
          (r x < 2 → x ∈ closure (d ∩ {y | r x < r y}))) ∧
      (∀ t : ℝ, t ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (d ∩ {x | r x = t}) (b ∩ {x | r x = t})) ∧
      (∀ t : ℝ, t ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ t}) (b ∩ {x | r x = t})) ∧
      ∀ t : ℝ, t ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | t ≤ r x}) (b ∩ {x | r x = t}) := by
  have hzero : ((0, 0) : ℝ × ℝ) ∈ frontier base := by
    rw [frontier_base]
    norm_num [roof]
  obtain ⟨e, he, heb, heq⟩ :=
    hd.exists_homeomorph_boundary_point isFinitePLBallPair_base q ⟨(0, 0), hzero⟩
  obtain ⟨f, hf, hfval⟩ := he
  have hePL : e.IsFinitePL := ⟨f, hf, hfval⟩
  have hmap (x : E) (hx : x ∈ d) : f x ∈ base := by
    rw [← hfval ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  have hboundary (x : E) (hx : x ∈ d) : f x ∈ frontier base ↔ x ∈ b := by
    rw [← hfval ⟨x, hx⟩]
    exact (heb ⟨x, hx⟩).symm
  have hfinj : InjOn f d := by
    intro x hx y hy hxy
    have h : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext (by simpa only [hfval] using hxy)
    exact congrArg Subtype.val (e.injective h)
  have hfq : f q = (0, 0) := (hfval ⟨q, hd.1 q.property⟩).symm.trans
    (congrArg Subtype.val heq)
  let r : E → ℝ := cornerHeight ∘ f
  have hr : FinitePiecewiseAffineOn r d :=
    hf.postcomp (LinearMap.toContinuousLinearMap cornerHeight).toContinuousAffineMap
  have hmin (x : E) (hx : x ∈ d) : r x = 0 ↔ x = q := by
    change cornerHeight (f x) = 0 ↔ x = q
    rw [cornerHeight_eq_zero_iff (hmap x hx), ← hfq]
    exact ⟨hfinj hx (hd.1 q.property), fun h => congrArg f h⟩
  have htop : ((0, 1) : ℝ × ℝ) ∈ base := by
    rw [base_eq_triangle, TriangleDiskModel.mem_right_region_iff]
    norm_num
  let p : d := e.symm ⟨(0, 1), htop⟩
  have hfp : f p = (0, 1) := by
    rw [← hfval p]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hp : r p = 2 := by
    change cornerHeight (f p) = 2
    rw [hfp, cornerHeight_apply]
    norm_num
  have hcv : Convex ℝ base := by
    rw [base_eq_triangle]
    exact convex_convexHull ℝ _
  have hzeroHeight : cornerHeight (0, 0) = 0 := by norm_num [cornerHeight_apply]
  have htopHeight : cornerHeight (0, 1) = 2 := by norm_num [cornerHeight_apply]
  have hback (y : base) : r (e.symm y) = cornerHeight y := by
    change cornerHeight (f (e.symm y)) = cornerHeight y
    rw [← hfval (e.symm y)]
    exact congrArg cornerHeight (congrArg Subtype.val (e.apply_symm_apply y))
  have hsigns (x : E) (hx : x ∈ d) :
      (0 < r x → x ∈ closure (d ∩ {y | r y < r x})) ∧
        (r x < 2 → x ∈ closure (d ∩ {y | r x < r y})) := by
    let z : base := e ⟨x, hx⟩
    have hz : (e.symm z : E) = x := congrArg Subtype.val (e.symm_apply_apply _)
    have hzheight : cornerHeight z = r x := congrArg cornerHeight (hfval ⟨x, hx⟩)
    constructor
    · intro hpos
      have hlo : cornerHeight (0, 0) < cornerHeight z := by
        rw [hzeroHeight, hzheight]
        exact hpos
      have hmodel := hcv.mem_closure_lower_affine_height cornerHeight.toAffineMap
        z.property (isCompact_base.isClosed.frontier_subset hzero) hlo
      have h := e.symm.mem_lower_height_closure_of_height_preserving cornerHeight r hback z hmodel
      simpa only [hz] using h
    · intro hlt
      have hhi : cornerHeight z < cornerHeight (0, 1) := by
        rw [htopHeight, hzheight]
        exact hlt
      have hmodel := hcv.mem_closure_upper_affine_height cornerHeight.toAffineMap
        z.property htop hhi
      have h := e.symm.mem_upper_height_closure_of_height_preserving cornerHeight r hback z hmodel
      simpa only [hz] using h
  refine ⟨r, hr, fun x hx => ⟨cornerHeight_mem_Icc (hmap x hx), hmin x hx⟩,
    ⟨p, ?_, hp, ?_⟩, hsigns, ?_, ?_, ?_⟩
  · apply (hboundary p p.property).mp
    rw [hfp, frontier_base]
    norm_num [roof]
  · intro x hx
    change cornerHeight (f x) = 2 ↔ x = p
    rw [cornerHeight_eq_two_iff (hmap x hx), ← hfp]
    exact ⟨hfinj hx p.property, fun h => congrArg f h⟩
  · intro t ht
    have h := hePL.preimage_ballPair (isFinitePLBallPair_cornerHeight_section ht)
      inter_subset_left hfval
    have hsource : d ∩ f ⁻¹' (base ∩ {z | cornerHeight z = t}) =
        d ∩ {x | r x = t} := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.2⟩,
        fun hx => ⟨hx.1, hmap x hx.1, hx.2⟩⟩
    have hrim : d ∩ f ⁻¹' (frontier base ∩ {z | cornerHeight z = t}) =
        b ∩ {x | r x = t} := by
      ext x
      exact ⟨fun hx => ⟨(hboundary x hx.1).mp hx.2.1, hx.2.2⟩,
        fun hx => ⟨hd.1 hx.1, (hboundary x (hd.1 hx.1)).mpr hx.1, hx.2⟩⟩
    rwa [hsource, hrim] at h
  · intro t ht
    have h := hePL.preimage_ballPair (isFinitePLBallPair_cornerHeight_rim_sublevel ht)
      (fun x hx => isCompact_base.isClosed.frontier_subset hx.1) hfval
    have hsource : d ∩ f ⁻¹' (frontier base ∩ {z | cornerHeight z ≤ t}) =
        b ∩ {x | r x ≤ t} := by
      ext x
      exact ⟨fun hx => ⟨(hboundary x hx.1).mp hx.2.1, hx.2.2⟩,
        fun hx => ⟨hd.1 hx.1, (hboundary x (hd.1 hx.1)).mpr hx.1, hx.2⟩⟩
    have hrim : d ∩ f ⁻¹' (frontier base ∩ {z | cornerHeight z = t}) =
        b ∩ {x | r x = t} := by
      ext x
      exact ⟨fun hx => ⟨(hboundary x hx.1).mp hx.2.1, hx.2.2⟩,
        fun hx => ⟨hd.1 hx.1, (hboundary x (hd.1 hx.1)).mpr hx.1, hx.2⟩⟩
    rwa [hsource, hrim] at h
  · intro t ht
    have h := hePL.preimage_ballPair (isFinitePLBallPair_cornerHeight_rim_superlevel ht)
      (fun x hx => isCompact_base.isClosed.frontier_subset hx.1) hfval
    have hsource : d ∩ f ⁻¹' (frontier base ∩ {z | t ≤ cornerHeight z}) =
        b ∩ {x | t ≤ r x} := by
      ext x
      exact ⟨fun hx => ⟨(hboundary x hx.1).mp hx.2.1, hx.2.2⟩,
        fun hx => ⟨hd.1 hx.1, (hboundary x (hd.1 hx.1)).mpr hx.1, hx.2⟩⟩
    have hrim : d ∩ f ⁻¹' (frontier base ∩ {z | cornerHeight z = t}) =
        b ∩ {x | r x = t} := by
      ext x
      exact ⟨fun hx => ⟨(hboundary x hx.1).mp hx.2.1, hx.2.2⟩,
        fun hx => ⟨hd.1 hx.1, (hboundary x (hd.1 hx.1)).mpr hx.1, hx.2⟩⟩
    rwa [hsource, hrim] at h

theorem IsFinitePLBallPair.exists_pointed_height_with_rim_intervals {d b : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (q : b) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      (∀ t : ℝ, t ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (d ∩ {x | r x = t}) (b ∩ {x | r x = t})) ∧
      (∀ t : ℝ, t ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ t}) (b ∩ {x | r x = t})) ∧
      ∀ t : ℝ, t ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | t ≤ r x}) (b ∩ {x | r x = t}) := by
  obtain ⟨r, hr, hmin, hmax, _, hrest⟩ :=
    hd.exists_pointed_height_with_rim_intervals_and_signs q
  exact ⟨r, hr, hmin, hmax, hrest⟩

theorem IsFinitePLBallPair.exists_pointed_height_with_rim_sublevels {d b : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (q : b) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      (∀ t : ℝ, t ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (d ∩ {x | r x = t}) (b ∩ {x | r x = t})) ∧
      ∀ t : ℝ, t ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ t}) (b ∩ {x | r x = t}) := by
  obtain ⟨r, hr, hmin, hmax, hlevels, hrsub, _⟩ := hd.exists_pointed_height_with_rim_intervals q
  exact ⟨r, hr, hmin, hmax, hlevels, hrsub⟩

theorem IsFinitePLBallPair.exists_pointed_height {d b : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (q : b) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      ∀ t : ℝ, t ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (d ∩ {x | r x = t}) (b ∩ {x | r x = t}) := by
  obtain ⟨r, hr, hmin, hmax, hlevels, _⟩ := hd.exists_pointed_height_with_rim_sublevels q
  exact ⟨r, hr, hmin, hmax, hlevels⟩

end Set
