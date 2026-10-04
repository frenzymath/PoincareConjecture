import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.StripHalfDiskComplement

/-!
# Orienting the tube by its actual middle-facing source arms

The two signs obtained by cutting the original source disk determine a
transverse square symmetry. Precomposing the old tube with this symmetry
places the two outer arms at the upper corners and the two middle arms at
the lower corners, while preserving the longitudinal coordinate and the
entire tube. See Dehn039, section 3.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

/-- The old tube coordinates expressed in the orientation selected by
the two middle-facing source arms. -/
noncomputable def tubeArmOrientation (s0 s1 : Bool) : C3 →ᴬ[ℝ] C3 :=
  let xy := ContinuousLinearMap.fst ℝ P2 ℝ
  let x := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp xy).toContinuousAffineMap
  let y := ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp xy).toContinuousAffineMap
  let t := (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap
  if s0 then
    if s1 then ((-y).prod x).prod t else (x.prod (-y)).prod t
  else
    if s1 then ((-x).prod y).prod t else (y.prod (-x)).prod t

/-- The orientation never changes the old longitudinal parameter. -/
theorem tubeArmOrientation_longitudinal (s0 s1 : Bool) (z : C3) :
    (tubeArmOrientation s0 s1 z).2 = z.2 := by
  cases s0 <;> cases s1 <;> rfl

/-- The inverse is another one of the four explicitly selected symmetries. -/
theorem tubeArmOrientation_inverse (s0 s1 : Bool) (z : C3) :
    tubeArmOrientation s0 s1 (tubeArmOrientation (!s1) (!s0) z) = z := by
  cases s0 <;> cases s1 <;> simp [tubeArmOrientation]

theorem tubeArmOrientation_injective (s0 s1 : Bool) :
    Function.Injective (tubeArmOrientation s0 s1) := by
  intro x y h
  have h' := congrArg (tubeArmOrientation (!s1) (!s0)) h
  have hx := tubeArmOrientation_inverse (!s1) (!s0) x
  have hy := tubeArmOrientation_inverse (!s1) (!s0) y
  simp only [Bool.not_not] at hx hy
  exact hx.symm.trans (h'.trans hy)

/-- Both directions of membership in the entire closed tube are preserved. -/
theorem tubeArmOrientation_mem_tube (s0 s1 : Bool) (z : C3) :
    tubeArmOrientation s0 s1 z ∈ tube ↔ z ∈ tube := by
  rcases z with ⟨⟨x, y⟩, t⟩
  cases s0 <;> cases s1 <;>
    simp [tubeArmOrientation, tube, Prod.le_def, neg_le, and_comm, and_left_comm, and_assoc]

/-- Reorientation preserves the entire old tube image. -/
theorem tubeArmOrientation_image (s0 s1 : Bool) :
    tubeArmOrientation s0 s1 '' tube = tube := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (tubeArmOrientation_mem_tube s0 s1 z).mpr hz
  · intro z hz
    exact ⟨tubeArmOrientation (!s1) (!s0) z,
      (tubeArmOrientation_mem_tube (!s1) (!s0) z).mpr hz,
      tubeArmOrientation_inverse s0 s1 z⟩

/-- The selected symmetry is a homeomorphism of the same whole tube. -/
noncomputable def tubeArmHomeomorph (s0 s1 : Bool) : tube ≃ₜ tube where
  toFun z := ⟨tubeArmOrientation s0 s1 z,
    (tubeArmOrientation_mem_tube s0 s1 z).mpr z.property⟩
  invFun z := ⟨tubeArmOrientation (!s1) (!s0) z,
    (tubeArmOrientation_mem_tube (!s1) (!s0) z).mpr z.property⟩
  left_inv z := by
    apply Subtype.ext
    have h := tubeArmOrientation_inverse (!s1) (!s0) (z : C3)
    simpa only [Bool.not_not] using h
  right_inv z := Subtype.ext (tubeArmOrientation_inverse s0 s1 z)
  continuous_toFun := ((tubeArmOrientation s0 s1).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((tubeArmOrientation (!s1) (!s0)).continuous.comp continuous_subtype_val).subtype_mk _

/-- Reorientation retains an actual embedding of the whole closed tube. -/
theorem reoriented_tube_embedding {X : Type*} [TopologicalSpace X]
    (τ : C3 → X) (hτ : Topology.IsEmbedding (fun z : tube => τ z)) (s0 s1 : Bool) :
    Topology.IsEmbedding (fun z : tube => (τ ∘ tubeArmOrientation s0 s1) z) :=
  hτ.comp (tubeArmHomeomorph s0 s1).isEmbedding

/-- The original chartwise PL tube map remains chartwise PL after the
constructed affine change of transverse coordinates. -/
theorem reoriented_tube_polyhedralPL
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    {τ : C3 → X} (hτ : PolyhedralPLInCharts e τ tube) (s0 s1 : Bool) :
    PolyhedralPLInCharts e (τ ∘ tubeArmOrientation s0 s1) tube := by
  have hbox := ((isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hbox
  have hPL : FinitePiecewiseAffineOn (tubeArmOrientation s0 s1) K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine (tubeArmOrientation s0 s1)⟩
  have hmaps : MapsTo (tubeArmOrientation s0 s1) K.space tube := fun z hz =>
    (tubeArmOrientation_mem_tube s0 s1 z).mpr (hKs.subset hz)
  simpa only [hKs, tube] using hτ.comp_finitePiecewiseAffineOn K hK hPL hmaps

/-- The four whole arm coordinates, not only their end points, are fixed
by the signs selected in the original source decomposition. -/
theorem tubeArmOrientation_corners (s0 s1 : Bool) (t : ℝ) :
    tubeArmOrientation s0 s1 ((-1, 1), t) =
      ((farArmParameter (!s0), farArmParameter (!s0)), t) ∧
    tubeArmOrientation s0 s1 ((-1, -1), t) =
      ((farArmParameter s1, -farArmParameter s1), t) ∧
    tubeArmOrientation s0 s1 ((1, -1), t) =
      ((farArmParameter s0, farArmParameter s0), t) ∧
    tubeArmOrientation s0 s1 ((1, 1), t) =
      ((farArmParameter (!s1), -farArmParameter (!s1)), t) := by
  cases s0 <;> cases s1 <;> norm_num [tubeArmOrientation, farArmParameter]

/-- Precomposition keeps the exact old tube image in any target. -/
theorem reoriented_tube_image {X : Type*} (τ : C3 → X) (s0 s1 : Bool) :
    (τ ∘ tubeArmOrientation s0 s1) '' tube = τ '' tube := by
  rw [image_comp, tubeArmOrientation_image]

/-- The actual two old sheet formulas give all four arm equations needed
by the upper and alternate attachment chains after reorientation. -/
theorem reoriented_tube_old_arm_equations
    {E X : Type*} (f : E → X) (c0 c1 : P2 → E) (τ : C3 → X)
    (h0 : ∀ p ∈ source, f (c0 p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c1 p) = τ ((p.2, -p.2), p.1))
    (s0 s1 : Bool) (t : Icc (0 : ℝ) 1) :
    f (c0 (t, farArmParameter (!s0))) = (τ ∘ tubeArmOrientation s0 s1) ((-1, 1), t) ∧
    f (c1 (t, farArmParameter s1)) = (τ ∘ tubeArmOrientation s0 s1) ((-1, -1), t) ∧
    f (c0 (t, farArmParameter s0)) = (τ ∘ tubeArmOrientation s0 s1) ((1, -1), t) ∧
    f (c1 (t, farArmParameter (!s1))) = (τ ∘ tubeArmOrientation s0 s1) ((1, 1), t) := by
  have hmem (s : Bool) : ((t : ℝ), farArmParameter s) ∈ source :=
    arm_far_subset_source s ⟨t.property, rfl⟩
  obtain ⟨hA, hL, hR, hC⟩ := tubeArmOrientation_corners s0 s1 (t : ℝ)
  dsimp only [Function.comp_apply]
  rw [hA, hL, hR, hC]
  exact ⟨h0 _ (hmem (!s0)), h1 _ (hmem s1), h0 _ (hmem s0), h1 _ (hmem (!s1))⟩

end PoincareMT.M76.Dehn.PolygonalCrossingResolution
