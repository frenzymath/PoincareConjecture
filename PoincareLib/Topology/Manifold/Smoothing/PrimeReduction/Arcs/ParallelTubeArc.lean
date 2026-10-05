import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleArc.SignedDiamondSquareCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLIntervals

/-!
# Parallel intervals in a signed tube

A nonzero transverse displacement on the triangle sheet constructs an
actual finite PL interval avoiding the whole sphere sheet. Its endpoint
values are the complete tube's corresponding endface values.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1

/-- Construct the displaced triangle-sheet interval, including its
finite PL parameterization and exact endpoint rim. Outer edge ordering
is a separate conclusion of the planar returning-ribbon argument. -/
theorem exists_parallel_signed_tube_arc
    {T triangle sphere : Set V3}
    (tube : ↥(Dehn.signedTubeDiamond ×ˢ I) ≃ₜ T) (htube : tube.IsFinitePL)
    (htriangle : ∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
      (x : P3).1 ∈ Dehn.signedTubeSheet 0 ↔ (tube x : V3) ∈ triangle)
    (hsphere : ∀ x : ↥(Dehn.signedTubeDiamond ×ˢ I),
      (x : P3).1 ∈ Dehn.signedTubeSheet 1 ↔ (tube x : V3) ∈ sphere)
    {c : ℝ} (hc : |c| ≤ 1) (hc0 : c ≠ 0) :
    ∃ (f : ℝ → V3) (A : Set V3) (b : I ≃ₜ A),
      FinitePiecewiseAffineOn f I ∧ InjOn f I ∧ A = f '' I ∧
      b.IsFinitePL ∧ (∀ t : I, (b t : V3) = f t) ∧
      IsFinitePLBallPair ℝ A {f 0, f 1} ∧ f 0 ≠ f 1 ∧
      A ⊆ T ∩ triangle ∧ Disjoint A sphere ∧
      ∀ t : I, f t = (tube ⟨((0, c), (t : ℝ)),
        (Dehn.signedTubeDiamond_coordinate_iff (0, c)).mpr (by simpa using hc),
        t.property⟩ : V3) := by
  classical
  have hdc : (0, c) ∈ Dehn.signedTubeDiamond :=
    (Dehn.signedTubeDiamond_coordinate_iff (0, c)).mpr (by simpa using hc)
  obtain ⟨F, hF, hFval⟩ := htube
  let line : ℝ →ᴬ[ℝ] P3 :=
    (ContinuousAffineMap.const ℝ ℝ (0, c)).prod (ContinuousAffineMap.id ℝ ℝ)
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hcopy := hI
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hline : FinitePiecewiseAffineOn line I :=
    ⟨K, hK, hKs, K.affineOnFaces_affine line⟩
  let f := F ∘ line
  have hf : FinitePiecewiseAffineOn f I := hF.comp hline (fun _ ht => ⟨hdc, ht⟩)
  have hval (t : I) : f t = (tube ⟨((0, c), (t : ℝ)), hdc, t.property⟩ : V3) :=
    (hFval ⟨((0, c), (t : ℝ)), hdc, t.property⟩).symm
  have hi : InjOn f I := by
    intro t ht u hu htu
    have heq : tube ⟨((0, c), t), hdc, ht⟩ = tube ⟨((0, c), u), hdc, hu⟩ := by
      apply Subtype.ext
      exact (hval ⟨t, ht⟩).symm.trans (htu.trans (hval ⟨u, hu⟩))
    exact congrArg (fun x : ↥(Dehn.signedTubeDiamond ×ˢ I) => (x : P3).2)
      (tube.injective heq)
  obtain ⟨b, hb, hbval⟩ := hf.exists_homeomorph_image hi
  have hball : IsFinitePLBallPair ℝ (f '' I) {f 0, f 1} := by
    simpa only [image_pair] using hI.image hf hi
  have h01 : f 0 ≠ f 1 := by
    intro heq
    have := hi (show (0 : ℝ) ∈ I by simp) (show (1 : ℝ) ∈ I by simp) heq
    norm_num at this
  refine ⟨f, f '' I, b, hf, hi, rfl, hb, hbval, hball, h01, ?_, ?_, hval⟩
  · rintro _ ⟨t, ht, rfl⟩
    rw [hval ⟨t, ht⟩]
    refine ⟨(tube ⟨((0, c), t), hdc, ht⟩).property, (htriangle _).mp ?_⟩
    exact (Dehn.signedTubeSheet_coordinate_iff (0, c) hdc 0).mpr (by simp)
  · apply disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ hS
    rw [hval ⟨t, ht⟩] at hS
    have hz := (Dehn.signedTubeSheet_coordinate_iff (0, c) hdc 1).mp ((hsphere _).mpr hS)
    exact hc0 (by simpa using hz)

end PoincareMT.M76
