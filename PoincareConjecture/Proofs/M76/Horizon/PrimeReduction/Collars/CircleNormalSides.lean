import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondSquareCoordinates
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
open Dehn
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem convex_signedTubeDiamond : Convex ℝ signedTubeDiamond := by
  have hpre : signedTubeDiamond =
      signedSquareToDiamond.symm ⁻¹' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
    ext x
    simpa using signedSquareToDiamond_mem (signedSquareToDiamond.symm x)
  rw [hpre]
  exact ((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).linear_preimage
    signedSquareToDiamond.symm.toLinearMap

theorem circle_tube_affine_height_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {a b : ℝ} (hab : a ≤ b) (sigma : C3 → E)
    (hSigma : ContinuousOn sigma (signedTubeDiamond ×ˢ Icc a b))
    (A : E →ᴬ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hzero : ∀ x ∈ signedTubeDiamond ×ˢ Icc a b,
      A (sigma x) = 0 ↔ x.1.1 = 0)
    (hinterior : sigma ((0, 0), a) ∈
      interior (sigma '' (signedTubeDiamond ×ˢ Icc a b))) :
    ((∀ x ∈ signedTubeDiamond ×ˢ Icc a b, 0 < x.1.1 → 0 < A (sigma x)) ∧
      (∀ x ∈ signedTubeDiamond ×ˢ Icc a b, x.1.1 < 0 → A (sigma x) < 0)) ∨
    ((∀ x ∈ signedTubeDiamond ×ˢ Icc a b, 0 < x.1.1 → A (sigma x) < 0) ∧
      (∀ x ∈ signedTubeDiamond ×ˢ Icc a b, x.1.1 < 0 → 0 < A (sigma x))) := by
  let D : Set C3 := signedTubeDiamond ×ˢ Icc a b
  let f : C3 → ℝ := A ∘ sigma
  let p : C3 →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ P2 ℝ)
  let Dp : Set C3 := D ∩ p ⁻¹' Ioi 0
  let Dn : Set C3 := D ∩ p ⁻¹' Iio 0
  have hconv : Convex ℝ D := convex_signedTubeDiamond.prod (convex_Icc a b)
  have hfp : IsPreconnected (f '' Dp) :=
    (hconv.inter ((convex_Ioi 0).linear_preimage p)).isPreconnected.image f
      ((A.continuous.comp_continuousOn hSigma).mono inter_subset_left)
  have hfn : IsPreconnected (f '' Dn) :=
    (hconv.inter ((convex_Iio 0).linear_preimage p)).isPreconnected.image f
      ((A.continuous.comp_continuousOn hSigma).mono inter_subset_left)
  have hdis : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
    exact disjoint_left.mpr (fun x hn hp =>
      (lt_trans (show x < 0 from hn) (show 0 < x from hp)).false)
  have hside (B : Set C3) (hB : B ⊆ D) (hnz : ∀ x ∈ B, p x ≠ 0)
      (hconn : IsPreconnected (f '' B)) :
      f '' B ⊆ Iio 0 ∨ f '' B ⊆ Ioi 0 := by
    apply hconn.subset_or_subset isOpen_Iio isOpen_Ioi hdis
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : f x ≠ 0 := fun hz => hnz x hx ((hzero x (hB hx)).mp hz)
    exact lt_or_gt_of_ne hx0
  have hp := hside Dp inter_subset_left (fun x hx => hx.2.ne') hfp
  have hn := hside Dn inter_subset_left (fun x hx => hx.2.ne) hfn
  have haxis : ((0, 0), a) ∈ D := by
    exact ⟨(signedTubeDiamond_coordinate_iff _).mpr (by norm_num), le_rfl, hab⟩
  have haxiszero : A (sigma ((0, 0), a)) = 0 := (hzero _ haxis).mpr rfl
  have hAsurj : Function.Surjective A :=
    A.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hA)
  have hopen : IsOpen (A '' interior (sigma '' D)) :=
    A.toAffineMap.isOpenMap A.continuous hAsurj _ isOpen_interior
  have hmem : (0 : ℝ) ∈ A '' interior (sigma '' D) :=
    ⟨sigma ((0, 0), a), hinterior, haxiszero⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  have hplus : (r / 2) ∈ A '' interior (sigma '' D) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [sub_zero, abs_of_pos (half_pos hr)]
    linarith
  have hminus : (-r / 2) ∈ A '' interior (sigma '' D) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [sub_zero, abs_of_neg (by linarith : -r / 2 < 0)]
    linarith
  obtain ⟨yp, hyp, hAp⟩ := hplus
  obtain ⟨xp, hxp, rfl⟩ := interior_subset hyp
  obtain ⟨yn, hyn, hAn⟩ := hminus
  obtain ⟨xn, hxn, rfl⟩ := interior_subset hyn
  have hfpos : 0 < f xp := by change 0 < A (sigma xp); rw [hAp]; positivity
  have hfneg : f xn < 0 := by change A (sigma xn) < 0; rw [hAn]; linarith
  have hxpnz : p xp ≠ 0 := fun hz => (hfpos.ne') ((hzero xp hxp).mpr hz)
  have hxnnz : p xn ≠ 0 := fun hz => hfneg.ne ((hzero xn hxn).mpr hz)
  rcases hp with hp | hp <;> rcases hn with hn | hn
  · exfalso
    rcases lt_or_gt_of_ne hxpnz with hx | hx
    · exact (lt_trans (hn ⟨xp, ⟨hxp, hx⟩, rfl⟩) hfpos).false
    · exact (lt_trans (hp ⟨xp, ⟨hxp, hx⟩, rfl⟩) hfpos).false
  · exact Or.inr ⟨fun x hx hs => hp ⟨x, ⟨hx, hs⟩, rfl⟩,
      fun x hx hs => hn ⟨x, ⟨hx, hs⟩, rfl⟩⟩
  · exact Or.inl ⟨fun x hx hs => hp ⟨x, ⟨hx, hs⟩, rfl⟩,
      fun x hx hs => hn ⟨x, ⟨hx, hs⟩, rfl⟩⟩
  · exfalso
    rcases lt_or_gt_of_ne hxnnz with hx | hx
    · exact (lt_trans hfneg (hn ⟨xn, ⟨hxn, hx⟩, rfl⟩)).false
    · exact (lt_trans hfneg (hp ⟨xn, ⟨hxn, hx⟩, rfl⟩)).false

end PoincareConjecture.M76
