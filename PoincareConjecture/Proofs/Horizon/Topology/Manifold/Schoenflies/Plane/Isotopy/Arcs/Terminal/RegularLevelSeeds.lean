import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sublevel.Minimum
import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

theorem exists_points_below_and_above_regular_level
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {q : S2} (hregular : mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    {b : Real} (hqb : h q = b) {U : Set S2} (hU : IsOpen U) (hqU : q ∈ U) :
    (∃ x ∈ U, h x < b) ∧ (∃ y ∈ U, b < h y) := by
  constructor
  · by_contra hnone
    have hmin : IsLocalMin h q := by
      filter_upwards [hU.mem_nhds hqU] with x hx
      rw [hqb]
      exact le_of_not_gt (fun hxb => hnone ⟨x, hx, hxb⟩)
    exact hregular (Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh hmin)
  · by_contra hnone
    have hmax : IsLocalMax h q := by
      filter_upwards [hU.mem_nhds hqU] with y hy
      rw [hqb]
      exact le_of_not_gt (fun hby => hnone ⟨y, hy, hby⟩)
    apply hregular
    have hn := Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh.neg hmax.neg
    change mfderiv (𝓡 2) 𝓘(Real, Real) (-h) q = 0 at hn
    rw [mfderiv_neg] at hn
    exact neg_eq_zero.mp hn

theorem exists_regular_level_seeds_with_negative_separator
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {q : S2} (hregular : mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    {b : Real} (hqb : h q = b) {U : Set S2} (hU : IsOpen U) (hqU : q ∈ U)
    (l : S2 → Real) (hl : Continuous l) (hlq : l q < 0) :
    (∃ x ∈ U, h x < b ∧ l x < 0) ∧ (∃ y ∈ U, b < h y ∧ l y < 0) := by
  obtain ⟨⟨x, hx, hxb⟩, ⟨y, hy, hby⟩⟩ := exists_points_below_and_above_regular_level
    hh hregular hqb (hU.inter (isOpen_lt hl continuous_const)) ⟨hqU, hlq⟩
  exact ⟨⟨x, hx.1, hxb, hx.2⟩, ⟨y, hy.1, hby, hy.2⟩⟩

theorem exists_regular_level_seeds_with_positive_separator
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {q : S2} (hregular : mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    {b : Real} (hqb : h q = b) {U : Set S2} (hU : IsOpen U) (hqU : q ∈ U)
    (l : S2 → Real) (hl : Continuous l) (hlq : 0 < l q) :
    (∃ x ∈ U, h x < b ∧ 0 < l x) ∧ (∃ y ∈ U, b < h y ∧ 0 < l y) := by
  obtain ⟨⟨x, hx, hxb⟩, ⟨y, hy, hby⟩⟩ := exists_points_below_and_above_regular_level
    hh hregular hqb (hU.inter (isOpen_lt continuous_const hl)) ⟨hqU, hlq⟩
  exact ⟨⟨x, hx.1, hxb, hx.2⟩, ⟨y, hy.1, hby, hy.2⟩⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
