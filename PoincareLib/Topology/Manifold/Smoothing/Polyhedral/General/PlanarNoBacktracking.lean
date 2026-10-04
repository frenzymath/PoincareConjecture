import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.PlanarRadialArc

/-!
# No reversal of adjacent projected planar edges

Two consecutive short straight edges cannot turn back along the circle
when neither outer vertex belongs to the other edge's spherical image.
This is the local cyclic-order argument in Cairns 1940, Section 6,
p. 802; see M76 derivation 23.
-/

set_option autoImplicit false

open Set NormedSpace

namespace Complex

/-- Nonincident vertex directions prohibit reversal along two adjacent
short edges. The angles are arbitrary real lifts.
See Cairns p. 802 and M76 derivation 23. -/
theorem lt_of_no_radial_backtracking {a b c : ℝ} (hab : a < b)
    (hba : b - a < Real.pi) (hbc : b - c < Real.pi)
    (hc : (Circle.exp c : ℂ) ∉ NormedSpace.normalize ''
      segment ℝ (Circle.exp a : ℂ) (Circle.exp b))
    (ha : (Circle.exp a : ℂ) ∉ NormedSpace.normalize ''
      segment ℝ (Circle.exp b : ℂ) (Circle.exp c)) : b < c := by
  by_contra h
  have hcb : c ≤ b := le_of_not_gt h
  by_cases hac : a ≤ c
  · apply hc
    rw [normalize_image_segment_circleExp hab hba]
    exact ⟨c, ⟨hac, hcb⟩, rfl⟩
  · have hca : c < a := lt_of_not_ge hac
    apply ha
    rw [segment_symm ℝ, normalize_image_segment_circleExp (hca.trans hab) hbc]
    exact ⟨a, ⟨hca.le, hab.le⟩, rfl⟩

end Complex

namespace Circle

/-- The signed short angular increment between two unit vertices.
See Cairns p. 802 and M76 derivation 23. -/
noncomputable def shortIncrement (x y : Circle) : ℝ := Complex.arg (y / x : Circle)

/-- The signed increment recovers the second circle vertex by rotation.
See Cairns p. 802 and M76 derivation 23. -/
theorem mul_exp_shortIncrement (x y : Circle) : x * Circle.exp (shortIncrement x y) = y := by
  rw [shortIncrement, Circle.exp_arg]
  exact mul_div_cancel _ _

/-- The principal angular increment is strictly larger than minus pi.
See Cairns p. 802 and M76 derivation 23. -/
theorem neg_pi_lt_shortIncrement (x y : Circle) : -Real.pi < shortIncrement x y :=
  Complex.neg_pi_lt_arg _

/-- Independent endpoint vectors exclude the antipodal value of the
principal increment. See Cairns p. 802 and M76 derivation 23. -/
theorem shortIncrement_lt_pi {x y : Circle}
    (hlin : LinearIndependent ℝ ((↑) : ↥({(x : ℂ), (y : ℂ)} : Set ℂ) → ℂ)) :
    shortIncrement x y < Real.pi := by
  apply lt_of_le_of_ne (Complex.arg_le_pi _)
  intro hpi
  have hpi' : shortIncrement x y = Real.pi := hpi
  have he := congrArg (fun z : Circle => (z : ℂ)) (mul_exp_shortIncrement x y)
  rw [hpi'] at he
  have hy : (y : ℂ) = -(x : ℂ) := by
    simpa only [coe_mul, coe_exp, Complex.exp_pi_mul_I, mul_neg_one] using he.symm
  apply hlin.zero_notMem_convexHull
  rw [convexHull_pair]
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  rw [hy, smul_neg, add_neg_cancel]

/-- Distinct unit vertices have a nonzero signed angular increment.
See Cairns p. 802 and M76 derivation 23. -/
theorem shortIncrement_ne_zero {x y : Circle} (hxy : x ≠ y) : shortIncrement x y ≠ 0 := by
  intro hzero
  have he := mul_exp_shortIncrement x y
  rw [hzero, Circle.exp_zero, mul_one] at he
  exact hxy he

end Circle
