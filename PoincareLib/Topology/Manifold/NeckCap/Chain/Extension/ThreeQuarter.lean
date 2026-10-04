import PoincareLib.Topology.Manifold.NeckCap.Chain.Extension.InteriorCapture
import PoincareLib.Topology.Manifold.NeckCap.Chain.Extension.DistanceUpper
import PoincareLib.Topology.Manifold.NeckCap.Cap.Collar
import PoincareLib.Topology.Manifold.NeckCap.Chain.Extension.NoReturn

/-!
# Length obstruction to returning across a frontier neck

A path from outside an old neck to its negative half must be long if it
crosses the old central sphere. The two path segments pay separately for
the full old radius and for the depth of the negative half. Separation then
forces overlap with a neck centered at the positive frontier to remain in
the old positive three quarters.

Reference: Morgan--Tian, Lemmas A.17--A.18, pp. 506--507.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

/-- Crossing the central sphere from a point almost one radius from the center
to the negative half costs more than a comparable neck's center-to-end length. -/
theorem pathELength_lower_of_cross_central_sphere_of_distance (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 γ)
    (hstart : ENNReal.ofReal ((0.98 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.edist N.center (γ 0))
    (haxis : (N.coordinate_inverse (γ 1)).2 ≤ -N.epsilon⁻¹ / 2)
    {t : ℝ} (ht : t ∈ Icc 0 1) (hcross : γ t ∈ N.central_sphere) :
    ENNReal.ofReal ((1.4 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := N.scale_pos
  have hi := inv_pos.mpr N.epsilon_pos
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hi.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hroot : (0.99 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have houtside : γ 1 ∉ N.coordinate_map ''
      (univ ×ˢ Icc (-((0.49 : ℝ) * N.epsilon⁻¹)) ((0.49 : ℝ) * N.epsilon⁻¹)) := by
    intro hx
    have h := (N.mem_coordinate_slab_iff (by linarith) (by linarith)).mp hx
    linarith [h.2.1]
  have henddist : ENNReal.ofReal ((0.48 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.edist N.center (γ 1) := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_)
      (N.edist_center_lower_of_not_mem_coordinate_slab
        (r := (0.49 : ℝ) * N.epsilon⁻¹) ⟨by positivity, by linarith⟩ houtside)
    nlinarith [mul_le_mul_of_nonneg_right hroot (mul_nonneg hs.le hi.le)]
  have hdiam := N.edist_central_sphere_le_two_pi_mul_scale
    N.center_on_central_sphere hcross
  have hleft : ENNReal.ofReal ((0.98 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      ENNReal.ofReal ((2 * Real.pi) * N.scale) + g.pathELength γ 0 t := by
    apply hstart.trans
    calc
      _ ≤ g.edist N.center (γ t) + g.edist (γ t) (γ 0) :=
        Manifold.riemannianEDist_triangle
      _ = g.edist N.center (γ t) + g.edist (γ 0) (γ t) := by
        rw [show g.edist (γ t) (γ 0) = g.edist (γ 0) (γ t) from
          Manifold.riemannianEDist_comm]
      _ ≤ _ := add_le_add hdiam
        (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn rfl rfl ht.1)
  have hright : ENNReal.ofReal ((0.48 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      ENNReal.ofReal ((2 * Real.pi) * N.scale) + g.pathELength γ t 1 :=
    henddist.trans (Manifold.riemannianEDist_triangle.trans (add_le_add hdiam
      (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn rfl rfl ht.2)))
  have hsum := add_le_add hleft hright
  have hadd : g.pathELength γ 0 t + g.pathELength γ t 1 = g.pathELength γ 0 1 :=
    Manifold.pathELength_add ht.1 ht.2
  rw [add_add_add_comm, hadd] at hsum
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hsum
  by_contra hnot
  have hshort := lt_of_not_ge hnot
  have hlt := ENNReal.add_lt_add_left
    (ENNReal.ofReal_ne_top (r := (2 * Real.pi) * N.scale + (2 * Real.pi) * N.scale))
    hshort
  have hstrict := hsum.trans_lt hlt
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hstrict
  have hnum := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hstrict
  have hpi := mul_le_mul_of_nonneg_right Real.pi_le_four hs.le
  have hlen := mul_le_mul_of_nonneg_left hinv hs.le
  nlinarith

/-- Crossing the central sphere between an exterior point and the negative
half costs more than the full center-to-end length of a comparable neck. -/
theorem pathELength_lower_of_cross_central_sphere (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 γ)
    (hstart : γ 0 ∉ N.carrier) (_hend : γ 1 ∈ N.carrier)
    (haxis : (N.coordinate_inverse (γ 1)).2 ≤ -N.epsilon⁻¹ / 2)
    {t : ℝ} (ht : t ∈ Icc 0 1) (hcross : γ t ∈ N.central_sphere) :
    ENNReal.ofReal ((1.4 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ 0 1 := by
  apply N.pathELength_lower_of_cross_central_sphere_of_distance hε hγ _ haxis ht hcross
  apply (ENNReal.ofReal_le_ofReal ?_).trans
    (N.balanced_edist_lower_of_not_mem_carrier hε hstart)
  have hi := inv_pos.mpr N.epsilon_pos
  nlinarith [mul_pos N.scale_pos hi]

/-- Any overlap with the old negative half lies in the same complementary
component as the successor center. This is obtained from an actual short
smooth path; no path or overlap certificate is assumed. -/
theorem mem_component_complement_of_negative_half_overlap_of_distance
    (N N' : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (heq : N'.epsilon = N.epsilon)
    (hscale : N'.scale ≤ (1.01 : ℝ) * N.scale)
    (hdistance : ENNReal.ofReal ((0.98 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.edist N.center N'.center) {x : M}
    (hx : x ∈ N.carrier) (hx' : x ∈ N'.carrier)
    (haxis : (N.coordinate_inverse x).2 ≤ -N.epsilon⁻¹ / 2) :
    x ∈ connectedComponentIn N.central_sphereᶜ N'.center := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := N.scale_pos
  have hi := inv_pos.mpr N.epsilon_pos
  have hupper := N'.edist_center_le_balanced_upper_of_mem_closure
    (heq ▸ hε) (subset_closure hx')
  rw [heq] at hupper
  have hstrict : g.edist N'.center x <
      ENNReal.ofReal ((1.4 : ℝ) * N.scale * N.epsilon⁻¹) := by
    apply hupper.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hscale hi.le, mul_pos hs hi]
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hstrict
      (show (0 : ℝ) < 1 by norm_num)
  have havoid : γ '' Icc 0 1 ⊆ N.central_sphereᶜ := by
    rintro y ⟨t, ht, rfl⟩ hcross
    have hlower := N.pathELength_lower_of_cross_central_sphere_of_distance hε hγ
      (hγ0 ▸ hdistance) (hγ1 ▸ haxis) ht hcross
    exact not_lt_of_ge hlower hlength
  have hconnected : IsPreconnected (γ '' Icc 0 1) :=
    isPreconnected_Icc.image γ hγ.continuous.continuousOn
  exact hconnected.subset_connectedComponentIn
    ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩ havoid
    ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩

/-- The exterior-center version follows from the neck escape-radius bound. -/
theorem mem_component_complement_of_negative_half_overlap
    (N N' : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (heq : N'.epsilon = N.epsilon)
    (hscale : N'.scale ≤ (1.01 : ℝ) * N.scale)
    (hcenter : N'.center ∉ N.carrier) {x : M}
    (hx : x ∈ N.carrier) (hx' : x ∈ N'.carrier)
    (haxis : (N.coordinate_inverse x).2 ≤ -N.epsilon⁻¹ / 2) :
    x ∈ connectedComponentIn N.central_sphereᶜ N'.center := by
  apply N.mem_component_complement_of_negative_half_overlap_of_distance N'
    hε heq hscale _ hx hx' haxis
  apply (ENNReal.ofReal_le_ofReal ?_).trans
    (N.balanced_edist_lower_of_not_mem_carrier hε hcenter)
  have hi := inv_pos.mpr N.epsilon_pos
  nlinarith [mul_pos N.scale_pos hi]

/-- A point approached through the positive outer quarter is in the same
component of the sphere complement as the entire positive half. -/
theorem positive_half_subset_component_complement_of_mem_closure_positive_quarter
    (N : EpsilonNeck g) {p : M}
    (hp : p ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) :
    N.region 0 N.epsilon⁻¹ ⊆ connectedComponentIn N.central_sphereᶜ p := by
  have hi := inv_pos.mpr N.epsilon_pos
  have hquarter := N.isConnected_region (a := N.epsilon⁻¹ / 2)
    (b := N.epsilon⁻¹) (by linarith) le_rfl (by linarith)
  have hpositive := N.isConnected_region (a := 0) (b := N.epsilon⁻¹)
    (by linarith) le_rfl hi
  have hquarter_avoid : closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ⊆
      N.central_sphereᶜ := by
    have hsub : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
        (N.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2))ᶜ := by
      intro y hy hz
      exact lt_asymm hy.2.1 hz.2.2
    have hclosure := closure_minimal hsub
      (N.isOpen_region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2)).isClosed_compl
    intro y hy hsphere
    have hs := (N.mem_central_sphere_iff y).mp hsphere
    exact hclosure hy ⟨hs.1, by rw [hs.2]; linarith, by rw [hs.2]; positivity⟩
  have hpositive_avoid : N.region 0 N.epsilon⁻¹ ⊆ N.central_sphereᶜ := by
    intro y hy hsphere
    have hs := (N.mem_central_sphere_iff y).mp hsphere
    linarith [hy.2.1, hs.2]
  obtain ⟨q, hq⟩ := hquarter.nonempty
  have hqpositive : q ∈ N.region 0 N.epsilon⁻¹ :=
    ⟨hq.1, by linarith [hq.2.1], hq.2.2⟩
  have hconnected := hpositive.isPreconnected.union q hqpositive
    (subset_closure hq) hquarter.isPreconnected.closure
  have hsub := hconnected.subset_connectedComponentIn (Or.inr hp)
    (union_subset hpositive_avoid hquarter_avoid)
  exact subset_union_left.trans hsub

/-- A sufficiently distant neck on the positive side of a separating neck
cannot reach its negative half, even if its center lies inside the old carrier. -/
theorem overlap_subset_positive_three_quarters_of_distance
    (N N' : EpsilonNeck g) (hN : N.IsSeparating)
    (hε : N.epsilon ≤ 1 / 1000) (heq : N'.epsilon = N.epsilon)
    (hscale : N'.scale ≤ (1.01 : ℝ) * N.scale)
    (hdistance : ENNReal.ofReal ((0.98 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.edist N.center N'.center)
    (hpositive : N.region 0 N.epsilon⁻¹ ⊆
      connectedComponentIn N.central_sphereᶜ N'.center) :
    N.carrier ∩ N'.carrier ⊆ N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
  intro x hx
  refine ⟨hx.1, ?_, (N.coordinate_inverse_mem x hx.1).2.2⟩
  by_contra hn
  have haxis := le_of_not_gt hn
  let U := connectedComponentIn N.central_sphereᶜ N'.center
  have hxU : x ∈ U := N.mem_component_complement_of_negative_half_overlap_of_distance N'
    hε heq hscale hdistance hx.1 hx.2 haxis
  have hU : IsPreconnected U := isPreconnected_connectedComponentIn
  have hcomponent : U ⊆ connectedComponent N.center := by
    rw [connectedComponent_eq (N.carrier_subset_connectedComponent hx.1)]
    exact hU.subset_connectedComponent hxU
  have havoid : Disjoint U N.central_sphere := by
    apply disjoint_left.mpr
    intro y hy hsphere
    exact connectedComponentIn_subset N.central_sphereᶜ N'.center hy hsphere
  have hi := inv_pos.mpr N.epsilon_pos
  obtain ⟨y, hy⟩ := (N.isConnected_region (a := 0) (b := N.epsilon⁻¹)
    (by linarith) le_rfl hi).nonempty
  apply N.not_meets_both_halves_of_isSeparating hN hU hcomponent havoid
  exact ⟨⟨x, hxU, hx.1, (N.coordinate_inverse_mem x hx.1).2.1, by linarith⟩,
    ⟨y, hpositive hy, hy⟩⟩

/-- A neck centered at the positive frontier of a separating neck cannot
reach the old negative half. Its overlap is contained in the old positive
three quarters, including the strict lower height bound. -/
theorem overlap_subset_positive_three_quarters_of_frontier
    (N N' : EpsilonNeck g) (hN : N.IsSeparating)
    (hε : N.epsilon ≤ 1 / 1000) (heq : N'.epsilon = N.epsilon)
    (hscale : N'.scale ≤ (1.01 : ℝ) * N.scale)
    (hcenter : N'.center ∉ N.carrier)
    (hpos : N'.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) :
    N.carrier ∩ N'.carrier ⊆ N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
  apply N.overlap_subset_positive_three_quarters_of_distance N' hN hε heq hscale _
    (N.positive_half_subset_component_complement_of_mem_closure_positive_quarter hpos)
  apply (ENNReal.ofReal_le_ofReal ?_).trans
    (N.balanced_edist_lower_of_not_mem_carrier hε hcenter)
  have hi := inv_pos.mpr N.epsilon_pos
  nlinarith [mul_pos N.scale_pos hi]

/-- The old three-quarter containment holds uniformly for equal-parameter
frontier necks, with the scale bound supplied by the ambient scalar estimate. -/
theorem exists_frontier_overlap_subset_positive_three_quarters_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g), N.IsSeparating →
      N.epsilon ≤ ε₀ → N'.epsilon = N.epsilon → N'.center ∉ N.carrier →
      N'.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
      N.carrier ∩ N'.carrier ⊆ N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
  obtain ⟨ε₁, hε₁, _, hscale⟩ := exists_scale_comparison_on_closure.{u}
  refine ⟨min ε₁ (1 / 1000), lt_min hε₁ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hε heq hcenter hpos
  exact N.overlap_subset_positive_three_quarters_of_frontier N' hN
    (hε.trans (min_le_right _ _)) heq
    (hscale N N' (hε.trans (min_le_left _ _))
      (closure_mono (N.region_subset_carrier _ _) hpos)).2 hcenter hpos

end PoincareMT.EpsilonNeck
