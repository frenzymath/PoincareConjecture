import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalSphereContact
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFrontierQuarter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceUpper
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem edist_center_lower_of_not_mem_coordinate_slab_m28 (N : EpsilonNeck g)
    {r : ℝ} (hr : r ∈ Ioo 0 N.epsilon⁻¹) {x : M}
    (hx : x ∉ N.coordinate_map '' (univ ×ˢ Icc (-r) r)) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) ≤
      g.edist N.center x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_contra h
  have hdist : Manifold.riemannianEDist (𝓡 3) N.center x <
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) := lt_of_not_ge h
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hdist
      (show (0 : ℝ) < 1 by norm_num)
  have hcenter := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
  have hstart : γ 0 ∈ N.region (-r) r := by
    rw [hγ0]
    exact ⟨hcenter.1, hcenter.2 ▸ neg_lt_zero.mpr hr.1, hcenter.2 ▸ hr.1⟩
  obtain ⟨t, ht, hcarrier, hboundary, -⟩ := N.exists_initial_segment_to_slab_boundary
    (show (0 : ℝ) ≤ 1 by norm_num) (neg_lt_neg hr.2) hr.2
    hγ.continuous.continuousOn hstart (hγ1 ▸ hx)
  have hax := N.axial_displacement_le_pathELength ht.1.le hγ hcarrier
  have hvalue : |(N.coordinate_inverse (γ t)).2 -
      (N.coordinate_inverse (γ 0)).2| = r := by
    rw [hγ0, hcenter.2, sub_zero]
    rcases hboundary with hneg | hpos
    · rw [hneg, abs_neg, abs_of_pos hr.1]
    · rw [hpos, abs_of_pos hr.1]
  rw [hvalue] at hax
  have hmono : g.pathELength γ 0 t ≤ g.pathELength γ 0 1 :=
    Manifold.pathELength_mono le_rfl ht.2
  exact (not_lt_of_ge (hax.trans hmono)) hlength

theorem pathELength_lower_of_cross_central_sphere_m28 (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 γ)
    (hstart : γ 0 ∉ N.carrier) (_hend : γ 1 ∈ N.carrier)
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
      (N.edist_center_lower_of_not_mem_coordinate_slab_m28
        (r := (0.49 : ℝ) * N.epsilon⁻¹) ⟨by positivity, by linarith⟩ houtside)
    nlinarith [mul_le_mul_of_nonneg_right hroot (mul_nonneg hs.le hi.le)]
  have hdiam := N.edist_central_sphere_le_two_pi_mul_scale
    N.center_on_central_sphere hcross
  have hleft : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      ENNReal.ofReal ((2 * Real.pi) * N.scale) + g.pathELength γ 0 t := by
    apply (N.balanced_edist_lower_of_not_mem_carrier hε hstart).trans
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

theorem mem_component_complement_of_negative_half_overlap_m28
    (N N' : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (heq : N'.epsilon = N.epsilon)
    (hscale : N'.scale ≤ (1.01 : ℝ) * N.scale)
    (hcenter : N'.center ∉ N.carrier) {x : M}
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
    have hlower := N.pathELength_lower_of_cross_central_sphere_m28 hε hγ
      (hγ0 ▸ hcenter) (hγ1 ▸ hx) (hγ1 ▸ haxis) ht hcross
    exact not_lt_of_ge hlower hlength
  have hconnected : IsPreconnected (γ '' Icc 0 1) :=
    isPreconnected_Icc.image γ hγ.continuous.continuousOn
  exact hconnected.subset_connectedComponentIn
    ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩ havoid
    ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩

theorem positive_half_subset_component_complement_of_mem_closure_positive_quarter_m28
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

theorem overlap_subset_positive_three_quarters_of_frontier_m28
    (N N' : EpsilonNeck g) (hN : N.IsSeparating)
    (hε : N.epsilon ≤ 1 / 1000) (heq : N'.epsilon = N.epsilon)
    (hscale : N'.scale ≤ (1.01 : ℝ) * N.scale)
    (hcenter : N'.center ∉ N.carrier)
    (hpos : N'.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) :
    N.carrier ∩ N'.carrier ⊆ N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
  intro x hx
  refine ⟨hx.1, ?_, (N.coordinate_inverse_mem x hx.1).2.2⟩
  by_contra hn
  have haxis := le_of_not_gt hn
  let U := connectedComponentIn N.central_sphereᶜ N'.center
  have hxU := N.mem_component_complement_of_negative_half_overlap_m28 N'
    hε heq hscale hcenter hx.1 hx.2 haxis
  have hU : IsPreconnected U := isPreconnected_connectedComponentIn
  have hcomponent : U ⊆ connectedComponent N.center := by
    rw [connectedComponent_eq (N.carrier_subset_connectedComponent hx.1)]
    exact hU.subset_connectedComponent hxU
  have havoid : Disjoint U N.central_sphere := by
    apply disjoint_left.mpr
    intro y hy hsphere
    exact connectedComponentIn_subset N.central_sphereᶜ N'.center hy hsphere
  have hpositive :=
    N.positive_half_subset_component_complement_of_mem_closure_positive_quarter_m28 hpos
  have hi := inv_pos.mpr N.epsilon_pos
  obtain ⟨y, hy⟩ := (N.isConnected_region (a := 0) (b := N.epsilon⁻¹)
    (by linarith) le_rfl hi).nonempty
  apply N.not_meets_both_halves_of_isSeparating hN hU hcomponent havoid
  exact ⟨⟨x, hxU, hx.1, (N.coordinate_inverse_mem x hx.1).2.1, by linarith⟩,
    ⟨y, hpositive hy, hy⟩⟩

private theorem edist_center_le_axis_bound (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) :
    g.edist N.center x ≤ ENNReal.ofReal
      ((2 * Real.pi + Real.sqrt (1 + N.epsilon) * |(N.coordinate_inverse x).2|) * N.scale) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := N.scale_pos
  let z := N.coordinate_inverse x
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := (N.coordinate_inverse_mem x hx).2
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hcoord : N.coordinate_map z = x := by
    have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
    rwa [N.coordinate_map_eq] at h
  have hcentral : N.coordinate_map (z.1, 0) ∈ N.central_sphere := by
    rw [N.central_sphere_eq]
    exact ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have haxial := N.edist_coordinate_map_axis_le z.1 hzero hz
  simp only [sub_zero] at haxial
  rw [Prod.eta z, hcoord] at haxial
  calc
    g.edist N.center x ≤ g.edist N.center (N.coordinate_map (z.1, 0)) +
        g.edist (N.coordinate_map (z.1, 0)) x := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal ((2 * Real.pi) * N.scale) +
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * |z.2|) :=
      add_le_add (N.edist_central_sphere_le_two_pi_mul_scale
        N.center_on_central_sphere hcentral) haxial
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp [z]
      ring

private theorem edist_center_le_inner_region (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {x : M}
    (hx : x ∈ N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹)) :
    g.edist N.center x ≤ ENNReal.ofReal ((0.7 : ℝ) * N.scale * N.epsilon⁻¹) := by
  apply (edist_center_le_axis_bound N hx.1).trans
  apply ENNReal.ofReal_le_ofReal
  have hi := inv_pos.mpr N.epsilon_pos
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hi.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hroot : Real.sqrt (1 + N.epsilon) ≤ (1.001 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have habs : |(N.coordinate_inverse x).2| ≤ (0.6 : ℝ) * N.epsilon⁻¹ :=
    abs_le.mpr ⟨by linarith [hx.2.1], hx.2.2.le⟩
  have hmul := mul_le_mul hroot habs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1.001)
  have hbound : 2 * Real.pi + Real.sqrt (1 + N.epsilon) * |(N.coordinate_inverse x).2| ≤
      (0.7 : ℝ) * N.epsilon⁻¹ := by nlinarith [Real.pi_le_four]
  nlinarith [mul_le_mul_of_nonneg_right hbound N.scale_pos.le]

theorem inner_region_disjoint_successor_central_sphere_m28
    (N Q : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (hscale : Q.scale ≤ (1.01 : ℝ) * N.scale) (hout : Q.center ∉ N.carrier) :
    Disjoint (N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹))
      Q.central_sphere := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply disjoint_left.mpr
  intro x hx hxQ
  have hs := N.scale_pos
  have hQ := Q.scale_pos
  have hi := inv_pos.mpr N.epsilon_pos
  have hbound := (N.balanced_edist_lower_of_not_mem_carrier hε hout).trans
    (Manifold.riemannianEDist_triangle.trans (add_le_add
      (edist_center_le_inner_region N hε hx)
      (Q.edist_central_sphere_le_two_pi_mul_scale hxQ Q.center_on_central_sphere)))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hbound
  have hnum := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hi.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hdiam : (2 * Real.pi) * Q.scale ≤ (8.08 : ℝ) * N.scale := by
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four Q.scale_pos.le]
  nlinarith [mul_le_mul_of_nonneg_left hinv N.scale_pos.le, N.scale_pos]

theorem pathELength_lower_of_cross_successor_central_sphere_m28
    (N Q : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (heq : Q.epsilon = N.epsilon)
    (hscalelo : (0.99 : ℝ) * N.scale ≤ Q.scale)
    (hscalehi : Q.scale ≤ (1.01 : ℝ) * N.scale)
    (hout : Q.center ∉ N.carrier) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 γ) (hstart : γ 0 = N.center)
    (haxis : Q.epsilon⁻¹ / 2 ≤ (Q.coordinate_inverse (γ 1)).2)
    {t : ℝ} (ht : t ∈ Icc 0 1) (hcross : γ t ∈ Q.central_sphere) :
    ENNReal.ofReal ((1.4 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := N.scale_pos
  have hQs := Q.scale_pos
  have hi := inv_pos.mpr N.epsilon_pos
  have hQi := inv_pos.mpr Q.epsilon_pos
  have hQε : Q.epsilon ≤ 1 / 1000 := by simpa only [heq] using hε
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hi.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hroot : (0.99 : ℝ) ≤ Real.sqrt (1 - Q.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - Q.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - Q.epsilon)]
  have houtside : γ 1 ∉ Q.coordinate_map ''
      (univ ×ˢ Icc (-((0.49 : ℝ) * Q.epsilon⁻¹)) ((0.49 : ℝ) * Q.epsilon⁻¹)) := by
    intro hx
    have h := (Q.mem_coordinate_slab_iff (by linarith) (by linarith)).mp hx
    linarith [h.2.2]
  have henddist : ENNReal.ofReal ((0.48 : ℝ) * Q.scale * Q.epsilon⁻¹) ≤
      g.edist Q.center (γ 1) := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_)
      (Q.edist_center_lower_of_not_mem_coordinate_slab_m28
        (r := (0.49 : ℝ) * Q.epsilon⁻¹) ⟨by positivity, by linarith⟩ houtside)
    nlinarith [mul_le_mul_of_nonneg_right hroot (mul_nonneg hQs.le hQi.le)]
  have hdiam := Q.edist_central_sphere_le_two_pi_mul_scale
    Q.center_on_central_sphere hcross
  have hstartdist : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.edist Q.center (γ 0) := by
    rw [hstart, show g.edist Q.center N.center = g.edist N.center Q.center from
      Manifold.riemannianEDist_comm]
    exact N.balanced_edist_lower_of_not_mem_carrier hε hout
  have hleft : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      ENNReal.ofReal ((2 * Real.pi) * Q.scale) + g.pathELength γ 0 t := by
    apply hstartdist.trans
    calc
      _ ≤ g.edist Q.center (γ t) + g.edist (γ t) (γ 0) :=
        Manifold.riemannianEDist_triangle
      _ = g.edist Q.center (γ t) + g.edist (γ 0) (γ t) := by
        rw [show g.edist (γ t) (γ 0) = g.edist (γ 0) (γ t) from
          Manifold.riemannianEDist_comm]
      _ ≤ _ := add_le_add hdiam
        (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn rfl rfl ht.1)
  have hright : ENNReal.ofReal ((0.48 : ℝ) * Q.scale * Q.epsilon⁻¹) ≤
      ENNReal.ofReal ((2 * Real.pi) * Q.scale) + g.pathELength γ t 1 :=
    henddist.trans (Manifold.riemannianEDist_triangle.trans (add_le_add hdiam
      (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn rfl rfl ht.2)))
  have hsum := add_le_add hleft hright
  have hadd : g.pathELength γ 0 t + g.pathELength γ t 1 = g.pathELength γ 0 1 :=
    Manifold.pathELength_add ht.1 ht.2
  rw [add_add_add_comm, hadd] at hsum
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), heq] at hsum
  by_contra hnot
  have hshort := lt_of_not_ge hnot
  have hlt := ENNReal.add_lt_add_left
    (ENNReal.ofReal_ne_top (r := (2 * Real.pi) * Q.scale + (2 * Real.pi) * Q.scale))
    hshort
  have hstrict := hsum.trans_lt hlt
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hstrict
  have hnum := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hstrict
  have hpi : (2 * Real.pi) * Q.scale ≤ (8.08 : ℝ) * N.scale := by
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four hQs.le]
  have hscaled := mul_le_mul_of_nonneg_right hscalelo hi.le
  have hlen := mul_le_mul_of_nonneg_left hinv hs.le
  nlinarith

theorem mem_component_complement_of_successor_positive_half_overlap_m28
    (N Q : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (heq : Q.epsilon = N.epsilon)
    (hscalelo : (0.99 : ℝ) * N.scale ≤ Q.scale)
    (hscalehi : Q.scale ≤ (1.01 : ℝ) * N.scale)
    (hout : Q.center ∉ N.carrier) {x : M}
    (hx : x ∈ N.carrier) (haxis : Q.epsilon⁻¹ / 2 ≤ (Q.coordinate_inverse x).2) :
    x ∈ connectedComponentIn Q.central_sphereᶜ N.center := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := N.scale_pos
  have hi := inv_pos.mpr N.epsilon_pos
  have hupper := N.edist_center_le_balanced_upper_of_mem_closure hε (subset_closure hx)
  have hstrict : g.edist N.center x <
      ENNReal.ofReal ((1.4 : ℝ) * N.scale * N.epsilon⁻¹) := by
    apply hupper.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [mul_pos hs hi]
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hstrict
      (show (0 : ℝ) < 1 by norm_num)
  have havoid : γ '' Icc 0 1 ⊆ Q.central_sphereᶜ := by
    rintro y ⟨t, ht, rfl⟩ hcross
    have hlower := N.pathELength_lower_of_cross_successor_central_sphere_m28 Q hε
      heq hscalelo hscalehi hout hγ hγ0 (hγ1 ▸ haxis) ht hcross
    exact not_lt_of_ge hlower hlength
  have hconnected : IsPreconnected (γ '' Icc 0 1) :=
    isPreconnected_Icc.image γ hγ.continuous.continuousOn
  exact hconnected.subset_connectedComponentIn
    ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩ havoid
    ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩

theorem overlap_subset_successor_three_quarters_m28
    (N Q : EpsilonNeck g) (hQ : Q.IsSeparating)
    (hε : N.epsilon ≤ 1 / 1000) (heq : Q.epsilon = N.epsilon)
    (hscalelo : (0.99 : ℝ) * N.scale ≤ Q.scale)
    (hscalehi : Q.scale ≤ (1.01 : ℝ) * N.scale)
    (hout : Q.center ∉ N.carrier)
    (hnegative : Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
      N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹)) :
    N.carrier ∩ Q.carrier ⊆ Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2) := by
  have hi := inv_pos.mpr N.epsilon_pos
  have hmiddle := N.isConnected_region
    (a := -(0.2 : ℝ) * N.epsilon⁻¹) (b := (0.6 : ℝ) * N.epsilon⁻¹)
    (by linarith) (by linarith) (by linarith)
  have hcenter : N.center ∈ N.region
      (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹) := by
    have hc := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
    exact ⟨hc.1, by rw [hc.2]; linarith, by rw [hc.2]; linarith⟩
  have hmiddleavoid := N.inner_region_disjoint_successor_central_sphere_m28 Q hε hscalehi hout
  have hmiddlecomponent := hmiddle.isPreconnected.subset_connectedComponentIn
    hcenter hmiddleavoid.subset_compl_right
  obtain ⟨y, hy⟩ := (Q.isConnected_region
    (a := -N.epsilon⁻¹) (b := -N.epsilon⁻¹ / 2)
    (by rw [heq]) (by rw [heq]; linarith) (by linarith)).nonempty
  intro x hx
  refine ⟨hx.2, by simpa only [heq] using (Q.coordinate_inverse_mem x hx.2).2.1, ?_⟩
  by_contra hn
  have haxis : Q.epsilon⁻¹ / 2 ≤ (Q.coordinate_inverse x).2 := by
    rw [heq]
    exact le_of_not_gt hn
  let U := connectedComponentIn Q.central_sphereᶜ N.center
  have hxU : x ∈ U := N.mem_component_complement_of_successor_positive_half_overlap_m28 Q
    hε heq hscalelo hscalehi hout hx.1 haxis
  have hU : IsPreconnected U := isPreconnected_connectedComponentIn
  have hcomponent : U ⊆ connectedComponent Q.center := by
    rw [connectedComponent_eq (Q.carrier_subset_connectedComponent hx.2)]
    exact hU.subset_connectedComponent hxU
  have havoid : Disjoint U Q.central_sphere := by
    apply disjoint_left.mpr
    intro z hz hsphere
    exact connectedComponentIn_subset Q.central_sphereᶜ N.center hz hsphere
  apply Q.not_meets_both_halves_of_isSeparating hQ hU hcomponent havoid
  refine ⟨⟨y, hmiddlecomponent (hnegative hy), hy.1, ?_, ?_⟩,
    ⟨x, hxU, hx.2, ?_, (Q.coordinate_inverse_mem x hx.2).2.2⟩⟩
  · simpa only [heq] using hy.2.1
  · linarith [hy.2.2]
  · rw [heq] at haxis
    linarith



theorem exists_frontier_reversal_balanced_overlap_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ (N P : EpsilonNeck g), N.IsSeparating → N.epsilon ≤ ε₀ →
        P.epsilon = N.epsilon →
        P.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        P.center ∉ N.carrier →
        ∃ Q : EpsilonNeck g, Q.SameUpToReversal P ∧
          N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ Q.carrier ∧
          Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆ N.carrier ∧
          N.carrier ∩ Q.carrier ⊆
            N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
              Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2) ∧
          Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
            N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹) ∧
          Q.IsSeparating := by
  obtain ⟨ε₁, hε₁, _, hquarters⟩ := exists_frontier_reversal_quarter_overlap_m28.{u}
  obtain ⟨ε₂, hε₂, _, hscale⟩ := exists_scale_comparison_at_common_closure_m28.{u}
  refine ⟨min ε₁ (min ε₂ (1 / 1000)),
    lt_min hε₁ (lt_min hε₂ (by norm_num)),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro M _ _ _ _ _ _ _ g N P hN hε heq hfront hout
  obtain ⟨Q, hQ, hpositive, hnegative, hsep, _⟩ :=
    hquarters N P (hε.trans (min_le_left _ _)) heq hfront hout
  have hsame : Q.SameUpToReversal P := by
    rcases hQ with rfl | rfl
    · exact SameUpToReversal.refl _
    · exact P.reversed_sameUpToReversal
  have hQε : Q.epsilon = N.epsilon := hsame.epsilon_eq.trans heq
  have hQfront : Q.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) := by
    rwa [hsame.center_eq]
  have hQout : Q.center ∉ N.carrier := by rwa [hsame.center_eq]
  have hNsmall : N.epsilon ≤ ε₂ :=
    hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hQsmall : Q.epsilon ≤ ε₂ := by
    rw [hQε]
    exact hNsmall
  have hcommon : (closure N.carrier ∩ closure Q.carrier).Nonempty := by
    refine ⟨Q.center, ?_, ?_⟩
    · exact closure_mono (N.region_subset_carrier _ _) hQfront
    · exact subset_closure (Q.central_sphere_subset_carrier Q.center_on_central_sphere)
  have hscales := hscale N Q
    (hε.trans ((min_le_right _ _).trans (min_le_left _ _))) hQsmall hcommon
  have hsmall : N.epsilon ≤ 1 / 1000 :=
    hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hold := N.overlap_subset_positive_three_quarters_of_frontier_m28 Q hN hsmall hQε
    hscales.2 hQout hQfront
  have hnew := N.overlap_subset_successor_three_quarters_m28 Q (hsep.mpr hN) hsmall hQε
    hscales.1 hscales.2 hQout hnegative
  exact ⟨Q, hsame, hpositive, fun _ hx => (hnegative hx).1,
    fun _ hx => ⟨hold hx, hnew hx⟩, hnegative, hsep.mpr hN⟩

end PoincareConjecture.EpsilonNeck
