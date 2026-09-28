import PoincareConjecture.Proofs.M74.Cor15_4.SchoenfliesGlobalChart










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

open M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

private theorem radial_annulus_isConnected {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    IsConnected {x : StandardCapSpace | r < ‖x‖ ∧ ‖x‖ < R} := by
  have himage : (fun p : RoundCylinderSpace => p.2 • p.1.1) '' (univ ×ˢ Ioo r R) =
      {x : StandardCapSpace | r < ‖x‖ ∧ ‖x‖ < R} := by
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have hn : ‖t • q.1‖ = t := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_trans hr ht.1),
          mem_sphere_zero_iff_norm.mp q.2, mul_one]
      simpa only [mem_ofPred_eq, hn, mem_Ioo] using ht
    · intro hx
      have hn : 0 < ‖x‖ := lt_trans hr hx.1
      let q : UnitTwoSphere := ⟨‖x‖⁻¹ • x, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ (ne_of_gt hn)]⟩
      refine ⟨(q, ‖x‖), ⟨mem_univ _, hx⟩, ?_⟩
      change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]
  rw [← himage]
  have hc := (SurgeryCoordinates.cylinder_interval_simplyConnected r R hrR).isPathConnected
  exact hc.isConnected.image _ (continuous_snd.smul
    (continuous_subtype_val.comp continuous_fst)).continuousOn



theorem shiftedSchoenflies_original_sphere_image
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) :
    D.chart '' sphere (0 : StandardCapSpace) (D.radial (1 / 2)) =
      B.punctureCollar d '' (univ ×ˢ {0}) := by
  have hr : 0 < D.radial (1 / 2) := D.radial_pos _ (by norm_num)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let q : UnitTwoSphere := ⟨(D.radial (1 / 2))⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr), mem_sphere_zero_iff_norm.mp hx,
        inv_mul_cancel₀ (ne_of_gt hr)]⟩
    refine ⟨(D.boundary_map.symm q, 0), ⟨mem_univ _, mem_singleton 0⟩, ?_⟩
    rw [← B.shiftedSchoenflies_original_boundary d D, D.boundary_map.apply_symm_apply]
    change D.chart (D.radial (1 / 2) • ((D.radial (1 / 2))⁻¹ • x)) = D.chart x
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    subst s
    refine ⟨D.radial (1 / 2) • (D.boundary_map q).1, ?_,
      B.shiftedSchoenflies_original_boundary d D q⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      mem_sphere_zero_iff_norm.mp (D.boundary_map q).2, mul_one]

private theorem chart_ball_annulus_union (c : StandardCapSpace → StandardCapSpace)
    {r R : ℝ} (hrR : r < R) (hinj : InjOn c (ball 0 R))
    (himage : c '' ball 0 R = univ) :
    c '' ball 0 r ∪ c '' {x | r < ‖x‖ ∧ ‖x‖ < R} = (c '' sphere 0 r)ᶜ := by
  ext y
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) ⟨z, hz, hzx⟩
    · have hzR : z ∈ ball (0 : StandardCapSpace) R := by
        rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz]
        exact hrR
      have hzx' := hinj hzR (ball_subset_ball hrR.le hx) hzx
      subst z
      exact (not_lt_of_ge (mem_sphere_zero_iff_norm.mp hz).ge) (mem_ball_zero_iff.mp hx)
    · have hzR : z ∈ ball (0 : StandardCapSpace) R := by
        rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz]
        exact hrR
      have hzx' := hinj hzR (mem_ball_zero_iff.mpr hx.2) hzx
      subst z
      exact (not_lt_of_ge (mem_sphere_zero_iff_norm.mp hz).le) hx.1
  · intro hy
    obtain ⟨x, hx, rfl⟩ : y ∈ c '' ball 0 R := by rw [himage]; trivial
    have hne : ‖x‖ ≠ r := by
      intro h
      exact hy (mem_image_of_mem _ (mem_sphere_zero_iff_norm.mpr h))
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (mem_image_of_mem _ (mem_ball_zero_iff.mpr h))
    · exact Or.inr (mem_image_of_mem _ ⟨h, mem_ball_zero_iff.mp hx⟩)




theorem shiftedSchoenflies_original_ball_image
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) :
    D.chart '' ball (0 : StandardCapSpace) (D.radial (1 / 2)) =
      B.punctureChart d '' B.closedBallᶜ := by
  let r := D.radial (1 / 2)
  have hr : 0 < r := D.radial_pos _ (by norm_num)
  have hrR : r < D.radius := D.radial_lt _ (by norm_num)
  let W := D.chart '' ball (0 : StandardCapSpace) r
  let Z := D.chart '' {x : StandardCapSpace | r < ‖x‖ ∧ ‖x‖ < D.radius}
  let U := B.punctureChart d '' ((B.map '' ball (0 : StandardCapSpace) 1) \ {B.map 0})
  let V := B.punctureChart d '' B.closedBallᶜ
  let S := B.punctureCollar d '' (univ ×ˢ {0})
  have hcover : W ∪ Z = Sᶜ := by
    rw [show S = D.chart '' sphere (0 : StandardCapSpace) r from
      (B.shiftedSchoenflies_original_sphere_image d D).symm]
    exact chart_ball_annulus_union D.chart hrR D.chart_injOn
      (B.shiftedSchoenflies_chart_image_univ d D)
  have hUVcover : U ∪ V = Sᶜ := B.punctureChart_interior_union_exterior d
  have hU : IsOpen U := B.punctureChart_image_puncturedBall_isOpen d (by norm_num)
  have hV : IsOpen V := B.punctureChart_image_closedBall_compl_isOpen d
  have hUV : Disjoint U V := B.punctureChart_interior_disjoint_exterior d
  have hWbounded : Bornology.IsBounded W :=
    ((isCompact_closedBall (0 : StandardCapSpace) r).image_of_continuousOn
      (D.chart_smooth.continuousOn.mono (closedBall_subset_ball hrR))).isBounded.subset
        (image_mono ball_subset_closedBall)
  have hWconnected : IsConnected W :=
    (show IsConnected (ball (0 : StandardCapSpace) r) from
      ⟨nonempty_ball.mpr hr, (convex_ball (0 : StandardCapSpace) r).isPreconnected⟩).image _
        (D.chart_smooth.continuousOn.mono (ball_subset_ball hrR.le))
  have hZconnected : IsConnected Z :=
    (radial_annulus_isConnected hr hrR).image _
      (D.chart_smooth.continuousOn.mono (fun _ hx => mem_ball_zero_iff.mpr hx.2))
  have hUnbounded : ¬Bornology.IsBounded U :=
    B.punctureChart_image_puncturedBall_unbounded d (by norm_num) (by norm_num)
  obtain ⟨u, huU, huW⟩ : ∃ u, u ∈ U ∧ u ∉ W := by
    by_contra h
    apply hUnbounded
    apply hWbounded.subset
    intro x hx
    by_contra hxW
    exact h ⟨x, hx, hxW⟩
  have huZ : u ∈ Z := by
    have hu : u ∈ W ∪ Z := by rw [hcover, ← hUVcover]; exact Or.inl huU
    exact hu.resolve_left huW
  have hZU : Z ⊆ U := hZconnected.isPreconnected.subset_left_of_subset_union hU hV hUV
    (fun x hx => by rw [hUVcover, ← hcover]; exact Or.inr hx) ⟨u, huZ, huU⟩
  have hVW : V ⊆ W := by
    intro x hx
    have hxWZ : x ∈ W ∪ Z := by rw [hcover, ← hUVcover]; exact Or.inr hx
    rcases hxWZ with hxW | hxZ
    · exact hxW
    · exact False.elim (Set.disjoint_left.mp hUV (hZU hxZ) hx)
  obtain ⟨v, hv⟩ := B.punctureChart_image_closedBall_compl_nonempty d
  have hWV : W ⊆ V := hWconnected.isPreconnected.subset_right_of_subset_union hU hV hUV
    (fun x hx => by rw [hUVcover, ← hcover]; exact Or.inl hx) ⟨v, hVW hv, hv⟩
  exact subset_antisymm hWV hVW

end PoincareConjecture.SurgeryBallEmbedding
