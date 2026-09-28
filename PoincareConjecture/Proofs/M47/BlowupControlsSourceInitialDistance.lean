import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBuffer










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M47



theorem standard_tip_distance_lower_of_ball_disjoint
    (g : RiemannianMetric 3 StandardCapSpace) {U : Set StandardCapSpace}
    {x : StandardCapSpace} {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hball : g.ball x r ⊆ U)
    (hdisjoint : Disjoint U {y | g.edist 0 y ≤ ENNReal.ofReal a}) :
    ENNReal.ofReal (a + r) ≤ g.edist 0 x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hxU : x ∈ U := hball (by
    change g.edist x x < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr)
  have hfar : ENNReal.ofReal a < g.edist 0 x := by
    apply lt_of_not_ge
    exact fun h => Set.disjoint_left.mp hdisjoint hxU h
  by_contra hnot
  have hxshort : g.edist x 0 < ENNReal.ofReal (a + r) := by
    have hsymm : g.edist x 0 = g.edist 0 x := Manifold.riemannianEDist_comm
    rw [hsymm]
    exact lt_of_not_ge hnot
  obtain ⟨p, hp0, hp1, hp, hlength, _⟩ := g.exists_short_path_in_ball x 0 hxshort
  have hcont : ContinuousOn (fun s => g.edist 0 (p s)) (Icc (0 : ℝ) 1) :=
    (M36.metric_edist_continuous g).comp_continuousOn
      (continuousOn_const.prodMk hp.continuousOn)
  have hlevelmem : ENNReal.ofReal a ∈
      Icc (g.edist 0 (p 1)) (g.edist 0 (p 0)) := by
    rw [hp0, hp1, M36.metric_edist_self]
    exact ⟨bot_le, hfar.le⟩
  obtain ⟨s, hs, hlevel⟩ := intermediate_value_Icc' zero_le_one hcont hlevelmem
  change g.edist 0 (p s) = ENNReal.ofReal a at hlevel
  have hyout : p s ∉ U := fun h => Set.disjoint_left.mp hdisjoint h hlevel.le
  have hxy : ENNReal.ofReal r ≤ g.edist x (p s) := by
    apply le_of_not_gt
    exact fun h => hyout (hball h)
  have hprefix : ENNReal.ofReal r ≤ g.pathELength p 0 s := by
    have h := M36.metric_edist_le_pathELength g hs.1
      (hp.mono (Icc_subset_Icc_right hs.2))
    rw [hp0] at h
    exact hxy.trans h
  have hsuffix : ENNReal.ofReal a ≤ g.pathELength p s 1 := by
    have h := M36.metric_edist_le_pathELength g hs.2
      (hp.mono (Icc_subset_Icc_left hs.1))
    rw [hp1] at h
    have hsymm : g.edist (p s) 0 = g.edist 0 (p s) := Manifold.riemannianEDist_comm
    rwa [hsymm, hlevel] at h
  have htotal : ENNReal.ofReal (a + r) ≤ g.pathELength p 0 1 := by
    rw [ENNReal.ofReal_add ha.le hr.le, add_comm]
    exact (add_le_add hprefix hsuffix).trans_eq (M36.metric_pathELength_add g p hs.1 hs.2)
  exact not_lt_of_ge htotal hlength



theorem standard_initial_neck_tip_distance_lower
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z
      (Icc (-v * (G.connection v).scalarCurvature z) 0))
    (hsmall : gamma ≤ 1 / 1200)
    (hdisjoint : Disjoint N.patch.carrier
      {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
    (hshort : v * (G.connection v).scalarCurvature z < 1 + gamma)
    {x : StandardCapSpace} (hx : x ∈ N.patch.carrier)
    (hheight : |(N.patch.inverse x).2| ≤ gamma⁻¹ / 3 + 1) :
    ENNReal.ofReal (g0.cylindrical_end.radius + 104) ≤ g0.metric.edist 0 x := by
  have h := standard_tip_distance_lower_of_ball_disjoint g0.metric
    (by norm_num : (0 : ℝ) < 100)
    (by linarith [g0.cylindrical_end.radius_pos] : 0 < g0.cylindrical_end.radius + 4)
    (standard_initial_neck_ball_subset N hsmall hdisjoint hshort hx hheight) hdisjoint
  simpa only [show g0.cylindrical_end.radius + 4 + 100 =
    g0.cylindrical_end.radius + 104 by ring] using h

end PoincareConjecture.M47
