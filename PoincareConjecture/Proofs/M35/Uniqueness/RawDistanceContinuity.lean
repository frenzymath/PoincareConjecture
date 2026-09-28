import PoincareConjecture.Proofs.M35.Uniqueness.RawDistanceBarrier
import PoincareConjecture.Proofs.M04.ShiCappedDistance
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.Uniqueness



theorem continuousOn_raw_distance
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (p : StandardCapSpace) :
    ContinuousOn (fun z : ℝ × StandardCapSpace =>
      ((G.flow.metric z.1).edist p z.2).toReal) (Icc 0 T ×ˢ univ) := by
  obtain ⟨K, hK, hbound⟩ := G.curvature_locally_bounded T hT.le hTlt
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.flow
    (K := Icc 0 T) (fun t ht => ⟨ht.1, ht.2.trans_lt hTlt⟩)
    (ordConnected_Icc : (Icc (0 : ℝ) T).OrdConnected)
    (show (Icc (0 : ℝ) T).Nontrivial from
      ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, hT.ne⟩)
  have hcap (R : ℝ) (hR : 0 < R) :
      ContinuousOn (fun z : ℝ × StandardCapSpace =>
        M04.shiCappedDistance (G.flow.metric z.1) p R z.2) (Icc 0 T ×ˢ univ) := by
    exact M04.continuousOn_shiCappedDistance_flow F hK hR p
      (U := univ) (fun _ _ _ _ => mem_univ _) (fun t ht x _ =>
        (le_abs_self _).trans (hbound t ht x))
  intro z hz
  let d := ((G.flow.metric z.1).edist p z.2).toReal
  let R := d + 1
  have hR : 0 < R := by dsimp [R, d]; positivity
  have hzball : z.2 ∈ (G.flow.metric z.1).ball p R := by
    change (G.flow.metric z.1).edist p z.2 < ENNReal.ofReal R
    rw [← ENNReal.ofReal_toReal ((G.flow.metric z.1).edist_ne_top p z.2)]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr (by dsimp [R, d]; linarith)
  have hvalue := M04.shiCappedDistance_eq_of_mem_ball hzball
  have hlim := hcap R hR z hz
  have hnear : ∀ᶠ w in 𝓝[Icc 0 T ×ˢ (univ : Set StandardCapSpace)] z,
      M04.shiCappedDistance (G.flow.metric w.1) p R w.2 < R :=
    hlim (gt_mem_nhds (by
      change M04.shiCappedDistance (G.flow.metric z.1) p R z.2 < R
      rw [hvalue]
      dsimp [R, d]
      linarith))
  have hagree : (fun w : ℝ × StandardCapSpace =>
      ((G.flow.metric w.1).edist p w.2).toReal) =ᶠ[
      𝓝[Icc 0 T ×ˢ (univ : Set StandardCapSpace)] z]
      (fun w => M04.shiCappedDistance (G.flow.metric w.1) p R w.2) := by
    filter_upwards [hnear] with w hw
    have hwball : w.2 ∈ (G.flow.metric w.1).ball p R := by
      by_contra hn
      have heq := M04.shiCappedDistance_eq_of_le_edist hR.le (le_of_not_gt hn)
      exact (ne_of_lt hw) heq
    exact (M04.shiCappedDistance_eq_of_mem_ball hwball).symm
  change Tendsto _ _ (𝓝 (((G.flow.metric z.1).edist p z.2).toReal))
  rw [← hvalue]
  exact hlim.congr' hagree.symm



theorem continuousOn_rawDistanceSquare
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (p : StandardCapSpace) :
    ContinuousOn (Function.uncurry (rawDistanceSquare G p)) (Icc 0 T ×ˢ univ) := by
  exact continuousOn_const.add ((continuousOn_raw_distance G hT hTlt p).pow 2)

end PoincareConjecture.M35.Uniqueness
