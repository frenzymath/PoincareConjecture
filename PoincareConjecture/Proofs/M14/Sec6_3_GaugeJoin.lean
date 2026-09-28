import PoincareConjecture.Proofs.M14.Sec6_3_GaugeBlend










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)
  (α β : ℝ → G.Point)



noncomputable def oneSidedGaugeJoin (c r d s : ℝ) : G.Point :=
  if s < c - r then α s else if c ≤ s then β s else
    gaugeBlend b lift α β (c - 3 * d / 2) (d / 2) s



theorem oneSidedGaugeJoin_eq_middle {c r d s : ℝ} (hs : s ∈ Ico (c - r) c) :
    oneSidedGaugeJoin b lift α β c r d s =
      gaugeBlend b lift α β (c - 3 * d / 2) (d / 2) s := by
  simp only [oneSidedGaugeJoin, if_neg (not_lt.mpr hs.1), if_neg (not_le.mpr hs.2)]



theorem oneSidedGaugeJoin_eq_left {c r d : ℝ} (hd : 0 < d)
    (hα : ∀ s ∈ Icc (c - r) c,
      (G.gaugeCover.cylinder b).toSpacetime (lift (α s)) = α s)
    (htime : ∀ s ∈ Icc (c - r) c, (lift (α s)).1 = (lift (β s)).1)
    {s : ℝ} (hs : s ≤ c - 2 * d) :
    oneSidedGaugeJoin b lift α β c r d s = α s := by
  by_cases hl : s < c - r
  · simp only [oneSidedGaugeJoin, if_pos hl]
  have hsI : s ∈ Ico (c - r) c := ⟨le_of_not_gt hl, by linarith⟩
  rw [oneSidedGaugeJoin_eq_middle b lift α β hsI]
  exact gaugeBlend_eq_left b lift α β (by linarith) (by linarith)
    (hα s ⟨hsI.1, hsI.2.le⟩) (htime s ⟨hsI.1, hsI.2.le⟩)




theorem oneSidedGaugeJoin_eq_right {c r d : ℝ} (hd : 0 < d) (hdr : 2 * d < r)
    (hβ : ∀ s ∈ Icc (c - r) c,
      (G.gaugeCover.cylinder b).toSpacetime (lift (β s)) = β s)
    {s : ℝ} (hs : c - d ≤ s) :
    oneSidedGaugeJoin b lift α β c r d s = β s := by
  have hleft : ¬s < c - r := by linarith
  by_cases hright : c ≤ s
  · simp only [oneSidedGaugeJoin, if_neg hleft, if_pos hright]
  have hsI : s ∈ Ico (c - r) c := ⟨le_of_not_gt hleft, lt_of_not_ge hright⟩
  rw [oneSidedGaugeJoin_eq_middle b lift α β hsI]
  exact gaugeBlend_eq_right b lift α β (by linarith) (by linarith)
    (hβ s ⟨hsI.1, hsI.2.le⟩)

end PoincareConjecture.M14
