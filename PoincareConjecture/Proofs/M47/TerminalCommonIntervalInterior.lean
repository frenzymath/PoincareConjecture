import PoincareConjecture.Proofs.M47.BlowupControlsSourceHistory










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

private theorem history_heq_of_forward_heq
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {s t : ℝ}
    (hs : s ∈ H.generalized.interval) (ht : t ∈ H.generalized.interval)
    {x : (H.generalized.slice s).carrier} {y : (H.generalized.slice t).carrier}
    (hst : s = t) (hxy : HEq (H.history.forward s hs x) (H.history.forward t ht y)) :
    HEq x y := by
  cases hst
  exact heq_of_eq ((H.history.forward_openEmbedding s hs).injective (eq_of_heq hxy))



theorem terminalCommonInterval_history_interior
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {base Q a tau B eta : ℝ}
    (hbase : base ∈ H.generalized.interval) (htau : 0 < tau) (ha : a < -tau)
    (U : TopologicalSpace.Opens (F.slice base).carrier) (p0 : U)
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0) U)
    (hbased : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x)
    (hcurv : ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
      |(F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs x)| ≤ B * Q)
    (hneg : ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
      (F.connection (base + s / Q)).negativeCurvaturePart (e.forward s hs x) ≤ eta * Q) :
    ∃ htime : ∀ s ∈ Icc (-tau) 0, base + s / Q ∈ H.generalized.interval,
      ∃ d : GeneralizedFlowCylinder H.generalized (H.generalized.slice base) base Q
          (Icc (-tau) 0) (H.history.forward base hbase ⁻¹' U),
        (∀ hs x, x ∈ H.history.forward base hbase ⁻¹' U →
          d.pointMap 0 hs x = (⟨base, x⟩ : H.generalized.point)) ∧
        (∀ s hs x, x ∈ H.history.forward base hbase ⁻¹' U →
          H.history.forward (base + s / Q) (htime s hs) (d.forward s hs x) =
            e.forward s ⟨ha.le.trans hs.1, hs.2⟩ (H.history.forward base hbase x)) ∧
        (∀ s hs x, x ∈ H.history.forward base hbase ⁻¹' U →
          ∀ v w : TangentSpace (𝓡 3) x,
            d.pullbackInner s hs x v w =
              e.pullbackInner s ⟨ha.le.trans hs.1, hs.2⟩ (H.history.forward base hbase x)
                (mfderiv (𝓡 3) (𝓡 3) (H.history.forward base hbase) x v)
                (mfderiv (𝓡 3) (𝓡 3) (H.history.forward base hbase) x w)) ∧
        (∀ s hs x, x ∈ H.history.forward base hbase ⁻¹' U →
          |H.generalized.curvatureNorm (d.pointMap s hs x)| ≤ B * Q ∧
          (H.generalized.connection (base + s / Q)).negativeCurvaturePart
            (d.forward s hs x) ≤ eta * Q) := by
  obtain ⟨htime, d, hmap, hmetric, _hidentity⟩ :=
    exists_regular_history_search_interior H hbase htau ha U p0 e hbased
  let d' := regular_history_rebase_cylinder H hbase U d
  have hread (s : ℝ) (hs : s ∈ Icc (-tau) 0)
      (x : (H.generalized.slice base).carrier) (hx : x ∈ H.history.forward base hbase ⁻¹' U) :
      H.history.forward (base + s / Q) (htime s hs) (d'.forward s hs x) =
        e.forward s ⟨ha.le.trans hs.1, hs.2⟩ (H.history.forward base hbase x) :=
    hmap s hs _ hx
  refine ⟨htime, d', ?_, hread, ?_, ?_⟩
  · intro hs x hx
    apply Sigma.ext (by simp : base + 0 / Q = base)
    apply history_heq_of_forward_heq H (htime 0 hs) hbase (by simp)
    exact (heq_of_eq (hread 0 hs x hx)).trans (hbased _ _ hx)
  · intro s hs x hx v w
    exact (regular_history_rebase_pullback H hbase U d U.isOpen s hs x hx v w).trans
      (hmetric s hs _ hx _ _)
  · intro s hs x hx
    have hn := H.curvature_norm_pullback (base + s / Q) (htime s hs) (d'.forward s hs x)
    have hnegative := H.negative_part_pullback (base + s / Q) (htime s hs) (d'.forward s hs x)
    rw [hread s hs x hx] at hn hnegative
    change |(H.generalized.connection (base + s / Q)).curvatureTensorNorm
        (d'.forward s hs x)| ≤ B * Q ∧ _
    rw [← hn, ← hnegative]
    exact ⟨hcurv _ _ _ hx, hneg _ _ _ hx⟩



theorem terminalCommonInterval_ball_preimage
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {base Q a radius : ℝ}
    (hbase : base ∈ H.generalized.interval) (ha : a < 0)
    (x : (H.generalized.slice base).carrier)
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
      ((F.metric base).ball (H.history.forward base hbase x) radius))
    (hbased : ∀ hs y, y ∈ (F.metric base).ball (H.history.forward base hbase x) radius →
      HEq (e.forward 0 hs y) y) :
    H.history.forward base hbase ⁻¹'
        (F.metric base).ball (H.history.forward base hbase x) radius =
      (H.generalized.metric base).ball x radius := by
  let h0 : (0 : ℝ) ∈ Icc a 0 := ⟨ha.le, le_rfl⟩
  have hregular := e.regular_image_of_earlier h0 ⟨a, ⟨le_rfl, ha.le⟩, ha⟩
  have hball : (F.metric base).ball (H.history.forward base hbase x) radius ⊆
      range (H.history.forward base hbase) := by
    rw [H.regular_range base hbase]
    intro y hy
    have he : (⟨base + 0 / Q, e.forward 0 h0 y⟩ : Σ t, (F.slice t).carrier) =
        ⟨base, y⟩ := Sigma.ext (by simp) (hbased h0 y hy)
    exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
      p.2 ∈ m33RegularRegion F p.1) he).mp (hregular ⟨y, hy, rfl⟩)
  have himage := H.history.ball_image_of_subset base hbase x radius hball
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := himage.symm ▸ hy
    exact (H.history.forward_openEmbedding base hbase).injective hzy ▸ hz
  · intro hy
    exact himage ▸ mem_image_of_mem _ hy

end PoincareConjecture.M47
