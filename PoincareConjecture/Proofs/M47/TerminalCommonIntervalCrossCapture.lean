import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCapture









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v w

namespace PoincareConjecture.M47

variable {M : Type u} {N : Type v} {X : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace X]
  [T3Space M] [T3Space N] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]

omit [T3Space M] in


theorem terminalCommonInterval_cross_capture
    (g : RiemannianMetric 3 M) (k : RiemannianMetric 3 N)
    (h : RiemannianMetric 3 X) (hk : MetricComplete k)
    (e : OpenPartialHomeomorph M X) (f : OpenPartialHomeomorph N X)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f f.source)
    (hfi : ContMDiffOn (𝓡 3) (𝓡 3) 1 f.symm f.target)
    (p : M) (q : N) (hbase : e p = f q) {R : ℝ} (hR : 0 < R)
    (hes : {z | g.edist p z ≤ ENNReal.ofReal (R + 1)} ⊆ e.source)
    (hfs : {z | k.edist q z ≤ ENNReal.ofReal (8 * (R + 1))} ⊆ f.source)
    (hupp : ∀ z, g.edist p z ≤ ENNReal.ofReal (R + 1) →
      ∀ v : TangentSpace (𝓡 3) z,
        h.tangentNorm (e z) (mfderiv (𝓡 3) (𝓡 3) e z v) ≤ 2 * g.tangentNorm z v)
    (hlow : ∀ z, k.edist q z ≤ ENNReal.ofReal (8 * (R + 1)) →
      ∀ v : TangentSpace (𝓡 3) z,
        k.tangentNorm z v ≤ 2 * h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v)) :
    {z | g.edist p z ≤ ENNReal.ofReal R} ⊆ (e.trans f.symm).source ∧
      MapsTo (e.trans f.symm) {z | g.edist p z ≤ ENNReal.ofReal R}
        (k.ball q (4 * (R + 1))) := by
  have hforward := g.image_ball_subset_ball_of_tangentNorm_le h e p
    (by norm_num : (0 : ℝ) < 2)
    (fun z hz => hes (show g.edist p z ≤ ENNReal.ofReal (R + 1) from le_of_lt hz))
    (fun z hz => (he z hz).contMDiffAt (e.open_source.mem_nhds hz))
    (fun z hz v => hupp z (show g.edist p z ≤ ENNReal.ofReal (R + 1) from le_of_lt hz) v)
  have hcapture : h.ball (f q) (2 * (R + 1)) ⊆ f '' k.ball q (4 * (R + 1)) := by
    have h := terminalCommonInterval_capture_of_closed_buffer k h hk f hf hfi q
      (by positivity : 0 < 8 * (R + 1)) (by norm_num : (0 : ℝ) < 2)
      (by linarith : 2 * (2 * (R + 1)) < 8 * (R + 1)) hfs hlow
    simpa only [show 2 * (2 * (R + 1)) = 4 * (R + 1) by ring] using h
  have hpoint (z : M) (hz : g.edist p z ≤ ENNReal.ofReal R) :
      z ∈ (e.trans f.symm).source ∧ (e.trans f.symm) z ∈ k.ball q (4 * (R + 1)) := by
    have hzball : z ∈ g.ball p (R + 1) :=
      hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < R + 1)).mpr (by linarith))
    have hzs : z ∈ e.source := hes (show g.edist p z ≤ ENNReal.ofReal (R + 1) from le_of_lt hzball)
    have hzimage := hforward (mem_image_of_mem e hzball)
    rw [hbase] at hzimage
    obtain ⟨y, hy, hye⟩ := hcapture hzimage
    have hyd : k.edist q y < ENNReal.ofReal (4 * (R + 1)) := hy
    have hys : y ∈ f.source :=
      hfs (hyd.le.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    have hzt : e z ∈ f.target := hye ▸ f.map_source hys
    refine ⟨⟨hzs, hzt⟩, ?_⟩
    change f.symm (e z) ∈ k.ball q (4 * (R + 1))
    rw [← hye, f.left_inv hys]
    exact hy
  exact ⟨fun z hz => (hpoint z hz).1, fun z hz => (hpoint z hz).2⟩

omit [T3Space M] [T3Space N] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X] in


theorem terminalCommonInterval_cross_map_identities
    (e : OpenPartialHomeomorph M X) (f : OpenPartialHomeomorph N X)
    (p : M) (q : N) (hp : p ∈ e.source) (hq : q ∈ f.source) (hbase : e p = f q) :
    (e.trans f.symm) p = q ∧ (e.trans f.symm).symm q = p ∧
      (∀ z ∈ (e.trans f.symm).source,
        f ((e.trans f.symm) z) = e z ∧ (e.trans f.symm).symm ((e.trans f.symm) z) = z) ∧
      ∀ z ∈ (e.trans f.symm).target,
        e ((e.trans f.symm).symm z) = f z ∧
          (e.trans f.symm) ((e.trans f.symm).symm z) = z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change f.symm (e p) = q
    rw [hbase, f.left_inv hq]
  · change e.symm (f q) = p
    rw [← hbase, e.left_inv hp]
  · intro z hz
    exact ⟨f.right_inv hz.2, (e.trans f.symm).left_inv hz⟩
  · intro z hz
    exact ⟨e.right_inv hz.2, (e.trans f.symm).right_inv hz⟩

end PoincareConjecture.M47
