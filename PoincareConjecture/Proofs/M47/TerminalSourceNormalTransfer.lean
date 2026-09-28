import PoincareConjecture.Proofs.M34.Standard.CapBallVolumeImage
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_BufferBalls









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]



theorem terminalSourceNormal_edist_le
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (x y : M) : h.edist (e x) (e y) ≤ g.edist x y := by
  have he : ContMDiff (𝓡 3) (𝓡 3) ∞ e :=
    contMDiffOn_univ.mp (hsource ▸ e.contMDiffOn)
  exact g.edist_comp_le_of_pullback_bound h he
    (fun z v => (hmetric z v v).symm.le) x y

variable [T3Space M]



theorem terminalSourceNormal_ball_image
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (p : M) (r : ℝ) (hcover : h.ball (e p) r ⊆ e.target) :
    e '' g.ball p r = h.ball (e p) r := by
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source := e.contMDiffOn.of_le (by simp)
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target :=
    e.symm.contMDiffOn.of_le (by simp)
  have hn (x : M) (v : TangentSpace (𝓡 3) x) :
      g.tangentNorm x v = h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) :=
    congrArg Real.sqrt (hmetric x v v)
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (terminalSourceNormal_edist_le g h e hsource hmetric p x).trans_lt hx
  · have hb := g.ball_subset_image_ball_of_forward_tangentNorm_le h
      e.toOpenPartialHomeomorph hf hi (hsource.symm ▸ mem_univ p) zero_lt_one hcover
      (fun x _hx _hd v => by
        change g.tangentNorm x v ≤
          1 * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
        rw [hn, one_mul])
    change h.ball (e p) r ⊆ e '' (g.ball p (1 * r) ∩ e.source) at hb
    simpa only [one_mul, hsource, inter_univ] using hb

variable [T3Space N] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology M] [SecondCountableTopology N]



theorem terminalSourceNormal_ball_volume
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (p : M) (r : ℝ) (hcover : h.ball (e p) r ⊆ e.target) :
    calibratedMetricVolume g (g.ball p r) = calibratedMetricVolume h (h.ball (e p) r) := by
  let : EMetricSpace M := g.comparisonEMetric
  have hopen : IsOpen (g.ball p r) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source := e.contMDiffOn.of_le (by simp)
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target :=
    e.symm.contMDiffOn.of_le (by simp)
  have hn (x : M) (v : TangentSpace (𝓡 3) x) :
      g.tangentNorm x v = h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) :=
    congrArg Real.sqrt (hmetric x v v)
  have hsub : g.ball p r ⊆ e.source := hsource.symm ▸ subset_univ _
  have hupper := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le g h
    e.toOpenPartialHomeomorph hf zero_lt_one
    (fun x _hx v => by
      change h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤ 1 * g.tangentNorm x v
      rw [← hn, one_mul]) hopen.measurableSet hsub
  have hlower := M34.calibratedMetricVolume_le_mul_image_of_local_tangentNorm_lower g h
    e.toOpenPartialHomeomorph hf hi zero_lt_one
    (fun x _hx v => by
      change g.tangentNorm x v ≤ 1 * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
      rw [hn, one_mul]) hopen.measurableSet hsub
  have himage := terminalSourceNormal_ball_image g h e hsource hmetric p r hcover
  change calibratedMetricVolume h (e '' g.ball p r) ≤ _ at hupper
  change _ ≤ ENNReal.ofReal 1 ^ 3 * calibratedMetricVolume h (e '' g.ball p r) at hlower
  rw [himage] at hupper hlower
  simp only [ENNReal.ofReal_one, one_pow, one_mul] at hlower hupper
  exact le_antisymm hlower hupper

omit [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace N] [BorelSpace N]
  [SecondCountableTopology M] [SecondCountableTopology N] in


theorem terminalSourceNormal_compact_ball
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (p : M) (r : ℝ) (hcompact : IsCompact (closure (h.ball (e p) r)))
    (hinside : closure (h.ball (e p) r) ⊆ e.target) :
    IsCompact (closure (g.ball p r)) := by
  have he := e.toOpenPartialHomeomorph.isOpenEmbedding hsource
  have hc : IsCompact (e ⁻¹' closure (h.ball (e p) r)) :=
    he.isEmbedding.isInducing.isCompact_preimage' hcompact (by
      intro y hy
      exact ⟨e.symm y, e.right_inv (hinside hy)⟩)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.preimage he.continuous)
  intro x hx
  exact subset_closure ((terminalSourceNormal_edist_le g h e hsource hmetric p x).trans_lt hx)

end PoincareConjecture.M47
