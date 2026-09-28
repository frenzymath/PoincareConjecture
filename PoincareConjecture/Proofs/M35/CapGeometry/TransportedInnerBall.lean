import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapDistance
import PoincareConjecture.Proofs.M35.RawFlow.MetricSpace










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35




theorem image_ball_subset_of_tangentNorm_upper
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f : M → N)
    {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    {C r : ℝ} (hC : 0 < C) (x : M) (hball : g.ball x r ⊆ U)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace (𝓡 3) z,
      h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤ C * g.tangentNorm z v) :
    f '' g.ball x r ⊆ h.ball (f x) (C * r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨gamma, hzero, hone, hsmooth, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hy
  have hmaps : MapsTo gamma (Icc (0 : ℝ) 1) U := by
    intro s hs
    apply hball
    have hd := Manifold.riemannianEDist_le_pathELength
      (hsmooth.mono (Icc_subset_Icc le_rfl hs.2)) hzero rfl hs.1
    exact (hd.trans (Manifold.pathELength_mono le_rfl hs.2)).trans_lt hlength
  have hlength' := pathELength_comp_le_of_tangentNorm_le
    g h f hU hf hC.le hbound gamma 0 1 hsmooth hmaps
  have hd : h.edist (f x) (f y) ≤ h.pathELength (f ∘ gamma) 0 1 :=
    Manifold.riemannianEDist_le_pathELength
      ((hf.of_le (by simp)).comp hsmooth hmaps)
      (congrArg f hzero) (congrArg f hone) zero_le_one
  apply (hd.trans hlength').trans_lt
  rw [ENNReal.ofReal_mul hC.le]
  exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top hlength

end PoincareConjecture.M35
