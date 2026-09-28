import PoincareConjecture.Proofs.M47.JointSeedGeodesicSmooth
import PoincareConjecture.Proofs.M47.JointSeedRadialExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M47

theorem exists_jointSeed_radial_path
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (q y : M) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure (g.ball q r))) (hy : y ∈ g.ball q r) :
    ∃ beta : ℝ → M, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ beta ∧
      beta 0 = q ∧ beta 1 = y ∧ MapsTo beta (Icc (0 : ℝ) 1) (g.ball q r) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (beta s) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) beta s 1) < r := by
  obtain ⟨epsilon, hepsilon, gamma, hgeo, hzero, hone, hsegment⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball q y hr hcompact hy
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-epsilon) (1 + epsilon) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨k, hk⟩ := hgeo.exists_constant_tangentNorm (by linarith)
  have hlength := hgeo.pathELength_eq_of_edist_segment hepsilon hzero hsegment
  have hkdist : ENNReal.ofReal (k : ℝ) = g.edist q y := by
    have h := g.pathELength_eq_of_tangentNorm_eq
      (fun s (hs : s ∈ Icc (0 : ℝ) 1) => hk s (hI hs))
    simp only [sub_zero, ENNReal.ofReal_one, mul_one] at h
    exact h.symm.trans hlength
  have hkr : (k : ℝ) < r := (ENNReal.ofReal_lt_ofReal_iff hr).1 (hkdist.trans_lt hy)
  have hmap : MapsTo gamma (Icc (0 : ℝ) 1) (g.ball q r) := by
    have h := g.mapsTo_ball_of_pathELength_lt (hgeo.contMDiffOn.mono hI)
      (hlength.trans_lt hy)
    simpa only [hzero] using h
  obtain ⟨beta, hsmooth, hgerm⟩ := exists_jointSeed_global_radial_extension
    hepsilon gamma (jointSeed_geodesic_contMDiffOn hgeo)
  refine ⟨beta, hsmooth,
    ((hgerm 0 (by simp)).self_of_nhds).trans hzero,
    ((hgerm 1 (by simp)).self_of_nhds).trans hone, ?_, ?_⟩
  · intro s hs
    simpa only [(hgerm s hs).self_of_nhds] using hmap hs
  · intro s hs
    rw [(hgerm s hs).mfderiv_eq, (hgerm s hs).self_of_nhds, hk s (hI hs)]
    exact hkr

end PoincareConjecture.M47
