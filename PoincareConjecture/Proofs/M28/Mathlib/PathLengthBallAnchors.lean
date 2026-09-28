import PoincareConjecture.Proofs.M28.Mathlib.PathLengthAnchors












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem exists_pathELength_right_anchor_in_ball
    (g : RiemannianMetric n M) {U : Set M} {x : M}
    {delta e L a b : ℝ} {γ : ℝ → M}
    (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (he : 0 ≤ e) (hL : 0 < L) (hbudget : e + L < delta)
    (hstart : g.edist x (γ a) ≤ ENNReal.ofReal e)
    (hend : γ b ∉ U) (hcapture : g.ball x delta ⊆ U) :
    ∃ t ∈ Ioo a b, g.pathELength γ a t = ENNReal.ofReal L ∧
      MapsTo γ (Icc a t) (g.ball x delta) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdelta : 0 < delta := (add_pos_of_nonneg_of_pos he hL).trans hbudget
  have hsum : ENNReal.ofReal e + ENNReal.ofReal L < ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add he hL.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hdelta).mpr hbudget
  have hroom : ENNReal.ofReal L < g.pathELength γ a b := by
    by_contra hnot
    have hlen : g.pathELength γ a b ≤ ENNReal.ofReal L := le_of_not_gt hnot
    have hdist : g.edist (γ a) (γ b) ≤ g.pathELength γ a b :=
      Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab.le
    have htriangle : g.edist x (γ b) ≤ g.edist x (γ a) + g.edist (γ a) (γ b) :=
      Manifold.riemannianEDist_triangle
    exact hend (hcapture ((htriangle.trans
      (add_le_add hstart (hdist.trans hlen))).trans_lt hsum))
  obtain ⟨t, ht, hlength⟩ := exists_pathELength_right_anchor g hab hγ hL hroom
  refine ⟨t, ht, hlength, ?_⟩
  intro s hs
  have hsmooth := hγ.mono (Icc_subset_Icc le_rfl (hs.2.trans ht.2.le))
  have hdist : g.edist (γ a) (γ s) ≤ g.pathELength γ a s :=
    Manifold.riemannianEDist_le_pathELength hsmooth rfl rfl hs.1
  have hsub : g.pathELength γ a s ≤ g.pathELength γ a t :=
    Manifold.pathELength_mono le_rfl hs.2
  have htriangle : g.edist x (γ s) ≤ g.edist x (γ a) + g.edist (γ a) (γ s) :=
    Manifold.riemannianEDist_triangle
  change g.edist x (γ s) < ENNReal.ofReal delta
  exact (htriangle.trans (add_le_add hstart
    (hdist.trans (hsub.trans_eq hlength)))).trans_lt hsum




theorem exists_pathELength_left_anchor_in_ball
    (g : RiemannianMetric n M) {U : Set M} {x : M}
    {delta e L a b : ℝ} {γ : ℝ → M}
    (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (he : 0 ≤ e) (hL : 0 < L) (hbudget : e + L < delta)
    (hstart : g.edist x (γ b) ≤ ENNReal.ofReal e)
    (hend : γ a ∉ U) (hcapture : g.ball x delta ⊆ U) :
    ∃ t ∈ Ioo a b, g.pathELength γ t b = ENNReal.ofReal L ∧
      MapsTo γ (Icc t b) (g.ball x delta) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdelta : 0 < delta := (add_pos_of_nonneg_of_pos he hL).trans hbudget
  have hsum : ENNReal.ofReal e + ENNReal.ofReal L < ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add he hL.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hdelta).mpr hbudget
  have hroom : ENNReal.ofReal L < g.pathELength γ a b := by
    by_contra hnot
    have hlen : g.pathELength γ a b ≤ ENNReal.ofReal L := le_of_not_gt hnot
    have hdist : g.edist (γ b) (γ a) ≤ g.pathELength γ a b := by
      change Manifold.riemannianEDist (𝓡 n) (γ b) (γ a) ≤ _
      rw [Manifold.riemannianEDist_comm]
      exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab.le
    have htriangle : g.edist x (γ a) ≤ g.edist x (γ b) + g.edist (γ b) (γ a) :=
      Manifold.riemannianEDist_triangle
    exact hend (hcapture ((htriangle.trans
      (add_le_add hstart (hdist.trans hlen))).trans_lt hsum))
  obtain ⟨t, ht, hlength⟩ := exists_pathELength_left_anchor g hab hγ hL hroom
  refine ⟨t, ht, hlength, ?_⟩
  intro s hs
  have hsmooth := hγ.mono (Icc_subset_Icc (ht.1.le.trans hs.1) le_rfl)
  have hdist : g.edist (γ b) (γ s) ≤ g.pathELength γ s b := by
    change Manifold.riemannianEDist (𝓡 n) (γ b) (γ s) ≤ _
    rw [Manifold.riemannianEDist_comm]
    exact Manifold.riemannianEDist_le_pathELength hsmooth rfl rfl hs.2
  have hsub : g.pathELength γ s b ≤ g.pathELength γ t b :=
    Manifold.pathELength_mono hs.1 le_rfl
  have htriangle : g.edist x (γ s) ≤ g.edist x (γ b) + g.edist (γ b) (γ s) :=
    Manifold.riemannianEDist_triangle
  change g.edist x (γ s) < ENNReal.ofReal delta
  exact (htriangle.trans (add_le_add hstart
    (hdist.trans (hsub.trans_eq hlength)))).trans_lt hsum

end PoincareConjecture.M28
