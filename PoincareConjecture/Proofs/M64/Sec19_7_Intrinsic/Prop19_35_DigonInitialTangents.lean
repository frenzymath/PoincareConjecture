import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_UnitTangentIndependence
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConvexCornerArrival





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture




theorem m64Intrinsic_convex_corner_departure_nonneg
    {eta : ℝ → AnnulusCoordinates} {T : ℝ}
    (he : ContDiff ℝ ∞ eta) (hT : 0 < T)
    {S : Set AnnulusCoordinates} (hconf : MapsTo eta (Ioo 0 T) S)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (eta 0)) (hzero : phi (eta 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (eta 0), z ∈ S → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) :
    (0 : ℝ × ℝ) ≤ L (deriv eta 0) := by
  have hd : HasDerivAt (phi ∘ eta) (L (deriv eta 0)) 0 :=
    hphi.comp_hasDerivAt 0 ((he.differentiable (by simp) 0).hasDerivAt)
  have hn : ∀ᶠ t in 𝓝[>] (0 : ℝ), eta t ∈ S →
      0 ≤ (phi (eta t)).1 ∧ 0 ≤ (phi (eta t)).2 :=
    (he.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually hcorner
  apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  filter_upwards [hn, Ioo_mem_nhdsGT hT] with t ht htI
  have hq := ht (hconf htI)
  change (0 : ℝ × ℝ) ≤ (t - 0)⁻¹ • (phi (eta t) - phi (eta 0))
  rw [hzero, sub_zero, sub_zero]
  exact ⟨mul_nonneg (inv_pos.mpr htI.1).le hq.1,
    mul_nonneg (inv_pos.mpr htI.1).le hq.2⟩





theorem m64Intrinsic_digon_initial_velocity_ne
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hgeoA : G.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : G.IsGeodesicOn beta (Icc 0 B)) (hbase : beta 0 = alpha 0)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B)) :
    deriv alpha 0 ≠ deriv beta 0 := by
  intro hvel
  have ha : G.IsGeodesicOn alpha ({0} : Set ℝ) := by
    intro t ht
    rcases mem_singleton_iff.mp ht with rfl
    exact hgeoA 0 ⟨le_rfl, hA.le⟩
  have hb : G.IsGeodesicOn beta ({0} : Set ℝ) := by
    intro t ht
    rcases mem_singleton_iff.mp ht with rfl
    exact hgeoB 0 ⟨le_rfl, hB.le⟩
  have heq := ha.eq_nhds_of_initial_data hb (mem_singleton 0) (alpha 0) (by simp)
    hbase.symm (by
      simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using hvel)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (min A B) :=
    Ioo_mem_nhdsGT (lt_min hA hB)
  have hagree : ∀ᶠ t in 𝓝[>] (0 : ℝ), alpha t = beta t :=
    heq.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htEq⟩ := (hsmall.and hagree).exists
  have htA : t < A := ht.2.trans_le (min_le_left A B)
  have htB : t < B := ht.2.trans_le (min_le_right A B)
  rcases hmeet t ⟨ht.1.le, htA.le⟩ t ⟨ht.1.le, htB.le⟩ htEq with h | h
  · exact ht.1.ne' h.1
  · exact htA.ne h.1





theorem m64Intrinsic_digon_initial_transverse_at_convex_corner
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hgeoA : G.IsGeodesicOn alpha (Icc 0 A))
    (hgeoB : G.IsGeodesicOn beta (Icc 0 B)) (hbase : beta 0 = alpha 0)
    (hmeet : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      alpha s = beta t → (s = 0 ∧ t = 0) ∨ (s = A ∧ t = B))
    (hunitA : G.inner (alpha 0) (deriv alpha 0) (deriv alpha 0) = 1)
    (hunitB : G.inner (beta 0) (deriv beta 0) (deriv beta 0) = 1)
    {S : Set AnnulusCoordinates} (hconfA : MapsTo alpha (Ioo 0 A) S)
    (hconfB : MapsTo beta (Ioo 0 B) S)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (alpha 0)) (hzero : phi (alpha 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (alpha 0), z ∈ S → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) :
    LinearIndependent ℝ (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates) := by
  have hconeA := m64Intrinsic_convex_corner_departure_nonneg ha hA hconfA L hphi hzero hcorner
  have hconeB := m64Intrinsic_convex_corner_departure_nonneg hb hB hconfB L
    (hbase.symm ▸ hphi) (hbase.symm ▸ hzero) (hbase.symm ▸ hcorner)
  have hopp : deriv alpha 0 ≠ -deriv beta 0 := by
    intro heq
    have hnonpos : L (deriv alpha 0) ≤ (0 : ℝ × ℝ) := by
      rw [heq, map_neg]
      exact neg_nonpos.mpr hconeB
    have hz : deriv alpha 0 = 0 := by
      apply L.injective
      simpa only [map_zero] using le_antisymm hnonpos hconeA
    simp only [hz, map_zero] at hunitA
    exact zero_ne_one hunitA
  have huB : G.inner (alpha 0) (deriv beta 0 : AnnulusCoordinates)
      (deriv beta 0 : AnnulusCoordinates) = 1 := by
    rw [← hbase]
    exact hunitB
  exact m64Intrinsic_unit_tangents_independent G (alpha 0) (deriv alpha 0) (deriv beta 0)
    hunitA huB (m64Intrinsic_digon_initial_velocity_ne G hA hB hgeoA hgeoB hbase hmeet) hopp

end PoincareConjecture
