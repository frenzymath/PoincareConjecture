import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnTransverse











noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_convex_corner_return_velocity_ne
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hT : 0 < T) (hreg : deriv gamma 0 ≠ 0)
    {S : Set AnnulusCoordinates} (hconf : MapsTo gamma (Icc 0 T) S)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (gamma 0))
    (hzero : phi (gamma 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (gamma 0), z ∈ S → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2)
    (hreturn : gamma 0 = gamma T) : deriv gamma 0 ≠ deriv gamma T := by
  intro hvel
  have hd0 : HasDerivAt (phi ∘ gamma) (L (deriv gamma 0)) 0 :=
    hphi.comp_hasDerivAt 0 ((hg.differentiable (by simp) 0).hasDerivAt)
  have hphiT : HasFDerivAt phi L.toContinuousLinearMap (gamma T) := hreturn ▸ hphi
  have hdT : HasDerivAt (phi ∘ gamma) (L (deriv gamma 0)) T := by
    simpa only [hvel] using!
      hphiT.comp_hasDerivAt T ((hg.differentiable (by simp) T).hasDerivAt)
  have hn0 : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      gamma x ∈ S → 0 ≤ (phi (gamma x)).1 ∧ 0 ≤ (phi (gamma x)).2 :=
    (hg.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually hcorner
  have hnT : ∀ᶠ x in 𝓝[<] T,
      gamma x ∈ S → 0 ≤ (phi (gamma x)).1 ∧ 0 ≤ (phi (gamma x)).2 :=
    (hg.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
      (hreturn ▸ hcorner)
  have hnonneg : (0 : ℝ × ℝ) ≤ L (deriv gamma 0) := by
    apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd0).2
    filter_upwards [hn0, Ioo_mem_nhdsGT hT] with x hx hxt
    have hq := hx (hconf (Ioo_subset_Icc_self hxt))
    change (0 : ℝ × ℝ) ≤ (x - 0)⁻¹ • (phi (gamma x) - phi (gamma 0))
    rw [hzero, sub_zero, sub_zero]
    exact ⟨mul_nonneg (inv_pos.mpr hxt.1).le hq.1,
      mul_nonneg (inv_pos.mpr hxt.1).le hq.2⟩
  have hnonpos : L (deriv gamma 0) ≤ (0 : ℝ × ℝ) := by
    apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hdT).1
    filter_upwards [hnT, Ioo_mem_nhdsLT hT] with x hx hxt
    have hq := hx (hconf (Ioo_subset_Icc_self hxt))
    change (x - T)⁻¹ • (phi (gamma x) - phi (gamma T)) ≤ (0 : ℝ × ℝ)
    rw [← hreturn, hzero, sub_zero]
    exact ⟨mul_nonpos_of_nonpos_of_nonneg (inv_lt_zero'.mpr (sub_neg.mpr hxt.2)).le hq.1,
      mul_nonpos_of_nonpos_of_nonneg (inv_lt_zero'.mpr (sub_neg.mpr hxt.2)).le hq.2⟩
  apply hreg
  apply L.injective
  simpa only [map_zero] using le_antisymm hnonpos hnonneg




theorem m64Intrinsic_convex_corner_geodesic_return_velocity_ne
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {gamma : ℝ → AnnulusCoordinates} {s t T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : G.IsGeodesicOn gamma (Icc 0 T))
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) (hreg : deriv gamma 0 ≠ 0)
    {S : Set AnnulusCoordinates} (hconf : MapsTo gamma (Icc 0 T) S)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (gamma 0))
    (hzero : phi (gamma 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (gamma 0), z ∈ S → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2)
    (hreturn : gamma s = gamma t) : deriv gamma s ≠ deriv gamma t := by
  intro hvel
  let eta : ℝ → AnnulusCoordinates := fun x => gamma (x + (t - s))
  have he : G.IsGeodesicOn eta (Icc 0 s) := by
    intro x hx
    apply hgeo.comp_add (t - s)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hg' : G.IsGeodesicOn gamma (Icc 0 s) :=
    fun x hx => hgeo x ⟨hx.1, hx.2.trans (hst.le.trans ht)⟩
  have hetas : eta s = gamma t := by
    dsimp only [eta]
    congr 1
    ring
  have hd (x : ℝ) : HasDerivAt eta (deriv gamma (x + (t - s))) x := by
    have h := ((hg.differentiable (by simp) (x + (t - s))).hasDerivAt).scomp x
      ((hasDerivAt_id x).add_const (t - s))
    simpa only [eta, Function.comp_def, id_eq, one_smul] using! h
  have hds : deriv eta s = deriv gamma t := by
    simpa only [show s + (t - s) = t by ring] using (hd s).deriv
  have hcoord : deriv (fun x => extChartAt (𝓡 2) (gamma s) (gamma x)) s =
      deriv (fun x => extChartAt (𝓡 2) (gamma s) (eta x)) s := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
      using hvel.trans hds.symm
  have heq := hg'.eq_nhds_on_of_initial_data he (convex_Icc _ _).isPreconnected
    (t₀ := s) ⟨hs, le_rfl⟩ (gamma s) (by simp)
    (hreturn.trans hetas.symm) hcoord
  have hback : gamma 0 = gamma (t - s) := by
    simpa only [eta, zero_add] using
      (heq 0 (show (0 : ℝ) ∈ Icc 0 s from ⟨le_rfl, hs⟩)).self_of_nhds
  have hdback : deriv gamma 0 = deriv gamma (t - s) := by
    have h := (heq 0 (show (0 : ℝ) ∈ Icc 0 s from ⟨le_rfl, hs⟩)).deriv_eq
    simpa only [zero_add] using h.trans (hd 0).deriv
  exact m64Intrinsic_convex_corner_return_velocity_ne hg (sub_pos.mpr hst) hreg
    (fun x hx => hconf ⟨hx.1, by linarith [hx.2]⟩) L hphi hzero hcorner hback hdback




theorem m64Intrinsic_unit_convex_corner_return_transverse
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {gamma : ℝ → AnnulusCoordinates} {s t T : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : G.IsGeodesicOn gamma (Icc 0 T))
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (hunit : ∀ x ∈ Icc 0 T, G.inner (gamma x) (deriv gamma x) (deriv gamma x) = 1)
    {S : Set AnnulusCoordinates} (hconf : MapsTo gamma (Icc 0 T) S)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (gamma 0))
    (hzero : phi (gamma 0) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (gamma 0), z ∈ S → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2)
    (hreturn : gamma s = gamma t) :
    LinearIndependent ℝ (![deriv gamma s, -deriv gamma t] : Fin 2 → AnnulusCoordinates) := by
  have hsI : s ∈ Icc 0 T := ⟨hs, hst.le.trans ht⟩
  have htI : t ∈ Icc 0 T := ⟨hs.trans hst.le, ht⟩
  have hreg (x : ℝ) (hx : x ∈ Icc 0 T) : deriv gamma x ≠ 0 := by
    intro hz
    have h := hunit x hx
    simp only [hz, map_zero] at h
    norm_num at h
  have hsame := m64Intrinsic_convex_corner_geodesic_return_velocity_ne G hg hgeo
    hs hst ht (hreg 0 ⟨le_rfl, hs.trans (hst.le.trans ht)⟩)
    hconf L hphi hzero hcorner hreturn
  have hopp := m64Intrinsic_regular_return_velocity_ne_neg G hg
    (fun x hx => hgeo x ⟨hs.trans hx.1, hx.2.trans ht⟩) hst
    (fun x hx => hreg x ⟨hs.trans hx.1, hx.2.trans ht⟩) hreturn
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨neg_ne_zero.mpr (hreg t htI), ?_⟩
  intro c hc
  have hw : G.inner (gamma s) (deriv gamma t) (deriv gamma t) = 1 := by
    rw [hreturn]
    exact hunit t htI
  have hsq : c ^ 2 = 1 := by
    have h := hunit s hsI
    rw [← hc] at h
    simp only [map_smul, smul_apply, smul_eq_mul, map_neg, neg_apply, hw] at h
    nlinarith only [h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show c ^ 2 = (1 : ℝ) ^ 2 by simpa using hsq)
      with rfl | rfl
  · apply hopp
    simpa only [one_smul] using hc.symm
  · apply hsame
    simpa only [neg_one_smul, neg_neg] using hc.symm

end PoincareConjecture
