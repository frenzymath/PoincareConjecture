import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConvexCornerReturn

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_convex_corner_arrival_nonneg
    {eta : ℝ → AnnulusCoordinates} {u T : ℝ}
    (he : ContDiff ℝ ∞ eta) (huT : u < T)
    {S : Set AnnulusCoordinates} (hconf : MapsTo eta (Ioo u T) S)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap (eta T))
    (hzero : phi (eta T) = 0)
    (hcorner : ∀ᶠ z in 𝓝 (eta T), z ∈ S → 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) :
    0 ≤ (L (-deriv eta T)).1 ∧ 0 ≤ (L (-deriv eta T)).2 := by
  have hd : HasDerivAt (phi ∘ eta) (L (deriv eta T)) T :=
    hphi.comp_hasDerivAt T ((he.differentiable (by simp) T).hasDerivAt)
  have hn : ∀ᶠ t in 𝓝[<] T, eta t ∈ S →
      0 ≤ (phi (eta t)).1 ∧ 0 ≤ (phi (eta t)).2 :=
    (he.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually hcorner
  have hnonpos : L (deriv eta T) ≤ (0 : ℝ × ℝ) := by
    apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
    filter_upwards [hn, Ioo_mem_nhdsLT huT] with t ht htu
    have hq := ht (hconf htu)
    change (t - T)⁻¹ • (phi (eta t) - phi (eta T)) ≤ (0 : ℝ × ℝ)
    rw [hzero, sub_zero]
    exact ⟨mul_nonpos_of_nonpos_of_nonneg (inv_lt_zero'.mpr (sub_neg.mpr htu.2)).le hq.1,
      mul_nonpos_of_nonpos_of_nonneg (inv_lt_zero'.mpr (sub_neg.mpr htu.2)).le hq.2⟩
  constructor
  · simpa only [map_neg, Prod.fst_neg] using neg_nonneg.mpr hnonpos.1
  · simpa only [map_neg, Prod.snd_neg] using neg_nonneg.mpr hnonpos.2

theorem m64Intrinsic_interior_geodesic_arrival_not_positive_multiple
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha eta : ℝ → AnnulusCoordinates} {A u T c : ℝ}
    (ha : ContDiff ℝ ∞ alpha)
    (hA : 0 < A) (huT : u < T) (hc : 0 < c)
    (hageo : G.IsGeodesicOn alpha (Icc 0 A))
    (hegeo : G.IsGeodesicOn eta (Icc u T))
    (hmeet : eta T = alpha A)
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hside : MapsTo alpha (Icc 0 A) (frontier U)) (hinside : MapsTo eta (Ioo u T) U) :
    deriv eta T ≠ c • deriv alpha A := by
  intro hvel
  let zeta := fun t : ℝ => alpha (c * t + (A - c * T))
  have hparameter : c * T + (A - c * T) = A := by ring
  have hzetaT : zeta T = alpha A := by dsimp only [zeta]; rw [hparameter]
  have hdalpha : HasDerivAt alpha (deriv alpha A) (c * T + (A - c * T)) := by
    rw [hparameter]
    exact (ha.differentiable (by simp) A).hasDerivAt
  have hdzeta : HasDerivAt zeta (c • deriv alpha A) T := by
    simpa only [zeta, Function.comp_def, id_eq, mul_one] using!
      hdalpha.scomp T (((hasDerivAt_id T).const_mul c).add_const (A - c * T))
  have heg : G.IsGeodesicOn eta {T} := by
    intro t ht
    have heq : t = T := ht
    subst t
    exact hegeo T ⟨huT.le, le_rfl⟩
  have hzg : G.IsGeodesicOn zeta {T} := by
    intro t ht
    have heq : t = T := ht
    subst t
    apply hageo.comp_affine c (A - c * T)
    simpa only [mem_preimage, hparameter] using (right_mem_Icc.mpr hA.le)
  have hagree : eta =ᶠ[𝓝 T] zeta :=
    heg.eq_nhds_of_initial_data hzg (mem_singleton T) (eta T) (by simp)
      (hmeet.trans hzetaT.symm) (by
        simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using
          hvel.trans hdzeta.deriv.symm)
  have hparamLimit : Tendsto (fun t : ℝ => c * t + (A - c * T)) (𝓝[<] T) (𝓝 A) := by
    have hcont : ContinuousAt (fun t : ℝ => c * t + (A - c * T)) T := by fun_prop
    simpa only [hparameter] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ⟨ht, htu⟩, htpos⟩ :=
    ((hagree.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT huT) |>.and
      (hparamLimit.eventually_const_lt hA)).exists
  have htA : c * t + (A - c * T) < A := by nlinarith [htu.2, hc]
  have hfront : eta t ∈ frontier U := by
    rw [ht]
    exact hside ⟨htpos.le, htA.le⟩
  exact (show eta t ∉ U by simpa only [hU.interior_eq] using hfront.2) (hinside htu)

end PoincareConjecture
