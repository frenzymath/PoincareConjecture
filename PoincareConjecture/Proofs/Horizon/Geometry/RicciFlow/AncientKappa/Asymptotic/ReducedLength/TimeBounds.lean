import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.RegularMeasure
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.TimeCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

namespace AncientAsymptoticSolitonPredecessors

theorem regular_reducedLength_deriv_lower {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    -2 * reducedLength K.flow 0 p q τ / τ ≤
      deriv (fun s => reducedLength K.flow 0 p q s) τ := by
  have heq : (fun s => reducedLength K.flow 0 p q s) =ᶠ[𝓝 τ]
      (fun s => r.representative (q, s)) := by
    have hnb := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (r.neighborhood_open.mem_nhds r.center_mem)
    filter_upwards [hnb] with s hs
    exact (r.representative_eq (q, s) hs).symm
  obtain ⟨d, hd⟩ := r.representative_time_derivative
  rw [(hd.congr_of_eventuallyEq heq).deriv, ← hd.deriv]
  exact P.regular_reducedLength_time_lower r

theorem reducedLength_absolutelyContinuous {K : AncientKappaSolution n M}
    {R : ℝ} {p : M} (D : ReducedLengthMeasureData K.flow 0 R p)
    (q : M) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < R) :
    AbsolutelyContinuousOnInterval (fun τ => reducedLength K.flow 0 p q τ) a b := by
  let g := K.flow.metric 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hlocD : LocallyLipschitzOn (univ ×ˢ Ioo 0 R)
      (fun z : M × ℝ => reducedLength K.flow 0 p z.1 z.2) := D.locally_lipschitz
  have hloc : LocallyLipschitzOn (Icc a b)
      (fun τ => reducedLength K.flow 0 p q τ) := by
    intro τ hτ
    have htime : τ ∈ Ioo 0 R := ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩
    obtain ⟨L, U, hU, hL⟩ := hlocD (x := (q, τ)) ⟨mem_univ q, htime⟩
    have hU' : U ∈ 𝓝 (q, τ) := by
      rwa [nhdsWithin_eq_nhds.mpr ((isOpen_univ.prod isOpen_Ioo).mem_nhds
        ⟨mem_univ q, htime⟩)] at hU
    refine ⟨L, (fun s => (q, s)) ⁻¹' U, ?_, ?_⟩
    · exact mem_nhdsWithin_of_mem_nhds
        ((continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hU')
    · simpa only [mul_one, Function.comp_def] using
        hL.comp (LipschitzWith.prodMk_left q).lipschitzOnWith (mapsTo_preimage _ _)
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_Icc
  exact (show LipschitzOnWith L (fun τ => reducedLength K.flow 0 p q τ) (uIcc a b) by
    simpa only [uIcc_of_le hab] using hL).absolutelyContinuousOnInterval

theorem reducedLength_weighted_time_le {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) (p q : M)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    reducedLength K.flow 0 p q a * a ^ 2 ≤
      reducedLength K.flow 0 p q b * b ^ 2 := by
  obtain ⟨V⟩ := P.reduced_volume (b + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  have hae : ∀ᵐ x ∂calibratedMetricVolume (K.flow.metric 0),
      reducedLength K.flow 0 p x a * a ^ 2 ≤
        reducedLength K.flow 0 p x b * b ^ 2 := by
    filter_upwards [P.ae_regular_worldline D] with x hx
    have hsub : Ioo a b ⊆ Ioo 0 (b + 1) :=
      fun τ hτ => ⟨ha.trans hτ.1, by linarith [hτ.2]⟩
    have hreg : ∀ᵐ τ ∂volume.restrict (Ioo a b), (x, τ) ∈ D.regularDomain :=
      hx.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    apply weighted_time_le_of_deriv_lower ha hab
      (reducedLength_absolutelyContinuous D x ha hab (by linarith))
    filter_upwards [hreg] with τ hτ
    obtain ⟨r⟩ := D.regular_points (x, τ) hτ
    exact P.regular_reducedLength_deriv_lower r
  have hclosed : IsClosed {x : M | reducedLength K.flow 0 p x a * a ^ 2 ≤
      reducedLength K.flow 0 p x b * b ^ 2} :=
    isClosed_le ((P.continuous_reducedLength p a ha).mul continuous_const)
      ((P.continuous_reducedLength p b (ha.trans_le hab)).mul continuous_const)
  exact hclosed.closure_subset_iff.mpr (fun _ h => h)
    ((calibratedMetricVolume (K.flow.metric 0)).dense_of_ae hae q)

theorem reducedLength_time_le {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) (p q : M)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    reducedLength K.flow 0 p q a ≤
      reducedLength K.flow 0 p q b * b ^ 2 / a ^ 2 := by
  exact (le_div_iff₀ (pow_pos ha 2)).mpr
    (P.reducedLength_weighted_time_le p q ha hab)

end AncientAsymptoticSolitonPredecessors

namespace AncientRescalingSequence

theorem scalar_at_base_time_le {K : AncientKappaSolution n M}
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) (σ : ℝ) (hσ : 0 < σ) (hσone : σ ≤ 1) :
    ((S.rescaling k).flow.connection (-σ)).scalarCurvature (S.base k) ≤
      3 * (n : ℝ) / (2 * σ ^ 3) := by
  have hs := S.scale_pos k
  have ha : 0 < S.scale k * σ := mul_pos hs hσ
  have hab : S.scale k * σ ≤ S.scale k := by nlinarith
  have hl := P.reducedLength_weighted_time_le S.reference (S.base k) ha hab
  have hbase := mul_le_mul_of_nonneg_right (S.base_reduced_length_bound k)
    (sq_nonneg (S.scale k))
  have hlength : reducedLength K.flow 0 S.reference (S.base k) (S.scale k * σ) * σ ^ 2 ≤
      (n : ℝ) / 2 := by
    apply (mul_le_mul_iff_right₀ (pow_pos hs 2)).mp
    nlinarith [hl.trans hbase]
  have hscalar := P.scalar_le_reducedLength S.reference (S.base k) (S.scale k * σ) ha
  have hscalar_mul := mul_le_mul_of_nonneg_right ((le_div_iff₀ ha).mp hscalar)
    (sq_nonneg σ)
  rw [(S.rescaling k).scalar_scale (-σ) (by linarith)]
  rw [show S.scale k * (-σ) = 0 - (S.scale k * σ) by ring]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (pow_pos hσ 3))).mpr
  nlinarith

end AncientRescalingSequence

end PoincareConjecture
