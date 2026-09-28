import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.InitialJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.Centered
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.TailTimeControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.PairwiseMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.LateControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem regularNeckCenteredLift_normalized_jet
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {t ε : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
    (N : GeneralizedStrongNeck F t ε) (hε : ε < 1 / 2) (x₀ : H.regularRegion P04)
    (hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) (j : ℕ) :
    iteratedFDeriv ℝ j ((normalizedNeckMetric (N.spatialNeck hε)).pullbackCoefficients
        (centeredNeckLift (N.spatialNeck hε) z.1 z.2)) 0 =
      (F.connection t).scalarCurvature N.center •
        iteratedFDeriv ℝ j (((H.terminalFlow P04).metric t).pullbackCoefficients
          (H.regularNeckCenteredLift P04 ht N hε x₀ z)) 0 := by
  rw [H.regularNeckCenteredLift_metric_jet P04 ht N hε x₀ hcapture z hz]
  have heq : (normalizedNeckMetric (N.spatialNeck hε)).pullbackCoefficients
      (centeredNeckLift (N.spatialNeck hε) z.1 z.2) =
      fun y => (F.connection t).scalarCurvature N.center •
        (F.metric t).pullbackCoefficients (centeredNeckLift (N.spatialNeck hε) z.1 z.2) y := by
    funext y
    ext v w
    rfl
  rw [heq]
  apply iteratedFDeriv_const_smul_apply'
  exact ((F.metric t).contDiffAt_pullbackCoefficients
    (centeredNeckLift_contMDiffAt (N.spatialNeck hε) z.1 z.2
      (zero_mem_centeredNeckDomain (N.spatialNeck hε) hz))).of_le
    (by exact_mod_cast le_top)

theorem exists_uniform_neck_coordinate_tail_bound
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hε : H.epsilon ≤ 1 / 200)
    (x₀ : H.regularRegion P04) (hQ : 0 < (H.terminalConnection P04).scalarCurvature x₀)
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (m : ℕ) (hm : m ≤ ⌊H.epsilon⁻¹⌋₊) :
    ∃ s B : ℝ, H.reference.tMinus < s ∧ s < T ∧ 0 ≤ B ∧
      ∀ t (ht : t ∈ Ico H.reference.tMinus T), s ≤ t →
        ∀ N : GeneralizedStrongNeck F t H.epsilon,
          N.center = H.reference.forward t ht x₀ →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-H.epsilon⁻¹) H.epsilon⁻¹ →
          ∀ r ∈ Icc t T, ∀ j ≤ m,
            ‖iteratedFDeriv ℝ j (((H.terminalFlow P04).metric r).pullbackCoefficients
                (H.regularNeckCenteredLift P04 ht N (by linarith) x₀ z)) 0 -
              iteratedFDeriv ℝ j (((H.terminalFlow P04).metric t).pullbackCoefficients
                (H.regularNeckCenteredLift P04 ht N (by linarith) x₀ z)) 0‖ ≤ B * (r - t) := by
  classical
  let Q := (H.terminalConnection P04).scalarCurvature x₀
  let l := Q / 2
  let u := 2 * Q
  have hl : 0 < l := by dsimp [l, Q]; positivity
  have hu : 0 < u := by dsimp [u, Q]; positivity
  have hscale : ∀ᶠ t in 𝓝[<] T,
      l < H.reference.scalar t x₀ ∧ H.reference.scalar t x₀ < u :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually
      (Ioo_mem_nhds (by dsimp [l, Q]; linarith) (by dsimp [u, Q]; linarith))
  obtain ⟨a, haT, hscale⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hscale
  obtain ⟨sK, hsK, hsKT, hcurv⟩ := H.exists_terminalFlow_curvature_derivative_tail_on_compact P04 hA
  choose K hK hcurv using hcurv
  obtain ⟨sG, hsG, hsGT, hmetric⟩ := H.exists_terminalFlow_pairwise_metric_tail P04 hA
  obtain ⟨Z, hZ, hinit⟩ := exists_centeredNeck_initial_jet_bound.{u} m
  obtain ⟨B, hB, htime⟩ := SpacetimeBounds.exists_closed_terminal_spatialJet_time_constant
    3 m K (fun _ => Z / l) (fun j => (hK j).le)
    (a := 1 / (8 * u)) (b := 12 / l) (by positivity) (by positivity)
  obtain ⟨s, hs, hsT⟩ := exists_between
    (max_lt hsKT (max_lt hsGT (max_lt haT (by linarith : T - 1 < T))))
  have hssK : sK < s := (le_max_left _ _).trans_lt hs
  have hssG : sG < s := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  have hsa : a < s := (le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs))
  have hsone : T - 1 < s := (le_max_right _ _).trans_lt
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs))
  refine ⟨s, B, hsK.trans hssK, hsT, hB, ?_⟩
  intro t ht hst N hcenter hNA z hz r hr j hj
  have hhalf : H.epsilon < 1 / 2 := by linarith
  let f := H.regularNeckCenteredLift P04 ht N hhalf x₀ z
  let U := centeredNeckDomain (N.spatialNeck hhalf) z.2
  have hU : IsOpen U := centeredNeckDomain_isOpen (N.spatialNeck hhalf) z.2
  have hzero : (0 : E) ∈ U := zero_mem_centeredNeckDomain (N.spatialNeck hhalf) hz
  have hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet := by
    intro y hy
    obtain ⟨w, _, hw⟩ := hNA (mem_image_of_mem _ hy)
    exact hw ▸ w.property
  have hf := H.regularNeckCenteredLift_smooth P04 ht N hhalf x₀ hcapture z
  have hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible :=
    fun _ hy => H.regularNeckCenteredLift_mfderiv_invertible P04 ht N hhalf x₀ hcapture z hy
  have hpointA : f 0 ∈ A := by
    obtain ⟨w, hw, heq⟩ := hNA (mem_image_of_mem _
      (centeredNeckLift_mem (N.spatialNeck hhalf) z.1 z.2 hzero))
    have heq' : f 0 = w := Subtype.ext
      ((H.regularNeckCenteredLift_val P04 ht N hhalf x₀ hcapture z hzero).trans heq.symm)
    exact heq'.symm ▸ hw
  let q := (F.connection t).scalarCurvature N.center
  have hq : 0 < q := N.scalar_center_pos
  have hqeq : q = H.reference.scalar t x₀ := by
    dsimp only [q]
    rw [hcenter, H.reference.scalar_pullback]
    rfl
  have hsc : l < q ∧ q < u := hqeq.symm ▸ hscale ⟨hsa.trans_le hst, ht.2⟩
  have htG : t ∈ Ico sG T := ⟨hssG.le.trans hst, ht.2⟩
  have hell : ∀ vtime ∈ Ico t T, ∀ v : E,
      (1 / (8 * u)) * ‖v‖ ^ 2 ≤
          ((H.terminalFlow P04).metric vtime).pullbackCoefficients f 0 v v ∧
        ((H.terminalFlow P04).metric vtime).pullbackCoefficients f 0 v v ≤
          (12 / l) * ‖v‖ ^ 2 := by
    intro vtime hvtime v
    have hquad := normalizedNeckMetric_centered_ellipticity (N.spatialNeck hhalf) hε z hz v
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ q * (F.metric t).pullbackCoefficients
        (centeredNeckLift (N.spatialNeck hhalf) z.1 z.2) 0 v v ∧
      q * (F.metric t).pullbackCoefficients (centeredNeckLift (N.spatialNeck hhalf) z.1 z.2)
        0 v v ≤ 3 * ‖v‖ ^ 2 at hquad
    rw [← H.regularNeckCenteredLift_coefficients P04 ht N hhalf x₀ hcapture z hzero] at hquad
    have hnonneg : 0 ≤ ((H.terminalFlow P04).metric t).pullbackCoefficients f 0 v v := by
      nlinarith [sq_nonneg ‖v‖]
    have hupper := mul_le_mul_of_nonneg_right hsc.2.le hnonneg
    have hlower := mul_le_mul_of_nonneg_right hsc.1.le hnonneg
    have hvG : vtime ∈ Ico sG T := ⟨htG.1.trans hvtime.1, hvtime.2⟩
    have htr := hmetric t htG vtime hvG _ hpointA (mfderiv (𝓡 3) (𝓡 3) f 0 v)
    have hrt := hmetric vtime hvG t htG _ hpointA (mfderiv (𝓡 3) (𝓡 3) f 0 v)
    change ((H.terminalFlow P04).metric t).pullbackCoefficients f 0 v v ≤
      4 * ((H.terminalFlow P04).metric vtime).pullbackCoefficients f 0 v v at htr
    change ((H.terminalFlow P04).metric vtime).pullbackCoefficients f 0 v v ≤
      4 * ((H.terminalFlow P04).metric t).pullbackCoefficients f 0 v v at hrt
    constructor
    · rw [one_div_mul_eq_div]
      apply (div_le_iff₀ (by positivity : 0 < 8 * u)).mpr
      nlinarith [mul_le_mul_of_nonneg_left htr hu.le]
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hl).mpr
      nlinarith [mul_le_mul_of_nonneg_left hrt hl.le]
  have hinit' : ∀ k ≤ m,
      ‖iteratedFDeriv ℝ k (((H.terminalFlow P04).metric t).pullbackCoefficients f) 0‖ ≤ Z / l := by
    intro k hk
    have h := hinit (N.spatialNeck hhalf) (by simpa using hε.trans (by norm_num)) hm z hz k hk
    rw [H.regularNeckCenteredLift_normalized_jet P04 ht N hhalf x₀ hcapture z hz,
      norm_smul, Real.norm_eq_abs, abs_of_pos N.scalar_center_pos] at h
    apply (le_div_iff₀ hl).mpr
    have hscale := mul_le_mul_of_nonneg_right hsc.1.le
      (norm_nonneg (iteratedFDeriv ℝ k (((H.terminalFlow P04).metric t).pullbackCoefficients f) 0))
    nlinarith
  exact htime (H.terminalFlow P04) hU hf hinv
    ((hsK.trans hssK).trans_le hst) ht.2 (by linarith) hzero hell
    (fun k _ vtime hvtime => hcurv k vtime
      ⟨hssK.le.trans (hst.trans hvtime.1), hvtime.2⟩ _ hpointA) hinit' r hr j hj

end PoincareConjecture.SingularTimeAssumptions
