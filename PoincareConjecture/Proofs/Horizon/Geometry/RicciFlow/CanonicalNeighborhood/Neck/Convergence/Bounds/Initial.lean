import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Model

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
open Set Filter
open scoped Manifold ContDiff Topology
namespace PoincareConjecture.PointedGeometricConvergence
attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem eventually_contDiffAt_cylinder_parametrizedCoefficients
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (t : ℝ) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) :
    ∀ᶠ i in atTop, ∀ q : UnitTwoSphere, ∀ x ∈ K,
      ContDiffAt ℝ ∞
        (((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
          (fun y => ((G.embedding i).toFun
            (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))).2)) x := by
  have hcompact : IsCompact (univ ×ˢ (Prod.snd '' K) : Set RoundCylinderSpace) :=
    isCompact_univ.prod (hK.image continuous_snd)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hcompact.image hΦ.continuous)
  filter_upwards [eventually_ge_atTop j] with i hji q x hx
  have hmem : Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x.1, x.2) ∈
      G.exhaustion i := G.exhaustion_monotone hji
    (hj (mem_image_of_mem Φ ⟨mem_univ _, mem_image_of_mem Prod.snd hx⟩))
  have hmap := ((G.embedding i).spatialMap_contMDiffAt
    (G.exhaustion_open i) hzero hmem).comp x
      ((hΦ.comp (cylinderChart_symm_smooth q)) x)
  exact ((S.flow (G.subsequence i)).metricAt t).contDiffAt_parametrizedCoefficients hmap

theorem exists_eventual_cylinder_parametrized_jet_bound
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K)
    (hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ)
    {rmin : ℝ} (hrmin : 0 < rmin) (m : ℕ) :
    ∃ Z : ℝ, 0 ≤ Z ∧
      ∀ {a b : ℝ} {S : PointedFlowSequence 3 a b}
        (G : PointedGeometricConvergence S) (_hzero : a < 0 ∧ 0 < b)
        {Φ : RoundCylinderSpace → G.limitCarrier.carrier},
        ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ →
        ∀ {t : ℝ}, t ∈ Ioo a b → ∀ {s₀ : ℝ}, rmin ≤ s₀ →
        (fun z v w => s₀ * roundCylinderPullback (G.limitFlow.metricAt t) Φ z v w) =
          EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop, ∀ q : UnitTwoSphere, ∀ x ∈ K,
          ‖iteratedFDeriv ℝ m
            (((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
              (fun y => ((G.embedding i).toFun
                (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))).2)) x‖ ≤ Z := by
  obtain ⟨Z, hZ, hbound⟩ := exists_roundCylinderModelCoefficients_jet_bound hK m
  refine ⟨rmin⁻¹ * Z + 1, by positivity, ?_⟩
  intro a b S G hzero Φ hΦ t ht s₀ hrs hround
  have hs₀ : 0 < s₀ := hrmin.trans_le hrs
  have hconv := G.tendstoUniformlyOn_cylinder_parametrized_error_jets
    hzero hΦ ht m hK hKU
  have hevent := (Metric.tendstoUniformlyOn_iff.mp hconv) 1 (by norm_num)
  filter_upwards [G.eventually_contDiffAt_cylinder_parametrizedCoefficients hzero hΦ t hK,
    hevent] with i hi he q x hx
  let f : RoundCylinderCoordinates → G.limitCarrier.carrier :=
    fun y => Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)
  let A := ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
    (fun y => ((G.embedding i).toFun (0, f y)).2)
  let A₀ := (G.limitFlow.metricAt t).parametrizedCoefficients f
  have hA : ContDiffAt ℝ ∞ A x := hi q x hx
  have hA₀ : ContDiffAt ℝ ∞ A₀ x :=
    (G.limitFlow.metricAt t).contDiffAt_parametrizedCoefficients
      ((hΦ.comp (cylinderChart_symm_smooth q)) x)
  have herror : ‖iteratedFDeriv ℝ m (A - A₀) x‖ < 1 := by
    simpa only [dist_zero_left, A, A₀, f, Pi.sub_def] using
      he (q, x) ⟨mem_univ _, hx⟩
  rw [iteratedFDeriv_sub_apply (hA.of_le (by exact_mod_cast le_top))
    (hA₀.of_le (by exact_mod_cast le_top))] at herror
  have hmodel : A₀ = s₀⁻¹ • roundCylinderModelCoefficients := by
    funext y
    exact (eq_inv_smul_iff₀ hs₀.ne').mpr
      (parametrizedCoefficients_cylinder_of_normalized_pullback
        (G.limitFlow.metricAt t) hΦ s₀ hround q y)
  have hlim : ‖iteratedFDeriv ℝ m A₀ x‖ ≤ rmin⁻¹ * Z := by
    rw [hmodel, iteratedFDeriv_const_smul_apply
      (contDiff_roundCylinderModelCoefficients.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hs₀.le)]
    exact mul_le_mul (inv_anti₀ hrmin hrs) (hbound x hx)
      (norm_nonneg _) (by positivity)
  change ‖iteratedFDeriv ℝ m A x‖ ≤ _
  calc
    _ ≤ ‖iteratedFDeriv ℝ m A x - iteratedFDeriv ℝ m A₀ x‖ +
        ‖iteratedFDeriv ℝ m A₀ x‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + rmin⁻¹ * Z := add_le_add herror.le hlim
    _ = _ := by ring

theorem exists_eventual_cylinder_parametrized_jet_bounds
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K)
    (hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ)
    {rmin : ℝ} (hrmin : 0 < rmin) :
    ∃ Z : ℕ → ℝ, (∀ m, 0 ≤ Z m) ∧
      ∀ {a b : ℝ} {S : PointedFlowSequence 3 a b}
        (G : PointedGeometricConvergence S), a < 0 ∧ 0 < b →
        ∀ {Φ : RoundCylinderSpace → G.limitCarrier.carrier},
        ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ →
        ∀ {t : ℝ}, t ∈ Ioo a b → ∀ {s₀ : ℝ}, rmin ≤ s₀ →
        (fun z v w => s₀ * roundCylinderPullback (G.limitFlow.metricAt t) Φ z v w) =
          EvolvingRoundCylinderMetric 0 →
        ∀ d : ℕ, ∀ᶠ i in atTop, ∀ m ≤ d, ∀ q : UnitTwoSphere, ∀ x ∈ K,
          ‖iteratedFDeriv ℝ m
            (((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
              (fun y => ((G.embedding i).toFun
                (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))).2)) x‖ ≤ Z m := by
  choose Z hZ hbound using fun m =>
    exists_eventual_cylinder_parametrized_jet_bound hK hKU hrmin m
  refine ⟨Z, hZ, ?_⟩
  intro a b S G hzero Φ hΦ t ht s₀ hrs hround d
  exact (eventually_all_finite (finite_Iic d)).mpr
    (fun m _ => hbound m G hzero hΦ ht hrs hround)

theorem eventually_cylinder_parametrized_center_ellipticity
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    {t : ℝ} (ht : t ∈ Ioo a b) {rmin rmax s₀ : ℝ}
    (hrmin : 0 < rmin) (hmin : rmin ≤ s₀) (hmax : s₀ ≤ rmax)
    (hround : (fun z v w => s₀ * roundCylinderPullback (G.limitFlow.metricAt t) Φ z v w) =
      EvolvingRoundCylinderMetric 0)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∀ᶠ i in atTop, ∀ q : UnitTwoSphere, ∀ r ∈ J, ∀ v : RoundCylinderCoordinates,
      let A := ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
        (fun y => ((G.embedding i).toFun
          (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))).2) (0, r)
      (rmax⁻¹ / 2) * ‖v‖ ^ 2 ≤ A v v ∧
        A v v ≤ (3 * rmin⁻¹ + 1) * ‖v‖ ^ 2 := by
  have hs₀ : 0 < s₀ := hrmin.trans_le hmin
  have hrmax : 0 < rmax := hs₀.trans_le hmax
  let K : Set RoundCylinderCoordinates := {0} ×ˢ J
  have hK : IsCompact K := isCompact_singleton.prod hJ
  have hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ := by
    intro x hx
    have hx0 : x.1 = 0 := hx.1
    exact ⟨by rw [hx0]; exact Metric.mem_ball_self (by norm_num), mem_univ _⟩
  let θ : ℝ := min (rmax⁻¹ / 2) 1
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hconv := G.tendstoUniformlyOn_cylinder_parametrized_error_jets
    hzero hΦ ht 0 hK hKU
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) θ hθ] with i hi q r hr v
  let f : RoundCylinderCoordinates → G.limitCarrier.carrier :=
    fun y => Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)
  let A := ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
    (fun y => ((G.embedding i).toFun (0, f y)).2) (0, r)
  let A₀ := (G.limitFlow.metricAt t).parametrizedCoefficients f (0, r)
  have herror : ‖A - A₀‖ ≤ θ := by
    have h := hi (q, (0, r)) ⟨mem_univ _, by exact ⟨rfl, hr⟩⟩
    have hlt : ‖A - A₀‖ < θ := by
      simpa only [dist_zero_left, norm_iteratedFDeriv_zero] using h
    exact hlt.le
  have heval : |A v v - A₀ v v| ≤ θ * ‖v‖ ^ 2 := by
    have h := (A - A₀).le_of_opNorm₂_le_of_le herror (le_refl ‖v‖) (le_refl ‖v‖)
    simpa only [sub_apply, Real.norm_eq_abs, pow_two, mul_assoc] using h
  have hmodel : A₀ = s₀⁻¹ • roundCylinderModelCoefficients (0, r) :=
    (eq_inv_smul_iff₀ hs₀.ne').mpr
      (parametrizedCoefficients_cylinder_of_normalized_pullback
        (G.limitFlow.metricAt t) hΦ s₀ hround q (0, r))
  have hlower : rmax⁻¹ * ‖v‖ ^ 2 ≤ A₀ v v := by
    rw [hmodel]
    change _ ≤ s₀⁻¹ * roundCylinderModelCoefficients (0, r) v v
    exact (mul_le_mul_of_nonneg_right (inv_anti₀ hs₀ hmax) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (roundCylinderModelCoefficients_center_quadratic_bounds r v).1
        (inv_nonneg.mpr hs₀.le))
  have hupper : A₀ v v ≤ 3 * rmin⁻¹ * ‖v‖ ^ 2 := by
    rw [hmodel]
    change s₀⁻¹ * roundCylinderModelCoefficients (0, r) v v ≤ _
    calc
      _ ≤ s₀⁻¹ * (3 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (roundCylinderModelCoefficients_center_quadratic_bounds r v).2
          (inv_nonneg.mpr hs₀.le)
      _ ≤ rmin⁻¹ * (3 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hrmin hmin) (by positivity)
      _ = _ := by ring
  have he := abs_le.mp heval
  have hθlo := mul_le_mul_of_nonneg_right (min_le_left (rmax⁻¹ / 2) 1) (sq_nonneg ‖v‖)
  have hθhi := mul_le_mul_of_nonneg_right (min_le_right (rmax⁻¹ / 2) 1) (sq_nonneg ‖v‖)
  change (rmax⁻¹ / 2) * ‖v‖ ^ 2 ≤ A v v ∧ A v v ≤ _
  constructor <;> dsimp only [θ] at he <;> nlinarith [he.1, he.2]

theorem eventually_cylinder_parametrized_model_error_jets
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    {t : ℝ} (ht : t ∈ Ioo a b) {s : ℝ} (hs : 0 < s)
    (hround : (fun z v w => s * roundCylinderPullback (G.limitFlow.metricAt t) Φ z v w) =
      EvolvingRoundCylinderMetric 0)
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K)
    (hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ)
    (d : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ i in atTop, ∀ j ≤ d, ∀ q : UnitTwoSphere, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j
          (((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
            (fun y => ((G.embedding i).toFun
              (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))).2)) x -
        s⁻¹ • iteratedFDeriv ℝ j roundCylinderModelCoefficients x‖ ≤ η := by
  have herror : ∀ᶠ i in atTop, ∀ j ≤ d, ∀ q : UnitTwoSphere, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun y =>
          ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
            (fun z => ((G.embedding i).toFun
              (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z.1, z.2))).2) y -
          (G.limitFlow.metricAt t).parametrizedCoefficients
            (fun z => Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z.1, z.2)) y) x‖ ≤ η := by
    apply (eventually_all_finite (finite_Iic d)).mpr
    intro j _
    have hconv := G.tendstoUniformlyOn_cylinder_parametrized_error_jets hzero hΦ ht j hK hKU
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) η hη] with i hi q x hx
    simpa only [dist_zero_left] using (hi (q, x) ⟨mem_univ _, hx⟩).le
  filter_upwards [herror, G.eventually_contDiffAt_cylinder_parametrizedCoefficients
    hzero hΦ t hK] with i hi hsmooth j hj q x hx
  let f : RoundCylinderCoordinates → G.limitCarrier.carrier :=
    fun y => Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)
  let A := ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
    (fun y => ((G.embedding i).toFun (0, f y)).2)
  let A₀ := (G.limitFlow.metricAt t).parametrizedCoefficients f
  have hA : ContDiffAt ℝ ∞ A x := hsmooth q x hx
  have hA₀ : ContDiffAt ℝ ∞ A₀ x :=
    (G.limitFlow.metricAt t).contDiffAt_parametrizedCoefficients
      ((hΦ.comp (cylinderChart_symm_smooth q)) x)
  have h := hi j hj q x hx
  change ‖iteratedFDeriv ℝ j (A - A₀) x‖ ≤ η at h
  rw [iteratedFDeriv_sub_apply (hA.of_le (by exact_mod_cast le_top))
    (hA₀.of_le (by exact_mod_cast le_top))] at h
  have hmodel : A₀ = s⁻¹ • roundCylinderModelCoefficients := by
    funext y
    exact (eq_inv_smul_iff₀ hs.ne').mpr
      (parametrizedCoefficients_cylinder_of_normalized_pullback
        (G.limitFlow.metricAt t) hΦ s hround q y)
  rw [hmodel, iteratedFDeriv_const_smul_apply
    (contDiff_roundCylinderModelCoefficients.contDiffAt.of_le (by exact_mod_cast le_top))] at h
  exact h

end PoincareConjecture.PointedGeometricConvergence
