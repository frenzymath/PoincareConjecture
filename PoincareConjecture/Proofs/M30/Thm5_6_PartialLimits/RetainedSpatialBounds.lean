import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ReferenceChartBounds
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ClosedSpatialJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormBounds














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 1200000 in




theorem exists_eventually_retained_closed_spatial_bounds
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    {S : PointedFlowSequence 3 (-T / 2) (T / 2)}
    (G : PointedGeometricConvergence S)
    (Fsrc : ∀ k : ℕ, RicciFlow 3 (S.carrier k).carrier (Icc (-T) 0))
    (hmetric : ∀ (k : ℕ) (t : ℝ),
      (Fsrc k).metric t = (S.flow k).flow.metric (t + T / 2))
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target) :
    let e := fun (k : ℕ) =>
      (fun y : G.limitCarrier.carrier => ((G.embedding k).toFun (0, y)).2) ∘
        (extChartAt (𝓡 3) q).symm
    let A := fun (k : ℕ) (t : ℝ) =>
      ((Fsrc (G.subsequence k)).metric t).pullbackCoefficients (e k)
    (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Icc (-T) 0, ∀ x ∈ K,
        ((Fsrc (G.subsequence k)).connection t).curvatureDerivativeNorm j (e k x) ≤ C) →
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      (∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-T) 0, ∀ x ∈ K,
        ∀ v : EuclideanSpace ℝ (Fin 3),
          α * ‖v‖ ^ 2 ≤ A k t x v v ∧ A k t x v v ≤ β * ‖v‖ ^ 2) ∧
      (∀ d : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
        ∀ x ∈ K, ∀ j : ℕ, j ≤ d →
          (∀ t ∈ Icc (-T) 0, ‖iteratedFDeriv ℝ j (A k t) x‖ ≤ B) ∧
          (∀ s ∈ Icc (-T) 0, ∀ t ∈ Icc (-T) 0,
            ‖iteratedFDeriv ℝ j (A k t) x - iteratedFDeriv ℝ j (A k s) x‖ ≤
              B * |t - s|)) := by
  classical
  intro e A hcurv
  have hzero : -T / 2 < 0 ∧ 0 < T / 2 := ⟨by linarith, by linarith⟩
  have hr : -T / 2 ∈ Ioo (-T) (0 : ℝ) := ⟨by linarith, by linarith⟩
  have hrc : -T / 2 ∈ Icc (-T) (0 : ℝ) := Ioo_subset_Icc_self hr
  have href (k : ℕ) : (Fsrc k).metric (-T / 2) = (S.flow k).flow.metric 0 := by
    rw [hmetric]
    congr 1
    ring
  choose C hC hcurvC using hcurv
  have hreference (j : ℕ) : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ j (A k (-T / 2)) x‖ ≤ Z := by
    obtain ⟨Z, hZ, hbound⟩ :=
      exists_eventually_reference_spatial_jet_bound G hzero q hK hKc j
    refine ⟨Z, hZ, ?_⟩
    filter_upwards [hbound] with k hk x hx
    dsimp only [A]
    rw [href]
    exact hk x hx
  choose Z _hZ hreferenceZ using hreference
  obtain ⟨α₀, β₀, hα₀, hβ₀, hell₀⟩ :=
    exists_eventually_reference_ellipticity G hzero q hK hKc
  have hellref : ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3),
      α₀ * ‖v‖ ^ 2 ≤ A k (-T / 2) x v v ∧
        A k (-T / 2) x v v ≤ β₀ * ‖v‖ ^ 2 := by
    filter_upwards [hell₀] with k hk x hx v
    dsimp only [A]
    rw [href]
    exact hk x hx v
  let L : ℝ := 27 * C 0
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (hC 0)
  let α : ℝ := Real.exp (-(2 * L) * T) * α₀
  let β : ℝ := Real.exp ((2 * L) * T) * β₀
  have hα : 0 < α := mul_pos (Real.exp_pos _) hα₀
  have hβ : 0 < β := mul_pos (Real.exp_pos _) hβ₀
  have hell : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-T) 0, ∀ x ∈ K,
      ∀ v : EuclideanSpace ℝ (Fin 3),
        α * ‖v‖ ^ 2 ≤ A k t x v v ∧ A k t x v v ≤ β * ‖v‖ ^ 2 := by
    filter_upwards [hcurvC 0, hellref] with k hk hkr t ht x hx v
    let F := Fsrc (G.subsequence k)
    let p := e k x
    let w := mfderiv (𝓡 3) (𝓡 3) (e k) x v
    have hQ (s : ℝ) : 0 ≤ (F.metric s).inner p w w := by
      by_cases hw : w = 0
      · rw [hw]
        simp only [map_zero, le_refl]
      · exact ((F.metric s).pos p w hw).le
    have hRic (s : ℝ) (hs : s ∈ Icc (-T) 0) :
        |(F.connection s).ricci p w w| ≤ L * (F.metric s).inner p w w := by
      have hRm : (F.connection s).curvatureTensorNorm p ≤ C 0 := by
        simpa only [LeviCivitaData.horizon_curvatureDerivativeNorm_zero] using hk s hs x hx
      have hnorm := (F.connection s).abs_ricci_quadratic_le_curvatureTensorNorm p w
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) p) = 3 :=
        finrank_euclideanSpace_fin
      norm_num only [Fintype.card_fin, hdim] at hnorm
      exact hnorm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRm (by norm_num)) (hQ s))
    have hcomparison := F.metric_inner_self_exp_bounds (convex_Icc (-T) 0)
      (Subset.refl _) p w L hRic hrc ht
    have hdisplacement : |t - (-T / 2)| ≤ T :=
      abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hlow : Real.exp (-(2 * L) * T) ≤
        Real.exp (-(2 * L) * |t - (-T / 2)|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hdisplacement (by linarith))
    have hupp : Real.exp ((2 * L) * |t - (-T / 2)|) ≤ Real.exp ((2 * L) * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdisplacement (by positivity))
    have hreference := hkr x hx v
    change α₀ * ‖v‖ ^ 2 ≤ (F.metric (-T / 2)).inner p w w ∧
      (F.metric (-T / 2)).inner p w w ≤ β₀ * ‖v‖ ^ 2 at hreference
    change α * ‖v‖ ^ 2 ≤ (F.metric t).inner p w w ∧
      (F.metric t).inner p w w ≤ β * ‖v‖ ^ 2
    constructor
    · calc
        α * ‖v‖ ^ 2 = Real.exp (-(2 * L) * T) * (α₀ * ‖v‖ ^ 2) := by
          dsimp only [α]
          ring
        _ ≤ Real.exp (-(2 * L) * T) * (F.metric (-T / 2)).inner p w w :=
          mul_le_mul_of_nonneg_left hreference.1 (Real.exp_nonneg _)
        _ ≤ Real.exp (-(2 * L) * |t - (-T / 2)|) *
            (F.metric (-T / 2)).inner p w w :=
          mul_le_mul_of_nonneg_right hlow (hQ (-T / 2))
        _ ≤ (F.metric t).inner p w w := hcomparison.1
    · calc
        (F.metric t).inner p w w ≤ Real.exp ((2 * L) * |t - (-T / 2)|) *
            (F.metric (-T / 2)).inner p w w := hcomparison.2
        _ ≤ Real.exp ((2 * L) * T) * (F.metric (-T / 2)).inner p w w :=
          mul_le_mul_of_nonneg_right hupp (hQ (-T / 2))
        _ ≤ Real.exp ((2 * L) * T) * (β₀ * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hreference.2 (Real.exp_nonneg _)
        _ = β * ‖v‖ ^ 2 := by
          dsimp only [β]
          ring
  let c := extChartAt (𝓡 3) q
  let ψ (k : ℕ) : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
    fun y => ((G.embedding k).toFun (0, y)).2
  let U (k : ℕ) : Set (EuclideanSpace ℝ (Fin 3)) :=
    c.target ∩ c.symm ⁻¹' G.exhaustion k
  have hU (k : ℕ) : IsOpen (U k) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓡 3) q) (G.exhaustion_open k)
  have hchart {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hspatial (k : ℕ) {y : EuclideanSpace ℝ (Fin 3)}
      (hy : c.symm y ∈ G.exhaustion k) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (ψ k) (c.symm y) :=
    (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hy
  have he (k : ℕ) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e k) (U k) := by
    intro y hy
    exact ((hspatial k hy.2).comp y (hchart hy.1)).contMDiffWithinAt
  have hi (k : ℕ) (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U k) :
      (mfderiv (𝓡 3) (𝓡 3) (e k) y).IsInvertible := by
    have hbij := (G.embedding k).spatialMap_mfderiv_bijective
      (G.exhaustion_open k) hzero hy.2
    let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      mfderiv (𝓡 3) (𝓡 3) (ψ k) (c.symm y)
    have hD : D.IsInvertible :=
      ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hbij.1)
        (LinearMap.range_eq_top.mpr hbij.2), rfl⟩
    have hc : (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hy.1
    change (mfderiv (𝓡 3) (𝓡 3) (ψ k ∘ c.symm) y).IsInvertible
    rw [mfderiv_comp y ((hspatial k hy.2).mdifferentiableAt (by simp))
      ((hchart hy.1).mdifferentiableAt (by simp))]
    exact hD.comp hc
  have hcK : ContinuousOn c.symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨k₀, hk₀⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hcK)
  refine ⟨α, β, hα, hβ, hell, ?_⟩
  intro d
  obtain ⟨B, hB, hbound⟩ := exists_closed_spatialJet_time_lipschitz_constant.{0}
    3 d C Z hC hα hβ.le
  have hcurvFinite := Filter.eventually_all.mpr (fun j : Fin (d + 1) => hcurvC (j : ℕ))
  have hrefFinite := Filter.eventually_all.mpr (fun j : Fin (d + 1) => hreferenceZ (j : ℕ))
  refine ⟨B, hB, ?_⟩
  filter_upwards [hell, hcurvFinite, hrefFinite, eventually_ge_atTop k₀]
    with k hk hck hzk hstage x hx j hj
  have hxU : x ∈ U k :=
    ⟨hKc hx, G.exhaustion_monotone hstage (hk₀ (mem_image_of_mem _ hx))⟩
  exact hbound hT hT1 (Fsrc (G.subsequence k)) (hU k) (he k) (hi k) hr hxU
    (fun t ht v => hk t ht x hx v)
    (fun i hi t ht => hck ⟨i, Nat.lt_succ_of_le hi⟩ t ht x hx)
    (fun i hi => hzk ⟨i, Nat.lt_succ_of_le hi⟩ x hx) j hj

end PoincareConjecture.M30
