import PoincareConjecture.Proofs.M47.CanonicalNeckUniformTimeJets
import PoincareConjecture.Proofs.M47.CanonicalNeckChartDifference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M]

theorem chart_neck_metric_jets_uniform_time_delta [T2Space M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹)
    (p : M) {H : Set E₃} (hH : IsCompact H)
    (hHt : H ⊆ (extChartAt (𝓡 3) p).target) {rho : ℝ} (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |s - t| < delta → ∀ (q : UnitTwoSphere) (z : ℝ),
        z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        N.coordinate_map (q, z) ∈ (extChartAt (𝓡 3) p).source →
        (extChartAt (𝓡 3) p) (N.coordinate_map (q, z)) ∈ H →
        ∀ j ≤ m, ∀ i l : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s) N.coordinate_map)
              (chartAt E₂ q) y i l -
            roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
              (chartAt E₂ q) y i l) (0, z)‖ < rho := by
  obtain ⟨C, hC, hbound⟩ := exists_neck_chart_coefficient_difference_bound N m hm p hH hHt
  let eta := rho / (C + 1)
  have heta : 0 < eta := div_pos hrho (by positivity)
  have hsmall : C * eta < rho := by
    have heq : (C + 1) * eta = rho := by dsimp only [eta]; field_simp
    nlinarith
  obtain ⟨delta, hdelta, hmod⟩ := metric_jets_uniform_time_delta_on_compact hab F
    (isOpen_extChartAt_target p) (contMDiffOn_extChartAt_symm p) hH hHt m heta
  refine ⟨delta, hdelta, ?_⟩
  intro s hs t ht hst q z hz hsource hcenter j hj i l
  exact (hbound (F.metric s) (F.metric t) eta heta.le
    (fun x hx k hk => (hmod s hs t ht hst x hx k hk).le)
    q z hz hsource hcenter j hj i l).trans_lt hsmall

theorem neck_metric_jets_uniform_time_delta [T3Space M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹)
    {K : Set M} (hK : IsCompact K) (hNK : N.carrier ⊆ K) {rho : ℝ} (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |s - t| < delta → ∀ (q : UnitTwoSphere) (z : ℝ),
        z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ j ≤ m, ∀ i l : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s) N.coordinate_map)
                (chartAt E₂ q) y i l -
              roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
                (chartAt E₂ q) y i l) (0, z)‖ < rho := by
  classical
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  let P (s t : ℝ) (q : UnitTwoSphere) (z : ℝ) : Prop :=
    ∀ j ≤ m, ∀ i l : Fin 3,
      ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s) N.coordinate_map)
            (chartAt E₂ q) y i l -
          roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
            (chartAt E₂ q) y i l) (0, z)‖ < rho
  have hlocal (p : M) : ∃ U : Set M, U ∈ 𝓝 p ∧ ∃ d : ℝ, 0 < d ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |s - t| < d →
        ∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
          N.coordinate_map (q, z) ∈ U → P s t q z := by
    let c := extChartAt (𝓡 3) p
    obtain ⟨H, hH, hpH, hHt⟩ := exists_compact_subset
      (isOpen_extChartAt_target (I := 𝓡 3) p) (mem_extChartAt_target (I := 𝓡 3) p)
    let U := c.source ∩ c ⁻¹' H
    have hU : U ∈ 𝓝 p := inter_mem (extChartAt_source_mem_nhds (I := 𝓡 3) p)
      ((continuousAt_extChartAt (I := 𝓡 3) p).preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp hpH))
    obtain ⟨d, hd, hmod⟩ := chart_neck_metric_jets_uniform_time_delta hab F N m hm p hH hHt hrho
    exact ⟨U, hU, d, hd, fun s hs t ht hst q z hz hx =>
      hmod s hs t ht hst q z hz hx.1 hx.2⟩
  choose U hU d hd hbound using hlocal
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover U (fun p _ => hU p)
  let R : Finset ℝ := insert 1 (S.image d)
  have hR : R.Nonempty := Finset.insert_nonempty _ _
  let delta := R.inf' hR id
  have hdelta : 0 < delta := by
    apply (Finset.lt_inf'_iff _).mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact zero_lt_one
    · obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hr
      exact hd p
  refine ⟨delta, hdelta, ?_⟩
  intro s hs t ht hst q z hz
  obtain ⟨p, hpS, hxp⟩ : ∃ p ∈ S, N.coordinate_map (q, z) ∈ U p := by
    simpa only [mem_iUnion, exists_prop] using hcover (hNK (N.coordinate_map_mem_of_axial_mem hz))
  have hdeltaP : delta ≤ d p := Finset.inf'_le id
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem d hpS))
  exact hbound p s hs t ht (hst.trans_le hdeltaP) q z hz hxp

end PoincareConjecture.Proofs.M47
