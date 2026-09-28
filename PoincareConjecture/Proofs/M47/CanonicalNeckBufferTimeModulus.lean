import PoincareConjecture.Proofs.M47.CanonicalNeckUniformTimeComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem neck_buffer_metric_jets_uniform_time_delta
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    {R : ℝ} (hR : R < N.epsilon⁻¹)
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹) {rho : ℝ} (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |s - t| < delta → ∀ (q : UnitTwoSphere) (z : ℝ),
        z ∈ Icc (-R) R → ∀ j ≤ m, ∀ i l : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient (roundCylinderPullback (F.metric s) N.coordinate_map)
                (chartAt E₂ q) y i l -
              roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
                (chartAt E₂ q) y i l) (0, z)‖ < rho := by
  classical
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  let D : Set RoundCylinderSpace := univ ×ˢ Icc (-R) R
  let K := N.coordinate_map '' D
  have hD : IsCompact D := isCompact_univ.prod isCompact_Icc
  have haxis {z : ℝ} (hz : z ∈ Icc (-R) R) : z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨(neg_lt_neg hR).trans_le hz.1, hz.2.trans_lt hR⟩
  have hK : IsCompact K := hD.image_of_continuousOn
    (N.coordinate_map_smooth.continuousOn.mono (fun _ hz => ⟨mem_univ _, haxis hz.2⟩))
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
  choose U hU d hd hmod using hlocal
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover U (fun p _ => hU p)
  let E : Finset ℝ := insert 1 (S.image d)
  have hE : E.Nonempty := Finset.insert_nonempty _ _
  let delta := E.inf' hE id
  have hdelta : 0 < delta := (Finset.lt_inf'_iff hE).mpr (by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact zero_lt_one
    · obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp he
      exact hd p)
  refine ⟨delta, hdelta, ?_⟩
  intro s hs t ht hst q z hz
  obtain ⟨p, hp, hzp⟩ : ∃ p ∈ S, N.coordinate_map (q, z) ∈ U p := by
    simpa only [mem_iUnion, exists_prop] using hcover
      (show N.coordinate_map (q, z) ∈ K from ⟨(q, z), ⟨mem_univ _, hz⟩, rfl⟩)
  have hle : delta ≤ d p := Finset.inf'_le id
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem d hp))
  exact hmod p s hs t ht (hst.trans_le hle) q z (haxis hz) hzp

end PoincareConjecture.Proofs.M47
