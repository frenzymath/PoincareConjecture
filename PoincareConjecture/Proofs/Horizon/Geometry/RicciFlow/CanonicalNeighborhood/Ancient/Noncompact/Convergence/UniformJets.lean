import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Closeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.MovingCylinder
import PoincareConjecture.Proofs.Horizon.Topology.UniformConvergence.MovingPoints












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture
namespace TerminalNeck

theorem eventually_uniform_coefficientJets_of_locally_moving
    {I J : Set ℝ} {B₀ : ℝ → RoundCylinderTwoTensor}
    {B : ℕ → ℝ → RoundCylinderTwoTensor}
    (hjet : ∀ p : UnitTwoSphere, ∀ q : ℕ → UnitTwoSphere,
      (∀ k, ‖(q k : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2) →
      ∀ τ : ℕ → ℝ, (∀ k, τ k ∈ I) → ∀ a b : Fin 3, ∀ j : ℕ,
        TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (B k (τ k))
              (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b -
            roundCylinderTensorCoefficient (B₀ (τ k))
              (chartAt (EuclideanSpace ℝ (Fin 2)) (q k)) y a b) x)
          (fun _ => 0) atTop (({0} : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ J))
    (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ u ∈ I, ∀ z : RoundCylinderSpace, z.2 ∈ J →
      ∀ j, j ≤ m → ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (B k u)
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
            roundCylinderTensorCoefficient (B₀ u)
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η := by
  have hconv (j : ℕ) (a b : Fin 3) : TendstoUniformlyOn
      (fun k (x : UnitTwoSphere × (ℝ × ℝ)) => iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient (B k x.2.1)
            (chartAt (EuclideanSpace ℝ (Fin 2)) x.1) y a b -
          roundCylinderTensorCoefficient (B₀ x.2.1)
            (chartAt (EuclideanSpace ℝ (Fin 2)) x.1) y a b) (0, x.2.2))
      (fun _ => 0) atTop (univ ×ˢ (I ×ˢ J)) := by
    apply Poincare.Topology.tendstoUniformlyOn_prod_of_isCompact_of_locally_moving_points
      (g := fun _ : ℝ × ℝ => (0 :
        RoundCylinderCoordinates [×j]→L[ℝ] ℝ)) isCompact_univ
    intro p _
    refine ⟨Metric.ball p (1 / 2), Metric.isOpen_ball,
      Metric.mem_ball_self (by norm_num), ?_⟩
    intro q hq
    have hpq (k : ℕ) : ‖(q k : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2 := by
      simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using (hq k).2
    apply Poincare.Topology.tendstoUniformlyOn_prod_of_moving_points
      (g := fun _ : ℝ => (0 : RoundCylinderCoordinates [×j]→L[ℝ] ℝ))
    intro τ hτ
    exact ((hjet p q hpq τ hτ a b j).comp (fun s : ℝ => (0, s))).mono
      (fun s hs => ⟨mem_singleton 0, hs⟩)
  have hsingle (j : ℕ) (a b : Fin 3) : ∀ᶠ k in atTop,
      ∀ u ∈ I, ∀ z : RoundCylinderSpace, z.2 ∈ J →
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (B k u)
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
            roundCylinderTensorCoefficient (B₀ u)
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv j a b) η hη] with k hk u hu z hz
    have h := hk (z.1, (u, z.2)) ⟨mem_univ _, hu, hz⟩
    simpa only [dist_zero_left] using h.le
  have hall : ∀ᶠ k in atTop, ∀ j ≤ m, ∀ a b : Fin 3,
      ∀ u ∈ I, ∀ z : RoundCylinderSpace, z.2 ∈ J →
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (B k u)
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
            roundCylinderTensorCoefficient (B₀ u)
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η :=
    (eventually_all_finite (finite_Iic m)).mpr fun j _ =>
      Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr fun b => hsingle j a b
  exact hall.mono fun k hk u hu z hz j hj a b => hk j hj a b u hu z hz

end TerminalNeck

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalUniformJetCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem eventually_terminalCylinder_coefficientJets
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
        ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2)
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹)) (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ u ∈ Icc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
      z.2 ∈ Icc (-ε⁻¹) ε⁻¹ → ∀ j, j ≤ m → ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient
              (roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric u)
                (fun z => ((e k).toFun (0, Φ z)).2))
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
            roundCylinderTensorCoefficient
              (roundCylinderPullback (G.limit.flow.flow.metric u) Φ)
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η := by
  apply TerminalNeck.eventually_uniform_coefficientJets_of_locally_moving ?_ m hη
  intro p q hpq τ hτ a b j
  have hc := hconv.smooth_zero_convergence_movingTime_cylinder_coefficients
    hfixed (J := Icc (-1 : ℝ) 0) isCompact_Icc (fun _ hu => hu.2)
    τ hτ hΦ p q hpq a b
  apply hc.2 j _ (isCompact_singleton.prod isCompact_Icc)
  rintro ⟨x, s⟩ ⟨hx, hs⟩
  have hx0 : x = 0 := mem_singleton_iff.mp hx
  subst x
  have hinv : ε⁻¹ < δ⁻¹ := (inv_lt_inv₀ (hδ.trans hδε) hδ).mpr hδε
  exact ⟨Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2),
    (neg_lt_neg hinv).trans_le hs.1, hs.2.trans_lt hinv⟩



theorem eventually_terminalCylinder_tensorSmoothOn
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹)) :
    ∀ᶠ k in atTop, ∀ u : ℝ, RoundCylinderTensorSmoothOn ε
      (roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric u)
        (fun z => ((e k).toFun (0, Φ z)).2)) := by
  have hinv : ε⁻¹ < δ⁻¹ := (inv_lt_inv₀ (hδ.trans hδε) hδ).mpr hδε
  have hsub : univ ×ˢ Icc (-ε⁻¹) ε⁻¹ ⊆ (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ :
      Set RoundCylinderSpace) := fun z hz =>
    ⟨hz.1, (neg_lt_neg hinv).trans_le hz.2.1, hz.2.2.trans_lt hinv⟩
  have hK : IsCompact (univ ×ˢ Icc (-ε⁻¹) ε⁻¹ : Set RoundCylinderSpace) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (hK.image_of_continuousOn (hΦ.continuousOn.mono hsub))
  filter_upwards [eventually_ge_atTop j] with k hk u
  have hs : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun z => ((e k).toFun (0, Φ z)).2) (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) := by
    intro z hz
    have hzK : z ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹ := ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
    have hzG := G.exhaustion_monotone hk (hj (mem_image_of_mem Φ hzK))
    exact (((e k).terminalSpatialMap_contMDiffAt (G.exhaustion_open k)
      (t := 0) le_rfl hzG).comp z
        (hΦ.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds (hsub hzK)))).contMDiffWithinAt
  simpa only [one_mul] using roundCylinderTensorSmoothOn_smul_pullback
    ((S.term (G.subsequence k)).flow.flow.metric u) hs 1



theorem eventually_terminalCylinder_familyClose
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
        ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2)
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹))
    (hclose : RoundCylinderFamilyClose δ (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback (G.limit.flow.flow.metric u) Φ)) :
    ∀ᶠ k in atTop, RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric u)
        (fun z => ((e k).toFun (0, Φ z)).2)) := by
  apply TerminalNeck.eventually_roundCylinderFamilyClose_of_coefficientJets hδ hδε hclose
  · exact (eventually_terminalCylinder_tensorSmoothOn (G := G) (e := e) hδ hδε hΦ).mono
      fun k hk u _ => hk u
  · intro η hη
    exact (hconv.eventually_terminalCylinder_coefficientJets hfixed hδ hδε hΦ
      ⌊ε⁻¹⌋₊ hη).mono fun k hk u hu z hz => hk u ⟨hu.1.le, hu.2⟩ z ⟨hz.1.le, hz.2.le⟩

end M23TerminalMetricConvergence
end PoincareConjecture
