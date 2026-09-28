import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceOrientedTransfer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckBalancedScale
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckBalancedDistance










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe v

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}



structure SourceEdgeCommonOrientationPacket
    (N P Q : EpsilonNeck g) {γ : ℝ → M} (tN tP : ℝ) : Prop where
  choice : Q = P ∨ Q = P.reversed
  epsilon_eq : Q.epsilon = N.epsilon
  center_N : γ tN = N.center
  center_Q : γ tP = Q.center
  edge : MapsTo γ (Ico tN tP) N.carrier
  frontier : Q.center ∈ frontier N.carrier
  narrow_closure : Q.center ∈ closure
    (N.region ((255 : ℝ) * N.epsilon⁻¹ / 256) N.epsilon⁻¹)
  forward_carrier : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ Q.carrier
  forward_region : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
    Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2)
  reciprocal_region : Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
    N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹)
  anchor_band : Q.region (-(0.31 : ℝ) * N.epsilon⁻¹)
      (-(0.29 : ℝ) * N.epsilon⁻¹) ⊆
    N.region ((0.59 : ℝ) * N.epsilon⁻¹) ((0.76 : ℝ) * N.epsilon⁻¹)
  transition : ∃ w ∈ Ioo tN tP,
    (N.coordinate_inverse (γ w)).2 = (509 : ℝ) * N.epsilon⁻¹ / 512 ∧
    (∀ t ∈ Ioo w tP, (509 : ℝ) * N.epsilon⁻¹ / 512 <
      (N.coordinate_inverse (γ t)).2) ∧
    N.region ((127 : ℝ) * N.epsilon⁻¹ / 128) N.epsilon⁻¹ ⊆ Q.carrier
  scale : (0.999 : ℝ) * N.scale < Q.scale ∧ Q.scale < (1.001 : ℝ) * N.scale
  overlap : (N.carrier ∩ Q.carrier).Nonempty
  center_distance : ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.edist N.center Q.center ∧
    g.edist N.center Q.center ≤
      ENNReal.ofReal ((1.01 : ℝ) * N.scale * N.epsilon⁻¹)



theorem exists_source_edge_common_orientation_packet :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {M : Type v} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N₀ P : EpsilonNeck g), N₀.epsilon ≤ ε₀ → P.epsilon = N₀.epsilon →
      ∀ {γ : ℝ → M} {tN tP : ℝ}, tN < tP →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc tN tP) →
        γ tN = N₀.center → γ tP = P.center →
        MapsTo γ (Ico tN tP) N₀.carrier → P.center ∈ frontier N₀.carrier →
        ∃ N Q : EpsilonNeck g, (N = N₀ ∨ N = N₀.reversed) ∧
          SourceEdgeCommonOrientationPacket N P Q (γ := γ) tN tP := by
  obtain ⟨εT, hTpos, hTsmall, hT⟩ :=
    exists_uniform_oriented_forward_reciprocal_sign.{v}
  obtain ⟨εF, hFpos, _, hF⟩ := exists_frontier_neck_sphere_sides_accuracy.{v}
  obtain ⟨εS, hSpos, _, hS⟩ := exists_neck_balanced_scale_accuracy.{v}
  obtain ⟨εD, hDpos, _, hD⟩ := exists_neck_frontier_distance_accuracy.{v}
  let ε₀ := min εT (min εF (min εS εD))
  refine ⟨ε₀, lt_min hTpos (lt_min hFpos (lt_min hSpos hDpos)),
    (min_le_left _ _).trans hTsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N₀ P hε heq γ tN tP htp hγ hcN hcP hedge hfront
  have hεT : N₀.epsilon ≤ εT := hε.trans (min_le_left _ _)
  have hεF : N₀.epsilon ≤ εF :=
    hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεS : N₀.epsilon ≤ εS :=
    hε.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεD : N₀.epsilon ≤ εD :=
    hε.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨σ, hσ, w, hw, hwlevel, hafter, _, hclose, htail, _⟩ :=
    hF M g N₀.connection N₀ P heq.symm hεF γ tN tP htp
      hγ.continuousOn hcN hcP hedge hfront
  have build (N : EpsilonNeck g) (hchoice : N = N₀ ∨ N = N₀.reversed)
      (hNε : N.epsilon = N₀.epsilon) (hc : γ tN = N.center)
      (hedgeN : MapsTo γ (Ico tN tP) N.carrier)
      (hfrontN : P.center ∈ frontier N.carrier)
      (hcloseN : P.center ∈ closure
        (N.region ((255 : ℝ) * N.epsilon⁻¹ / 256) N.epsilon⁻¹))
      (htransition : ∃ w ∈ Ioo tN tP,
        (N.coordinate_inverse (γ w)).2 = (509 : ℝ) * N.epsilon⁻¹ / 512 ∧
        (∀ t ∈ Ioo w tP, (509 : ℝ) * N.epsilon⁻¹ / 512 <
          (N.coordinate_inverse (γ t)).2) ∧
        N.region ((127 : ℝ) * N.epsilon⁻¹ / 128) N.epsilon⁻¹ ⊆ P.carrier) :
      ∃ N Q : EpsilonNeck g, (N = N₀ ∨ N = N₀.reversed) ∧
        SourceEdgeCommonOrientationPacket N P Q (γ := γ) tN tP := by
    have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
    have hout : P.center ∉ N.carrier :=
      (N.carrier_open.frontier_eq ▸ hfrontN).2
    have hquarter : P.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) := by
      apply closure_mono (s := N.region ((255 : ℝ) * N.epsilon⁻¹ / 256) N.epsilon⁻¹)
        (t := N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ?_ hcloseN
      intro y hy
      exact ⟨hy.1, by linarith [hy.2.1], hy.2.2⟩
    obtain ⟨Q, hQ, hforwardC, hforwardR, hrecip, hband⟩ :=
      hT N P (by simpa only [hNε] using hεT) (heq.trans hNε.symm) hquarter hout
    have hQcenter : Q.center = P.center := by
      rcases hQ with rfl | rfl <;> simp
    have hQcarrier : Q.carrier = P.carrier := by
      rcases hQ with rfl | rfl <;> simp
    have hQε : Q.epsilon = N.epsilon := by
      rcases hQ with rfl | rfl <;> simpa using heq.trans hNε.symm
    have hmeet : (N.carrier ∩ Q.carrier).Nonempty := by
      let q : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
      let z : RoundCylinderSpace := (q, (3 : ℝ) * N.epsilon⁻¹ / 4)
      have hz : z ∈ N.cylinderDomain :=
        ⟨mem_univ _, by dsimp [z]; constructor <;> linarith⟩
      have hy : N.coordinate_map z ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
        refine ⟨N.coordinate_map_mem hz, ?_⟩
        rw [N.coordinate_inverse_coordinate_map hz]
        dsimp [z]
        constructor <;> linarith
      exact ⟨N.coordinate_map z, hy.1, hforwardC hy⟩
    have hscale := hS M g N.connection Q N
      (by simpa only [hQε, hNε] using hεS)
      (by simpa only [hNε] using hεS)
      (by simpa only [inter_comm] using hmeet)
    have hdist := hD M g N (by simpa only [hNε] using hεD) P.center hfrontN
    refine ⟨N, Q, hchoice, ?_⟩
    refine ⟨hQ, hQε, hc, by simpa only [hQcenter] using hcP,
      hedgeN, by simpa only [hQcenter] using hfrontN,
      by simpa only [hQcenter] using hcloseN, hforwardC, hforwardR, hrecip,
      ?_, ?_, ?_, hmeet, by simpa only [hQcenter] using hdist⟩
    · intro y hy
      have hh := hband y hy.1 (Q.coordinate_inverse y).2 rfl
        (by linarith [hy.2.1]) (by linarith [hy.2.2])
      exact ⟨hh.1, by linarith [hh.2.1, hy.2.1],
        by linarith [hh.2.2, hy.2.2]⟩
    · simpa only [hQcarrier] using htransition
    · simpa only [show (999 / 1000 : ℝ) = 0.999 by norm_num,
        show (1001 / 1000 : ℝ) = 1.001 by norm_num] using hscale
  rcases hσ with rfl | rfl
  · refine build N₀ (Or.inl rfl) rfl hcN hedge hfront ?_ ?_
    · simpa only [neckSignedRegion_one] using hclose
    · refine ⟨w, hw, by simpa only [one_mul] using hwlevel, ?_, ?_⟩
      · simpa only [one_mul] using hafter
      · have ht := htail.trans (P.region_subset_carrier _ _)
        simpa only [neckSignedRegion_one] using ht
  · refine build N₀.reversed (Or.inr rfl) (by simp only [reversed_epsilon])
      (by simpa only [reversed_center] using hcN)
      (by simpa only [reversed_carrier] using hedge)
      (by simpa only [reversed_carrier] using hfront) ?_ ?_
    · simpa only [reversed_epsilon, reversed_region, neckSignedRegion_neg_one]
        using hclose
    · refine ⟨w, hw, ?_, ?_, ?_⟩
      · simpa only [reversed_epsilon, reversed_coordinate_inverse,
          neg_one_mul] using hwlevel
      · simpa only [reversed_epsilon, reversed_coordinate_inverse,
          neg_one_mul] using hafter
      · have ht := htail.trans (P.region_subset_carrier _ _)
        simpa only [reversed_epsilon, reversed_region, neckSignedRegion_neg_one] using ht

end PoincareConjecture.M28
