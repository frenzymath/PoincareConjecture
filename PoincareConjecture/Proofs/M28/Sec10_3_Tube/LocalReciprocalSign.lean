import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalForwardTransfer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeMinimizerOverlap
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal



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
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem exists_oriented_forward_reciprocal_sign :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
      P.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
      P.center ∉ N.carrier →
      ∃ Q : EpsilonNeck g,
        (Q = P ∨ Q = P.reversed) ∧
        N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ Q.carrier ∧
        N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
          Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2) ∧
        (Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
          N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹) ∧
        (∀ y ∈ Q.carrier, ∀ u, u = (Q.coordinate_inverse y).2 →
          -N.epsilon⁻¹ < u → u < -(0.07 : ℝ) * N.epsilon⁻¹ →
          y ∈ N.carrier ∧
          (0.9 : ℝ) * N.epsilon⁻¹ -
              (1.1 : ℝ) * (-u - (0.03 : ℝ) * N.epsilon⁻¹) ≤
            (N.coordinate_inverse y).2 ∧
            (N.coordinate_inverse y).2 ≤ (0.99 : ℝ) * N.epsilon⁻¹ -
              (0.9 : ℝ) * (-u - (0.03 : ℝ) * N.epsilon⁻¹))) := by
  obtain ⟨εT, hTpos, _, hT⟩ :=
    exists_frontier_transition_height_bounds_m28.{v}
  obtain ⟨εC, hCpos, _, hC⟩ :=
    exists_closure_positive_quarter_subset_of_central_sphere_contact_m28.{v}
  obtain ⟨εB, hBpos, hBsmall, hB⟩ :=
    exists_reciprocal_band_of_positive_frontier_contact.{v}
  let ε₀ := min εT (min εC εB)
  refine ⟨ε₀, lt_min hTpos (lt_min hCpos hBpos),
    (min_le_right _ _).trans ((min_le_right _ _).trans hBsmall), ?_⟩
  intro N P hε heq hcenter hout
  have hεT : N.epsilon ≤ εT := hε.trans (min_le_left _ _)
  have hεC : N.epsilon ≤ εC :=
    hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεB : N.epsilon ≤ εB :=
    hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hfront : P.center ∈ frontier N.carrier := by
    rw [N.carrier_open.frontier_eq]
    exact ⟨closure_mono (N.region_subset_carrier _ _) hcenter, hout⟩
  obtain ⟨σT, hσT, hheight⟩ := hT N P hεT heq P.center hfront hcenter
    P.center_on_central_sphere
  have hpositive := hC N P hεC heq
    ⟨P.center, hcenter, P.center_on_central_sphere⟩
  have hApos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hsmall10 : N.epsilon ≤ (1 / 10000 : ℝ) := by
    exact hε.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans hBsmall))
  have hsmall1000 : N.epsilon ≤ (1 / 1000 : ℝ) := hsmall10.trans (by norm_num)
  have hAlarge : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hsmall1000 hApos.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  rcases hσT with hσT | hσT
  · subst σT
    refine ⟨P, Or.inl rfl, ?_, ?_, ?_⟩
    · intro y hy; exact hpositive (subset_closure hy)
    · intro y hy
      have ha : (N.coordinate_inverse y).2 ∈
          Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := hy.2
      have hh := hheight (N.coordinate_inverse y).1
        (N.coordinate_inverse y).2 ha
      rw [N.coordinate_map_coordinate_inverse hy.1] at hh
      exact ⟨hpositive (subset_closure hy), by
        nlinarith [hh.1, Real.pi_le_four, ha.1, ha.2], by
        nlinarith [hh.2, Real.pi_le_four, ha.1, ha.2]⟩
    · obtain ⟨σB, hσB, hband⟩ := hB N P hεB heq P.center hfront hcenter
          P.center_on_central_sphere
      have hσBpos : σB = 1 := by
        let q : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
        let u₀ : ℝ := -(0.3 : ℝ) * N.epsilon⁻¹
        let z : RoundCylinderSpace := (q, σB * u₀)
        have hz : z ∈ P.cylinderDomain := by
          refine ⟨mem_univ _, ?_⟩
          rw [heq]
          dsimp [z, u₀]
          rcases hσB with hσB | hσB <;> rw [hσB] <;>
            constructor <;> nlinarith [hApos]
        let y : M := P.coordinate_map z
        have hy : y ∈ P.carrier := P.coordinate_map_mem hz
        have hsq : σB * (σB * u₀) = u₀ := by
          rcases hσB with hσB | hσB <;> rw [hσB] <;> ring
        have hu : σB * (P.coordinate_inverse y).2 = u₀ := by
          dsimp only [y, z]
          rw [P.coordinate_inverse_coordinate_map hz]
          exact hsq
        have hbandY := hband y hy u₀ hu.symm (by dsimp [u₀]; linarith)
          (by dsimp [u₀]; nlinarith [hApos])
        have hyN := hbandY.1
        have ha := hbandY.2.1
        have hau := hbandY.2.2
        have hlowA : (N.epsilon⁻¹ / 2) < (N.coordinate_inverse y).2 := by
          dsimp [u₀] at ha; nlinarith [hApos]
        have huppA : (N.coordinate_inverse y).2 < N.epsilon⁻¹ := by
          dsimp [u₀] at hau; linarith [hau, hApos]
        have hh := hheight (N.coordinate_inverse y).1
          (N.coordinate_inverse y).2 ⟨hlowA, huppA⟩
        have hmap : N.coordinate_map
            ((N.coordinate_inverse y).1, (N.coordinate_inverse y).2) = y :=
          N.coordinate_map_coordinate_inverse hyN
        rw [hmap] at hh
        have hupper : -(0.9 : ℝ) *
            (N.epsilon⁻¹ - (N.coordinate_inverse y).2) + 5 * Real.pi < 0 := by
          have hgap : (0.253 : ℝ) * N.epsilon⁻¹ ≤
              N.epsilon⁻¹ - (N.coordinate_inverse y).2 := by
            dsimp [u₀] at hau
            linarith [hau]
          linarith [hgap, hAlarge, Real.pi_le_four]
        have hneg : (P.coordinate_inverse y).2 < 0 := by
          have hhupper : (P.coordinate_inverse y).2 ≤
              -(0.9 : ℝ) * (N.epsilon⁻¹ - (N.coordinate_inverse y).2) +
                5 * Real.pi := by
            simpa only [one_mul] using hh.2
          exact lt_of_le_of_lt hhupper hupper
        rcases hσB with hσB | hσB
        · exact hσB
        · exfalso
          have hycoord : (P.coordinate_inverse y).2 = -u₀ := by
            dsimp only [y, z]
            rw [P.coordinate_inverse_coordinate_map hz]
            change σB * u₀ = -u₀
            rw [hσB]
            ring
          rw [hycoord] at hneg
          dsimp [u₀] at hneg
          linarith [hApos]
      rw [hσBpos] at hband
      have hrecip : P.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
          N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹) := by
        intro y hy
        have h := hband y hy.1 ((P.coordinate_inverse y).2) (by ring)
          hy.2.1 (by nlinarith [hy.2.2, hApos])
        refine ⟨h.1, ?_, ?_⟩
        · nlinarith [h.2.1, hy.2.1, hy.2.2, hApos]
        · nlinarith [h.2.2, hy.2.1, hy.2.2, hApos]
      exact ⟨hrecip, by simpa only [one_mul] using hband⟩
  · subst σT
    refine ⟨P.reversed, Or.inr rfl, ?_, ?_, ?_⟩
    · intro y hy; simpa only [reversed_carrier] using hpositive (subset_closure hy)
    · intro y hy
      have ha : (N.coordinate_inverse y).2 ∈
          Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := hy.2
      have hh := hheight (N.coordinate_inverse y).1
        (N.coordinate_inverse y).2 ha
      rw [N.coordinate_map_coordinate_inverse hy.1] at hh
      have hh' := hh
      have hlow : -N.epsilon⁻¹ < (P.reversed.coordinate_inverse y).2 := by
        have h := hh'.1
        simp only [neg_one_mul] at h
        rw [reversed_coordinate_inverse]
        nlinarith [h, Real.pi_le_four, ha.1, ha.2]
      have hupp : (P.reversed.coordinate_inverse y).2 < N.epsilon⁻¹ / 2 := by
        have h := hh'.2
        simp only [neg_one_mul] at h
        rw [reversed_coordinate_inverse]
        nlinarith [h, Real.pi_le_four, ha.1, ha.2]
      exact ⟨hpositive (subset_closure hy), hlow, hupp⟩
    · have hEqRev : P.reversed.epsilon = N.epsilon := by
        simpa only [reversed_epsilon] using heq
      have hSphereRev : P.center ∈ P.reversed.central_sphere := by
        simpa only [reversed_center, reversed_central_sphere] using
          P.center_on_central_sphere
      obtain ⟨σB, hσB, hband⟩ := hB N P.reversed hεB hEqRev P.center
        hfront hcenter hSphereRev
      have hσBpos : σB = 1 := by
        let q : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
        let u₀ : ℝ := -(0.3 : ℝ) * N.epsilon⁻¹
        let z : RoundCylinderSpace := (q, σB * u₀)
        have hz : z ∈ P.reversed.cylinderDomain := by
          refine ⟨mem_univ _, ?_⟩
          simp only [reversed_epsilon, heq]
          dsimp [z, u₀]
          rcases hσB with hσB | hσB <;> rw [hσB] <;>
            constructor <;> nlinarith [hApos]
        let y : M := P.reversed.coordinate_map z
        have hy := P.reversed.coordinate_map_mem hz
        have hsq : σB * (σB * u₀) = u₀ := by
          rcases hσB with hσB | hσB <;> rw [hσB] <;> ring
        have hu : σB * (P.reversed.coordinate_inverse y).2 = u₀ := by
          dsimp only [y, z]
          rw [P.reversed.coordinate_inverse_coordinate_map hz]
          exact hsq
        have hbandY := hband y hy u₀ hu.symm (by dsimp [u₀]; linarith)
          (by dsimp [u₀]; nlinarith [hApos])
        have hyN := hbandY.1
        have ha := hbandY.2.1
        have hau := hbandY.2.2
        have hlowA : (N.epsilon⁻¹ / 2) < (N.coordinate_inverse y).2 := by
          dsimp [u₀] at ha; nlinarith [hApos]
        have huppA : (N.coordinate_inverse y).2 < N.epsilon⁻¹ := by
          dsimp [u₀] at hau; linarith [hau, hApos]
        have hh := hheight (N.coordinate_inverse y).1
          (N.coordinate_inverse y).2 ⟨hlowA, huppA⟩
        have hmap : N.coordinate_map
            ((N.coordinate_inverse y).1, (N.coordinate_inverse y).2) = y :=
          N.coordinate_map_coordinate_inverse hyN
        rw [hmap] at hh
        have hupper : -(0.9 : ℝ) *
            (N.epsilon⁻¹ - (N.coordinate_inverse y).2) + 5 * Real.pi < 0 := by
          have hgap : (0.253 : ℝ) * N.epsilon⁻¹ ≤
              N.epsilon⁻¹ - (N.coordinate_inverse y).2 := by
            dsimp [u₀] at hau
            linarith [hau]
          linarith [hgap, hAlarge, Real.pi_le_four]
        have hneg : -(P.coordinate_inverse y).2 < 0 := by
          have hhupper : -(P.coordinate_inverse y).2 ≤
              -(0.9 : ℝ) * (N.epsilon⁻¹ - (N.coordinate_inverse y).2) +
                5 * Real.pi := by
            simpa only [one_mul, neg_one_mul] using hh.2
          exact lt_of_le_of_lt hhupper hupper
        rcases hσB with hσB | hσB
        · exact hσB
        · exfalso
          have hycoord : (P.reversed.coordinate_inverse y).2 = -u₀ := by
            dsimp only [y, z]
            rw [P.reversed.coordinate_inverse_coordinate_map hz]
            change σB * u₀ = -u₀
            rw [hσB]
            ring
          have hrel : -(P.coordinate_inverse y).2 =
              (P.reversed.coordinate_inverse y).2 := by
            simp only [reversed_coordinate_inverse]
          rw [hrel, hycoord] at hneg
          have hu₀pos : 0 < -u₀ := by
            dsimp [u₀]
            have hpos : 0 < (0.3 : ℝ) * N.epsilon⁻¹ :=
              mul_pos (by norm_num) hApos
            simpa only [neg_mul, neg_neg] using hpos
          exact (not_lt_of_ge hu₀pos.le) hneg
      rw [hσBpos] at hband
      have hrecip : P.reversed.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
          N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹) := by
        intro y hy
        have hu_low : -N.epsilon⁻¹ <
            (P.reversed.coordinate_inverse y).2 := hy.2.1
        have hu_high : (P.reversed.coordinate_inverse y).2 <
            -N.epsilon⁻¹ / 2 := hy.2.2
        have h := hband y hy.1 ((P.reversed.coordinate_inverse y).2) (by ring)
          hu_low (by linarith [hu_high, hApos])
        have hneg_lower : N.epsilon⁻¹ / 2 <
            -(P.reversed.coordinate_inverse y).2 := by
          linarith [hu_high]
        have hneg_upper : -(P.reversed.coordinate_inverse y).2 <
            N.epsilon⁻¹ := by
          linarith [hu_low]
        refine ⟨h.1, ?_, ?_⟩
        · linarith only [h.2.1, hneg_upper, hApos]
        · linarith only [h.2.2, hneg_lower, hApos]
      exact ⟨hrecip, by simpa only [one_mul] using hband⟩

end PoincareConjecture.M28
