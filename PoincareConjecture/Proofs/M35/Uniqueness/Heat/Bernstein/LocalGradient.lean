import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Bernstein.Energies
import PoincareConjecture.Proofs.M35.Uniqueness.LocalPositiveQuadraticBound
import PoincareConjecture.Proofs.M35.Uniqueness.VectorHeatGradientBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_local_positive_vector_heat_gradient_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B)
    {C₀ : Set StandardCapSpace} (hC₀ : IsCompact C₀) :
    ∃ E : Set StandardCapSpace, IsCompact E ∧ C₀ ⊆ interior E ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ → StandardCapSpace → StandardCapSpace,
      (∀ s, ContDiff ℝ ∞ (X s)) →
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
        (fun p : ℝ × StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace p.2
          (E := TangentSpace (𝓡 3)) (X p.1 p.2)) (Ioo 0 G.lifetime ×ˢ univ) →
      (∀ t ∈ Ioc 0 T, ∀ x ∈ E, (G.flow.metric t).inner x (X t x) (X t x) ≤ B) →
      (∀ t ∈ Ioc 0 T, ∀ x ∈ E, ∀ᶠ y in 𝓝 x,
        HasDerivWithinAt (fun s => X s y)
          (@Add.add StandardCapSpace inferInstance
            (∑ i, fieldHessian (G.flow.connection t) (X t) y
              ((G.flow.metric t).orthonormalBasis y i)
              ((G.flow.metric t).orthonormalBasis y i))
            (RicciFlow.ricciSharp (G.flow.connection t) y (X t y))) (Ico 0 G.lifetime) t) →
      ∀ t ∈ Ioc 0 T, ∀ p ∈ C₀, t * vectorHeatJetEnergy G X 1 t p ≤ C := by
  obtain ⟨K, hK, hRm⟩ := G.curvature_locally_bounded T hT.le hTlt
  let c := 1 / (2 * (17 * B + 1) ^ 2)
  let d := (324 * K * (17 * B + 1)) ^ 2 / 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  obtain ⟨E, hE, hCE, C, hC, hcomparison⟩ :=
    exists_raw_local_positive_quadratic_heat_bound P G hT hTlt hc hd hC₀
  refine ⟨E, hE, hCE, C, hC, ?_⟩
  intro X hX hJoint hbound hheat
  let q := vectorHeatJetEnergy G X 0
  let Q := vectorHeatJetEnergy G X 1
  let H := fun t x => (16 * B + 1 + q t x) * Q t x
  have hq (s) (y) : 0 ≤ q s y := vectorHeatJetEnergy_nonneg G X 0 s y
  have hQ (s) (y) : 0 ≤ Q s y := vectorHeatJetEnergy_nonneg G X 1 s y
  have hqb (s) (hs : s ∈ Ioc 0 T) (y) (hy : y ∈ E) : q s y ≤ B := by
    simpa only [q, vectorHeatJetEnergy_zero] using hbound s hs y hy
  have hcont : ContinuousOn (Function.uncurry H) (Ioc 0 T ×ˢ E) := by
    have h0 := (vectorHeatJetEnergy_positive_joint G (hT.trans hTlt) X hX hJoint 0).continuousOn
    have h1 := (vectorHeatJetEnergy_positive_joint G (hT.trans hTlt) X hX hJoint 1).continuousOn
    exact ((continuousOn_const.add h0).mul h1).mono
      (prod_mono (fun _ ht => ⟨ht.1, ht.2.trans_lt hTlt⟩) (subset_univ E))
  have hspace (s) (_hs : s ∈ Ioc 0 T) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (H s) :=
    (contMDiff_const.add (vectorHeatJetEnergy_space_smooth G X hX 0 s)).mul
      (vectorHeatJetEnergy_space_smooth G X hX 1 s)
  have heq (s) (hs : s ∈ Ioc 0 T) (y) (hy : y ∈ E) : ∃ a : ℝ,
      HasDerivWithinAt (fun r => H r y) a (Icc 0 s) s ∧
        a - (G.flow.connection s).laplacian (H s) y ≤ -c * H s y ^ 2 + d := by
    obtain ⟨a, ha, hb⟩ := vector_heat_product_reaction_of_eventually_heat G hT hTlt hs
      hK hB X hX hJoint y (hheat s hs y hy)
      ((le_abs_self _).trans (hRm s ⟨hs.1.le, hs.2⟩ y)) (hbound s hs y hy)
    have he : (fun r x => (16 * B + 1 + (G.flow.metric r).inner x (X r x) (X r x)) *
        ((G.flow.metric r).tensorNorm ((G.flow.connection r).covariantTensorDerivative
          (killingCovector (G.flow.metric r) (X r))) x) ^ 2) = H := by
      funext r x
      simp only [H, q, Q, vectorHeatJetEnergy_zero]
      rfl
    rw [he] at ha hb
    refine ⟨a, ha.mono (fun r hr => ⟨hr.1, hr.2.trans hs.2⟩), hb.trans ?_⟩
    exact vector_heat_product_quadratic_bound hB (hq s y) (hqb s hs y hy) (hQ s y)
      (mul_nonneg (by norm_num) hK)
  have hH (s) (_hs : s ∈ Ioc 0 T) (y) (_hy : y ∈ E) : 0 ≤ H s y := by
    have := hq s y
    exact mul_nonneg (by positivity) (hQ s y)
  have hout := hcomparison H hcont hH hspace heq
  intro t ht p hp
  have hQH : Q t p ≤ H t p := by
    calc
      Q t p = 1 * Q t p := by rw [one_mul]
      _ ≤ (16 * B + 1 + q t p) * Q t p :=
        mul_le_mul_of_nonneg_right (by have := hq t p; nlinarith) (hQ t p)
  exact (mul_le_mul_of_nonneg_left hQH ht.1.le).trans (hout t ht p hp)

end PoincareConjecture.M35.Uniqueness
