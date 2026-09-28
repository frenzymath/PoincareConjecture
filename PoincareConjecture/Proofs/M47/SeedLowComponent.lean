import PoincareConjecture.Proofs.M47.JointSeedPhysical
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CanonicalBall

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem seed_earlier_component_scalar_lt
    (P : M47ScalarPersistencePredecessors.{u}) [CompactSpace M]
    {J : Set ℝ} (G : RicciFlow 3 M J)
    (F : SurgeryFlowData.{u}) {s t C : ℝ} (q z : M)
    (phi : M → (F.slice s).carrier)
    (himage : ∀ p : M, phi p ∈ connectedComponent (phi z))
    (hread : ∀ p : M, (G.connection s).scalarCurvature p =
      (F.connection s).scalarCurvature (phi p))
    (hst : s ≤ t) (hJ : Icc s t ⊆ J)
    (N : SingularCComponent (F.metric s) (F.connection s) C)
    (hz : phi z ∈ N.carrier) :
    ∀ y ∈ N.carrier, (F.connection s).scalarCurvature y <
      (C / 6) * (G.connection t).scalarCurvature q := by
  obtain ⟨p, _hp, hp⟩ := exists_earlier_component_scalar_le P G (U := univ)
    isCompact_univ isOpen_univ hst hJ (mem_univ q)
  have hzbase : phi z ∈ connectedComponent N.basepoint := by
    rwa [← N.component_eq]
  have hcomponent : N.carrier = connectedComponent (phi z) :=
    N.component_eq.trans (connectedComponent_eq hzbase)
  have hpN : phi p ∈ N.carrier := hcomponent.symm ▸ himage p
  intro y hy
  apply (component_scalar_ratio N hpN hy).trans_le
  rw [← hread]
  exact mul_le_mul_of_nonneg_left hp (div_nonneg N.constant_pos.le (by norm_num))

theorem seed_future_reference_gap
    (P : M47ScalarPersistencePredecessors.{u}) [CompactSpace M]
    {J : Set ℝ} (G : RicciFlow 3 M J)
    (F : SurgeryFlowData.{u}) {s t C Q L : ℝ} (q z : M)
    (phi : M → (F.slice s).carrier)
    (himage : ∀ p : M, phi p ∈ connectedComponent (phi z))
    (hread : ∀ p : M, (G.connection s).scalarCurvature p =
      (F.connection s).scalarCurvature (phi p))
    (hst : s ≤ t) (hJ : Icc s t ⊆ J) (hC : 1 ≤ C) (hQ : 0 ≤ Q)
    (hfuture : (G.connection t).scalarCurvature q ≤ Q)
    (hlevel : C * Q ≤ L) (hhigh : L ≤ (G.connection s).scalarCurvature z) :
    ∃ p ∈ connectedComponent (phi z),
      (C / 6) * (F.connection s).scalarCurvature p ≤
        (F.connection s).scalarCurvature (phi z) := by
  obtain ⟨p, _hp, hp⟩ := exists_earlier_component_scalar_le P G (U := univ)
    isCompact_univ isOpen_univ hst hJ (mem_univ q)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨phi p, himage p, ?_⟩
  rw [← hread, ← hread]
  calc
    _ ≤ (C / 6) * Q := mul_le_mul_of_nonneg_left (hp.trans hfuture) (by positivity)
    _ ≤ C * Q := mul_le_mul_of_nonneg_right (by linarith) hQ
    _ ≤ L := hlevel
    _ ≤ _ := hhigh

theorem exists_seed_future_reference_analytic_bound (C : ℝ) :
    ∃ A : ℝ, 1 ≤ A ∧ C ≤ A ∧
      ∀ (_P : M47ScalarPersistencePredecessors.{u})
        (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [CompactSpace M]
        (J : Set ℝ) (G : RicciFlow 3 M J) (F : SurgeryFlowData.{u})
        (s t Q L : ℝ) (q z : M) (phi : M → (F.slice s).carrier),
        (∀ p : M, phi p ∈ connectedComponent (phi z)) →
        (∀ p : M, (G.connection s).scalarCurvature p =
          (F.connection s).scalarCurvature (phi p)) →
        s ≤ t → Icc s t ⊆ J → 1 ≤ C → 0 ≤ Q →
        (G.connection t).scalarCurvature q ≤ Q → C * Q ≤ L →
        L ≤ (G.connection s).scalarCurvature z →
        SurgeryCanonicalControl F s (phi z) F.parameters.epsilon C →
        M45PointwiseAnalyticEstimate (F.metric s) (F.connection s) (phi z) A := by
  obtain ⟨A, hA, hCA, hmodel⟩ := exists_jointSeed_physical_analytic_bound.{u} C
  refine ⟨A, hA, hCA, ?_⟩
  intro P M _ _ _ _ J G F s t Q L q z phi himage hread hst hJ hC hQ hfuture hlevel
    hhigh hcanonical
  obtain ⟨p, hp, hgap⟩ := seed_future_reference_gap P G F q z phi himage hread
    hst hJ hC hQ hfuture hlevel hhigh
  exact hmodel F s p (phi z) hp hgap hcanonical

theorem exists_seed_low_center_ball_bound (C : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ C ≤ B ∧
      ∀ (F : SurgeryFlowData.{u}) (t : ℝ) (x : (F.slice t).carrier)
        (Q r0 : ℝ), 0 ≤ C → 0 < r0 →
        (F.connection t).scalarCurvature x ≤ Q → Q ≤ r0⁻¹ ^ 2 →
        (C / 6) * Q ≤ r0⁻¹ ^ 2 →
        (∀ y ∈ (F.metric t).ball x (r0 / (8 * B)),
          r0⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature y →
          SurgeryCanonicalControl F t y F.parameters.epsilon C) →
        ∀ y ∈ (F.metric t).ball x (r0 / (8 * B)),
          (F.connection t).scalarCurvature y ≤ 2 * r0⁻¹ ^ 2 := by
  obtain ⟨B, hB, hCB, hmodel⟩ := exists_jointSeed_physical_analytic_bound.{u} C
  refine ⟨B, hB, hCB, ?_⟩
  intro F t x Q r0 hC hr0 hcenter hQ hgap hcanonical
  apply Proofs.M46.scalar_le_two_inv_sq_on_ball (F.metric t) (F.connection t)
    (M34.contMDiff_scalarCurvature (F.connection t)) (zero_lt_one.trans_le hB) hr0 x
    (hcenter.trans hQ)
  intro z hz hhigh v hv
  have hzcomponent := Proofs.M46.metric_ball_subset_connectedComponent
    (F.metric t) x (r0 / (8 * B)) hz
  have hxcomponent : x ∈ connectedComponent z := by
    rw [← connectedComponent_eq hzcomponent]
    exact mem_connectedComponent
  have hlow : (C / 6) * (F.connection t).scalarCurvature x ≤
      (F.connection t).scalarCurvature z :=
    (mul_le_mul_of_nonneg_left hcenter (by positivity)).trans (hgap.trans hhigh)
  have h := hmodel F t x z hxcomponent hlow (hcanonical z hz hhigh)
  exact ((F.connection t).abs_scalar_directional_le_scalarGradientNorm z v hv).trans h.2.1

end PoincareConjecture.M47
