import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicRectangleAdmission
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology ENNReal NNReal

universe u

namespace PoincareConjecture



theorem mem_m64AnnulusInterior_iff (p : LoopPlane) :
    p ∈ m64AnnulusInterior ↔
      0 < p 0 ∧ p 0 < curvePeriod ∧ 0 < p 1 ∧ p 1 < 1 := by
  simp [m64AnnulusInterior, Set.mem_pi, Fin.forall_fin_two, and_assoc]



theorem m64AnnulusInterior_subset_domain : m64AnnulusInterior ⊆ m64AnnulusDomain := by
  intro p hp
  rw [mem_m64AnnulusInterior_iff] at hp
  exact ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}




theorem m64Annulus_exists_eqOn_of_supported_smooth_modification
    (A : M64Annulus g c0 c1) {f : LoopPlane → M} {U K : Set LoopPlane}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hKinside : K ⊆ m64AnnulusInterior)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U)
    (hfix : ∀ p ∉ K, f p = A.map p) :
    ∃ B : M64Annulus g c0 c1, EqOn B.map f m64AnnulusDomain := by
  have hcontinuous : ContinuousOn f m64AnnulusDomain := by
    intro p hp
    by_cases hpU : p ∈ U
    · exact (hf.continuousOn.continuousAt (hU.mem_nhds hpU)).continuousWithinAt
    · have hpK : p ∉ K := fun h => hpU (hKU h)
      apply (A.continuous_on_domain p hp).congr_of_eventuallyEq_of_mem _ hp
      apply nhdsWithin_le_nhds
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hpK] with q hq
      exact hfix q hq
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hloc : LocallyLipschitzOn m64AnnulusDomain f := by
    intro p hp
    by_cases hpU : p ∈ U
    · obtain ⟨C, W, hW, hC⟩ := m64_lipschitzOn_nhds_of_contMDiffAt g
        (hf.contMDiffAt (hU.mem_nhds hpU))
      refine ⟨C, W ∩ m64AnnulusDomain,
        inter_mem (nhdsWithin_le_nhds hW) self_mem_nhdsWithin, ?_⟩
      intro x hx y hy
      change g.edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y
      simpa only [edist_dist, dist_eq_norm] using hC x hx.1 y hy.1
    · have hpK : p ∉ K := fun h => hpU (hKU h)
      let C : ℝ≥0 := ⟨A.lipschitz_constant, A.lipschitz_nonnegative⟩
      refine ⟨C, Kᶜ ∩ m64AnnulusDomain,
        inter_mem (nhdsWithin_le_nhds (hK.isClosed.isOpen_compl.mem_nhds hpK))
          self_mem_nhdsWithin, ?_⟩
      intro x hx y hy
      change g.edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y
      rw [hfix x hx.1, hfix y hy.1]
      have hcoe : (C : ℝ≥0∞) = ENNReal.ofReal A.lipschitz_constant := by
        exact (ENNReal.ofReal_coe_nnreal).symm
      rw [hcoe, edist_dist, dist_eq_norm]
      exact A.lipschitz_on_domain ⟨x, hx.2⟩ ⟨y, hy.2⟩
  obtain ⟨C, hC⟩ := M60.exists_lipschitzOnWith_of_compact_edist_ne_top
    m64AnnulusDomain_isCompact hloc (m64AnnulusDomain_edist_ne_top g hcontinuous)
  have hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    have h := hC x.property y.property
    change g.edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist (x : LoopPlane) y at h
    simpa only [ENNReal.ofReal_coe_nnreal, edist_dist, dist_eq_norm] using h
  have hboundary (x s : ℝ) (h : x = 0 ∨ x = curvePeriod ∨ s = 0 ∨ s = 1) :
      f (annulusPoint x s) = A.map (annulusPoint x s) := by
    apply hfix
    intro hp
    have hi := (mem_m64AnnulusInterior_iff _).mp (hKinside hp)
    change 0 < x ∧ x < curvePeriod ∧ 0 < s ∧ s < 1 at hi
    rcases h with h | h | h | h <;> subst_vars <;> linarith
  have hc0 : Function.Periodic c0 curvePeriod := by
    intro x
    rw [← A.lower_boundary (x + curvePeriod), A.periodic, A.lower_boundary]
  have hc1 : Function.Periodic c1 curvePeriod := by
    intro x
    rw [← A.upper_boundary (x + curvePeriod), A.periodic, A.upper_boundary]
  apply m64Annulus_exists_eqOn_rectangle_of_lipschitz g hc0 hc1 f hcontinuous
    (fun s _ => ?_) (fun x _ => ?_) (fun x _ => ?_) C.coe_nonneg hLip
  · rw [hboundary curvePeriod s (Or.inr (Or.inl rfl)),
      hboundary 0 s (Or.inl rfl)]
    simpa only [zero_add] using A.periodic 0 s
  · rw [hboundary x 0 (Or.inr (Or.inr (Or.inl rfl))), A.lower_boundary]
  · rw [hboundary x 1 (Or.inr (Or.inr (Or.inr rfl))), A.upper_boundary]

end PoincareConjecture
