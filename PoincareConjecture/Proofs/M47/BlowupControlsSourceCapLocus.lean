import PoincareConjecture.Proofs.M47.CanonicalCapCompactFamily










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47



theorem exists_source_cap_certificate_at_base_of_locus {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta gamma C R : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) (hC : 0 < C) (hR : 0 ≤ R)
    {K : Set (ℝ × StandardCapSpace)} (hK : IsCompact K)
    (hKsub : K ⊆ Icc 0 theta ×ˢ {x | g0.metric.edist 0 x ≤ ENNReal.ofReal R})
    (hcaps : ∀ p ∈ K, ∃ N : CapCertificate (P.standard_cap.flow.metric p.1),
      N.epsilon = gamma ∧ N.cap_constant ≤ C ∧
      N.connection = P.standard_cap.flow.connection p.1 ∧ p.2 ∈ N.core) :
    ∃ A0 : ℝ, 0 < A0 ∧ R < A0 ∧ ∀ A : ℝ, A0 ≤ A →
      ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S P.standard_cap.flow →
      ∀ (base t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count)
        (closed : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
          (Icc 0 ((base - t) / (F.parameters.h t) ^ 2))
          ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      SurgeryCapFamilyComparison F S A eta closed initial.chart →
      0 ≤ (base - t) / (F.parameters.h t) ^ 2 →
      ∀ (y0 : (F.slice t).carrier) (y : (F.slice base).carrier),
        y0 ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) →
        (∀ htop, HEq (closed.forward ((base - t) / (F.parameters.h t) ^ 2) htop y0) y) →
        (∀ z ∈ F.standard_initial.metric.ball 0 A, initial.chart z = y0 →
          ((base - t) / (F.parameters.h t) ^ 2, z) ∈ K) →
        ∃ H : CapCertificate (F.metric base),
          H.epsilon = gamma ∧ H.cap_constant ≤ C ∧
          H.connection = F.connection base ∧ y ∈ H.core := by
  obtain ⟨A0, hA0, hRA0, tolerances⟩ :=
    exists_compact_standard_cap_physical_tolerance_above P htheta0 htheta hC hR hK hKsub hcaps
  refine ⟨A0, hA0, hRA0, fun A hA => ?_⟩
  obtain ⟨eta0, heta0, transfer⟩ := tolerances A hA
  refine ⟨eta0, heta0, ?_⟩
  intro F hinitial S hS base t hT hn i closed initial eta heta hetaLe comparison hd
    y0 y hy0 htop hlocus
  let h := F.parameters.h t
  let d := (base - t) / h ^ 2
  have hh : 0 < h :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hdmem : d ∈ Icc 0 d := ⟨hd, le_rfl⟩
  have himage := comparison.choose_spec.2.2.2.1
  rw [← himage] at hy0
  obtain ⟨z, hz, hzy⟩ := hy0
  obtain ⟨H, hHe, hHC, hHconn, hHcore⟩ := transfer F hinitial S hS t hT hn i
    (Icc 0 d) _ closed initial eta heta hetaLe comparison hh d hdmem z (hlocus z hz hzy)
  have hclock : t + d / (h⁻¹ ^ 2) = base := by
    rw [surgeryCap_physical_time]
    dsimp only [d]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hh).ne']
    ring
  have hpoint : (⟨t + d / (h⁻¹ ^ 2), actualCapSliceChart closed initial comparison d hdmem z⟩ :
      Σ s, (F.slice s).carrier) = ⟨base, y⟩ := by
    apply Sigma.ext hclock
    change HEq (closed.forward d hdmem (initial.chart z)) y
    rw [hzy]
    exact htop hdmem
  exact (congrArg (fun w : Σ s, (F.slice s).carrier =>
    ∃ H : CapCertificate (F.metric w.1), H.epsilon = gamma ∧ H.cap_constant ≤ C ∧
      H.connection = F.connection w.1 ∧ w.2 ∈ H.core) hpoint).mp
        ⟨H, hHe, hHC, hHconn, hHcore⟩

end PoincareConjecture.Proofs.M47
