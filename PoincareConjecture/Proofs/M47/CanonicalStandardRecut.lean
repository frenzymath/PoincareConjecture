import PoincareConjecture.Proofs.M47.CanonicalStandardRecutCertificate
import PoincareConjecture.Proofs.M47.BlowupControlsCapAnchoredData
import PoincareConjecture.Proofs.M47.BlowupControlsCapOutwardCoreData










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {g : RiemannianMetric 3 M}




theorem exists_same_constant_epsilon_recut (N : CapCertificate g)
    (hcomplete : MetricComplete g) (hsmall : N.epsilon ≤ 1 / 1200)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 200)
    (haccuracy : 6 * N.epsilon ≤ epsilon) :
    ∃ H : CapCertificate g,
      H.epsilon = epsilon ∧ H.cap_constant = N.cap_constant ∧
      H.carrier = N.carrier ∧ H.connection = N.connection ∧ N.core ⊆ H.core := by
  have hsmallEnd : N.end_neck.epsilon ≤ 1 / 1200 := by
    simpa only [N.end_neck_epsilon] using hsmall
  have haccuracyEnd : 6 * N.end_neck.epsilon ≤ epsilon := by
    simpa only [N.end_neck_epsilon] using haccuracy
  let q := (N.end_neck.coordinate_inverse N.end_neck.center).1
  obtain ⟨b, E, B, hb, hmargin, hEe, hBe, hED, hBD, hEcarrier,
    hBcarrier, hBsphere, hnegative⟩ := exists_cap_anchored_neck_data N.end_neck
      hsmallEnd hepsilon hepsilon_le haccuracyEnd q
  have hbCap : -N.epsilon⁻¹ < b := by
    simpa only [N.end_neck_epsilon] using hb
  have hmarginCap : b + 8 < N.epsilon⁻¹ := by
    simpa only [N.end_neck_epsilon] using hmargin
  obtain ⟨radius, bound, hbound, _holdRadius, hballs⟩ :=
    exists_cap_outward_core_data N hcomplete hsmall hbCap hmarginCap
  obtain ⟨H, hHe, hHC, hHcarrier, hHD, _hclosed, _hcore, hcoreSubset⟩ :=
    exists_same_constant_outward_cap N hbCap (by linarith only [hmarginCap])
      hepsilon hepsilon_le E B hEe hBe
      (hED.trans N.end_neck_connection) (hBD.trans N.end_neck_connection)
      (by simpa only [N.end_neck_epsilon] using hEcarrier)
      (hBcarrier.trans N.end_neck_subset) hBsphere
      (by rw [hBsphere]; exact hnegative) radius bound hbound hballs
  exact ⟨H, hHe, hHC, hHcarrier, hHD, hcoreSubset⟩

end PoincareConjecture.Proofs.M47
