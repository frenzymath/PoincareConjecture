import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Boundary


noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}



theorem cappedTube_low_point_or_low_neck (Q : SingularLimitConclusion H)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    (hcap : Y.cap.cap_constant ≤ 2 * H.constant) (q : ℝ)
    {p : (Q.extension.extended.slice T).carrier} (hp : p ∈ Y.carrier)
    (hplow : Q.terminal_scalar p ≤ q) :
    (p ∈ Y.cap.carrier ∧
      ∀ y ∈ Y.cap.carrier, Q.terminal_scalar y < 2 * H.constant * q) ∨
      ∃ i : ℤ, i ∈ Y.tube.chain.shape.active ∧
        p ∈ (Y.tube.chain.neck i).carrier ∧
        ∀ y ∈ (Y.tube.chain.neck i).carrier, Q.terminal_scalar y < 2 * q := by
  rw [Y.carrier_eq_union] at hp
  rcases hp with hpcap | hptube
  · refine Or.inl ⟨hpcap, ?_⟩
    intro y hy
    have heq (z) : Y.cap.connection.scalarCurvature z = Q.terminal_scalar z := by
      rw [Q.terminal_scalar_eq]
      exact Y.cap.connection.scalarCurvature_eq _ z
    have hratio := Y.cap.scalar_lt_constant_mul hpcap hy
    rw [heq p, heq y] at hratio
    have hppos : 0 < Q.terminal_scalar p := by
      rw [← heq p]
      exact Y.cap.scalar_pos p hpcap
    exact hratio.trans_le ((mul_le_mul_of_nonneg_right hcap hppos.le).trans
      (mul_le_mul_of_nonneg_left hplow
        (by positivity [H.constant_pos] : 0 ≤ 2 * H.constant)))
  · rw [Y.tube.carrier_eq_chain_union] at hptube
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hptube
    refine Or.inr ⟨i.val, i.property, hpi, ?_⟩
    intro y hy
    have hratio := (Y.tube.chain.neck i.val).scalar_lt_two_mul_of_mem_carrier
      (Q.extension.extended.connection T)
      ((Y.tube.chain.epsilon_eq i.val i.property).trans_le Y.tube.epsilon_le_threshold) hy hpi
    rw [← Q.terminal_scalar_eq] at hratio
    linarith



theorem cappedTube_low_point_dichotomy (Q : SingularLimitConclusion H)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    (hcap : Y.cap.cap_constant ≤ 2 * H.constant) (q : ℝ) (hq : 0 ≤ q)
    {p : (Q.extension.extended.slice T).carrier} (hp : p ∈ Y.carrier)
    (hplow : Q.terminal_scalar p ≤ q) :
    (∀ y ∈ Y.cap.carrier, Q.terminal_scalar y < 4 * H.constant * q) ∨
      ∃ i : ℤ, i ∈ Y.tube.chain.shape.active ∧
        (∀ y ∈ (Y.tube.chain.neck i).carrier, Q.terminal_scalar y < 2 * q) ∧
        Disjoint Y.cap.carrier (Y.tube.chain.neck i).carrier := by
  have heq (z) : Y.cap.connection.scalarCurvature z = Q.terminal_scalar z := by
    rw [Q.terminal_scalar_eq]
    exact Y.cap.connection.scalarCurvature_eq _ z
  have hbound (z) (hz : z ∈ Y.cap.carrier) (hzlow : Q.terminal_scalar z ≤ 2 * q) :
      ∀ y ∈ Y.cap.carrier, Q.terminal_scalar y < 4 * H.constant * q := by
    intro y hy
    have hratio := Y.cap.scalar_lt_constant_mul hz hy
    rw [heq z, heq y] at hratio
    have hzpos : 0 < Q.terminal_scalar z := by
      rw [← heq z]
      exact Y.cap.scalar_pos z hz
    have hupper := (mul_le_mul_of_nonneg_right hcap hzpos.le).trans
      (mul_le_mul_of_nonneg_left hzlow (by positivity [H.constant_pos] : 0 ≤ 2 * H.constant))
    nlinarith
  rw [Y.carrier_eq_union] at hp
  rcases hp with hpcap | hptube
  · exact Or.inl (hbound p hpcap (hplow.trans (by linarith)))
  · rw [Y.tube.carrier_eq_chain_union] at hptube
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hptube
    have hneck : ∀ y ∈ (Y.tube.chain.neck i.val).carrier, Q.terminal_scalar y < 2 * q := by
      intro y hy
      have hratio := (Y.tube.chain.neck i.val).scalar_lt_two_mul_of_mem_carrier
        (Q.extension.extended.connection T)
        ((Y.tube.chain.epsilon_eq i.val i.property).trans_le Y.tube.epsilon_le_threshold) hy hpi
      rw [← Q.terminal_scalar_eq] at hratio
      linarith
    by_cases hdis : Disjoint Y.cap.carrier (Y.tube.chain.neck i.val).carrier
    · exact Or.inr ⟨i.val, i.property, hneck, hdis⟩
    · obtain ⟨z, hzcap, hzneck⟩ := Set.not_disjoint_iff.mp hdis
      exact Or.inl (hbound z hzcap (hneck z hzneck).le)



theorem subset_tube_of_cappedTube_scalar_bound (Q : SingularLimitConclusion H)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    {X : Set (Q.extension.extended.slice T).carrier} (hXY : X ⊆ Y.carrier)
    (q : ℝ) (hcap : ∀ x ∈ Y.cap.carrier, Q.terminal_scalar x < q)
    (hX : ∀ x ∈ X, q ≤ Q.terminal_scalar x) : X ⊆ Y.tube.carrier := by
  intro x hx
  have hy := hXY hx
  rw [Y.carrier_eq_union] at hy
  exact hy.resolve_left (fun hxc => (hcap x hxc).not_ge (hX x hx))

end PoincareConjecture.SingularLimitConclusion
