import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_CanonicalScalar











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44




theorem exists_scalar_doubling_constant (P : M44CapPersistencePredecessors.{u}) (C : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (F : SurgeryFlowData.{u}) {a b : ℝ}
      (S : SurgeryRegularSlab F.slice F.metric a b) (U : Set (F.slice a).carrier)
      {q M : ℝ}, 0 < M → q ≤ M →
      (∀ t : Ico a b, ∀ x ∈ U, q ≤ (S.flow.connection t.1).scalarCurvature x →
        SurgeryCanonicalControl F t.1 (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ x)
          F.parameters.epsilon C ∧
        ¬ ∃ N : SingularCComponent (F.metric t.1) (F.connection t.1) C,
          S.identify ⟨t.1, t.2.1, t.2.2.le⟩ x ∈ N.carrier) →
      (∀ x ∈ U, (S.flow.connection a).scalarCurvature x ≤ M) →
      8 * L * M * (b - a) ≤ 1 →
      ∀ t ∈ Icc a b, ∀ x ∈ U, (S.flow.connection t).scalarCurvature x ≤ 2 * M := by
  obtain ⟨L, hL, hbound⟩ := exists_surgery_canonical_scalar_evolution_bound P C
  refine ⟨L, hL, ?_⟩
  intro F a b S U q M hM hq hcanonical hinitial htime t ht x hx
  let f (s : ℝ) := (S.flow.connection s).scalarCurvature x
  let d (s : ℝ) := (S.flow.connection s).laplacian
    (S.flow.connection s).scalarCurvature x + 2 * (S.flow.connection s).ricciNormSq x
  have hcont : ContinuousOn f (Icc a b) := by
    intro s hs
    exact (P.curvature.scalar_evolution 3 (F.slice a).carrier
      (Icc a b) S.flow s hs x).continuousWithinAt
  have hderiv (s : ℝ) (hs : s ∈ Ico a b) : HasDerivWithinAt f (d s) (Ici s) s := by
    apply (P.curvature.scalar_evolution 3 (F.slice a).carrier (Icc a b)
      S.flow s ⟨hs.1, hs.2.le⟩ x).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE hs.2)
      (fun y hy => ⟨hs.1.trans hy.1, hy.2⟩)
  have hrate (s : ℝ) (hs : s ∈ Ico a b) (hhigh : q ≤ f s) : d s ≤ L * f s ^ 2 := by
    obtain ⟨hc, hn⟩ := hcanonical ⟨s, hs⟩ x hx hhigh
    have hh := hbound F s (S.identify ⟨s, hs.1, hs.2.le⟩ x) hc hn
    rw [regularSlab_scalar_eq F S ⟨s, hs.1, hs.2.le⟩ x,
      ← regularSlab_scalar_evolution_eq P F S ⟨s, hs.1, hs.2.le⟩ x] at hh
    exact (le_abs_self (d s)).trans hh
  exact le_two_mul_of_deriv_le_sq_above hL hM hq hcont hderiv
    (hinitial x hx) hrate htime t ht

end PoincareConjecture.M44
