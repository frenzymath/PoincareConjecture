import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Bounds.NeckScalarRate
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Round.RoundScalarRate
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Bounds.ForwardScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Bounds.SlabScalarTransport

/-!
# The canonical scalar rate outside compact C-components

Necks, caps and round components give one constant chosen before the
flow. The actual ordinary-slab identifications then transport this
estimate to the time derivative in Lemma 11.2, pp. 268-269, as used in
Lemma 16.8, pp. 372-373. See M44 derivation 32.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

/-- A common scalar-evolution bound on the three controlled canonical
alternatives. The compact C-component alternative must be excluded by
the tracked collar. Source: Lemma 11.2 in Lemma 16.8; M44 derivation 32. -/
theorem exists_surgery_canonical_scalar_evolution_bound
    (P : M44CapPersistencePredecessors.{u}) (C : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (F : SurgeryFlowData.{u}) (t : ℝ)
      (x : (F.slice t).carrier),
      SurgeryCanonicalControl F t x F.parameters.epsilon C →
      (¬ ∃ N : SingularCComponent (F.metric t) (F.connection t) C, x ∈ N.carrier) →
        |(F.connection t).laplacian (F.connection t).scalarCurvature x +
            2 * (F.connection t).ricciNormSq x| ≤
          L * (F.connection t).scalarCurvature x ^ 2 := by
  obtain ⟨Lneck, hLneck, hneck⟩ := exists_neck_scalar_evolution_bound P
  obtain ⟨Lround, _, hround⟩ := exists_round_scalar_evolution_bound P
  let L := max C (max Lneck Lround)
  have hC : C ≤ L := le_max_left _ _
  have hN : Lneck ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hR : Lround ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨L, hLneck.trans_le hN, ?_⟩
  intro F t x hcanonical hcomponent
  cases hcanonical with
  | neck N hcenter =>
      have hsmall : N.neck.epsilon ≤ 1 / 200 :=
        N.epsilon_eq.le.trans F.parameters.epsilon_le
      obtain ⟨hepsilon, horder⟩ := canonical_epsilon_fourJet_order N.neck.epsilon_pos hsmall
      have h := hneck N.neck hepsilon horder N.neck.center
        (N.neck.central_sphere_subset N.neck.center_on_central_sphere)
      rw [N.connection_eq, hcenter] at h
      exact h.trans (mul_le_mul_of_nonneg_right hN (sq_nonneg _))
  | cap N _ hconstant hconnection hx =>
      obtain ⟨B, hB, hbound⟩ := N.laplacian_bound
      have h := hbound x (N.core_subset_carrier hx)
      rw [hconnection] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        ((hB.le.trans hconstant).trans hC) (sq_nonneg _))
  | component N hx => exact (hcomponent ⟨N, hx⟩).elim
  | round N hx =>
      exact (hround (F.connection t) N F.parameters.epsilon_le x hx).trans
        (mul_le_mul_of_nonneg_right hR (sq_nonneg _))

/-- The scalar rate on an actual ordinary slab, with canonicality
tested at its corresponding changing-carrier point. Source:
Lemma 11.2 in Lemma 16.8, pp. 372-373; M44 derivation 32. -/
theorem exists_surgery_canonical_scalar_rate_within
    (P : M44CapPersistencePredecessors.{u}) (C : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (F : SurgeryFlowData.{u}) {a b : ℝ}
      (S : SurgeryRegularSlab F.slice F.metric a b) (t : Icc a b)
      (x : (F.slice a).carrier),
      SurgeryCanonicalControl F t.1 (S.identify t x) F.parameters.epsilon C →
      (¬ ∃ N : SingularCComponent (F.metric t.1) (F.connection t.1) C,
        S.identify t x ∈ N.carrier) → ∃ d : ℝ,
      HasDerivWithinAt (fun s => (S.flow.connection s).scalarCurvature x) d (Icc a b) t.1 ∧
        |d| ≤ L * (S.flow.connection t.1).scalarCurvature x ^ 2 := by
  obtain ⟨L, hL, hbound⟩ := exists_surgery_canonical_scalar_evolution_bound P C
  refine ⟨L, hL, ?_⟩
  intro F a b S t x hcanonical hcomponent
  have h := hbound F t.1 (S.identify t x) hcanonical hcomponent
  rw [regularSlab_scalar_eq F S t x] at h
  refine ⟨_, P.curvature.scalar_evolution 3 (F.slice a).carrier (Icc a b)
    S.flow t.1 t.2 x, ?_⟩
  rw [regularSlab_scalar_evolution_eq P F S t x]
  exact h

end PoincareMT.M44
