import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polygons.Mathlib.TriangleChainCoordinates
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fintype.EquivFin

/-!
# Pairing the actual triangle incidences across original edges

Each dart retains an original edge and one of its actual triangle
cofaces. The two-coface hypothesis constructs the edge-preserving swap,
and its sign is computed from its literal fixed-point-free involution.
This is the edge permutation in the finite orientation argument of
Wall derivation 019.
-/

set_option autoImplicit false

open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {V : Type*} [Fintype V] (A : PreAbstractSimplicialComplex V)

/-- An original edge with one of its actual triangular cofaces. -/
abbrev SurfaceDart := (e : Edge A) × (triangleCofaces A e)

open Classical in
noncomputable def surfaceEdgePairing
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    Equiv.Perm (SurfaceDart A) :=
  Equiv.sigmaCongrRight fun e =>
    let index := Finset.equivFinOfCardEq (hcofaces e)
    (index.trans (Equiv.swap (0 : Fin 2) 1)).trans index.symm

theorem surfaceEdgePairing_edge
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (d : SurfaceDart A) : (surfaceEdgePairing A hcofaces d).1 = d.1 := rfl

theorem surfaceEdgePairing_involutive
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    Function.Involutive (surfaceEdgePairing A hcofaces) := by
  classical
  rintro ⟨e, t⟩
  simp [surfaceEdgePairing]

theorem surfaceEdgePairing_ne_self
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (d : SurfaceDart A) : surfaceEdgePairing A hcofaces d ≠ d := by
  classical
  rcases d with ⟨e, t⟩
  intro he
  have ht := (Sigma.mk.inj_iff.mp he).2
  have hte : ((Finset.equivFinOfCardEq (hcofaces e)).symm
      (Equiv.swap (0 : Fin 2) 1 (Finset.equivFinOfCardEq (hcofaces e) t))) = t :=
    eq_of_heq ht
  have hi := congrArg (Finset.equivFinOfCardEq (hcofaces e)) hte
  simp only [Equiv.apply_symm_apply] at hi
  generalize hx : Finset.equivFinOfCardEq (hcofaces e) t = x at hi
  fin_cases x <;> norm_num [Equiv.swap_apply_def] at hi

theorem surfaceEdgePairing_triangle_ne
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (d : SurfaceDart A) : (surfaceEdgePairing A hcofaces d).2.val ≠ d.2.val := by
  rcases d with ⟨e, t⟩
  intro he
  apply surfaceEdgePairing_ne_self A hcofaces ⟨e, t⟩
  apply Sigma.ext (surfaceEdgePairing_edge A hcofaces ⟨e, t⟩)
  exact heq_of_eq (Subtype.ext he)

open Classical in
theorem surfaceEdgePairing_cofaces
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (d : SurfaceDart A) :
    triangleCofaces A d.1 = {d.2.val, (surfaceEdgePairing A hcofaces d).2.val} := by
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact d.2.property
    · rw [Finset.mem_singleton] at ht
      subst t
      exact (surfaceEdgePairing A hcofaces d).2.property
  · rw [hcofaces, Finset.card_pair (surfaceEdgePairing_triangle_ne A hcofaces d).symm]

open Classical in
theorem card_surfaceDart
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    Fintype.card (SurfaceDart A) = 2 * Fintype.card (Edge A) := by
  classical
  simp only [SurfaceDart, Fintype.card_sigma, Fintype.card_coe, hcofaces,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

open Classical in
theorem sign_surfaceEdgePairing
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    Equiv.Perm.sign (surfaceEdgePairing A hcofaces) =
      (-1 : ℤˣ) ^ Fintype.card (Edge A) := by
  classical
  have hsq : surfaceEdgePairing A hcofaces ^ 2 = 1 := by
    apply Equiv.ext
    intro d
    exact surfaceEdgePairing_involutive A hcofaces d
  let : IsEmpty (Function.fixedPoints (surfaceEdgePairing A hcofaces)) :=
    ⟨fun d => surfaceEdgePairing_ne_self A hcofaces d.val d.property⟩
  have hzero : Fintype.card (Function.fixedPoints (surfaceEdgePairing A hcofaces)) = 0 :=
    Fintype.card_eq_zero
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, hzero,
    Nat.sub_zero, card_surfaceDart A hcofaces]
  simp

end PreAbstractSimplicialComplex.ModTwoCochains
