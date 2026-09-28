import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.TriangleIndex
import Mathlib.GroupTheory.Perm.Fin










set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {V : Type*} [Fintype V] (A : PreAbstractSimplicialComplex V)

noncomputable def signedTriangleIndexRotation (s : ZMod 2) : Equiv.Perm (Fin 3) :=
  if s = 0 then finRotate 3 else (finRotate 3).symm

theorem sign_signedTriangleIndexRotation (s : ZMod 2) :
    Equiv.Perm.sign (signedTriangleIndexRotation s) = 1 := by
  by_cases hs : s = 0 <;> simp [signedTriangleIndexRotation, hs]

theorem signedTriangleIndexRotation_cube (s : ZMod 2) :
    signedTriangleIndexRotation s ^ 3 = 1 := by
  by_cases hs : s = 0 <;> simp only [signedTriangleIndexRotation, hs, if_true, if_false]
  all_goals decide

theorem signedTriangleIndexRotation_ne_self (s : ZMod 2) (i : Fin 3) :
    signedTriangleIndexRotation s i ≠ i := by
  by_cases hs : s = 0 <;> simp only [signedTriangleIndexRotation, hs, if_true, if_false]
  all_goals fin_cases i <;> decide

open Classical in
noncomputable def surfaceTriangleRotation (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) : Equiv.Perm (SurfaceDart A) :=
  let index := surfaceDartTriangleIndexEquiv A p hp himage
  (index.symm.trans (Equiv.prodCongrRight fun t => signedTriangleIndexRotation (sigma t))).trans index

open Classical in
theorem surfaceTriangleRotation_indexed (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (t : Triangle A) (i : Fin 3) :
    surfaceTriangleRotation A p hp himage sigma (triangleIndexedDart A p hp himage t i) =
      triangleIndexedDart A p hp himage t (signedTriangleIndexRotation (sigma t) i) := by
  let index := surfaceDartTriangleIndexEquiv A p hp himage
  change index ((Equiv.prodCongrRight fun t => signedTriangleIndexRotation (sigma t))
    (index.symm (index (t, i)))) = index (t, signedTriangleIndexRotation (sigma t) i)
  rw [Equiv.symm_apply_apply]
  rfl

open Classical in
theorem surfaceTriangleRotation_triangle (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (d : SurfaceDart A) :
    (surfaceTriangleRotation A p hp himage sigma d).2.val = d.2.val := by
  obtain ⟨⟨t, i⟩, rfl⟩ := triangleIndexedDart_surjective A p hp himage d
  rw [surfaceTriangleRotation_indexed]
  rfl

open Classical in
theorem sign_surfaceTriangleRotation (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) :
    Equiv.Perm.sign (surfaceTriangleRotation A p hp himage sigma) = 1 := by
  let index := surfaceDartTriangleIndexEquiv A p hp himage
  let rot := Equiv.prodCongrRight fun t => signedTriangleIndexRotation (sigma t)
  have he := Equiv.Perm.sign_eq_sign_of_equiv
    (surfaceTriangleRotation A p hp himage sigma) rot index.symm (by
      intro d
      simp [surfaceTriangleRotation, index, rot])
  rw [he, Equiv.Perm.sign_prodCongrRight]
  simp only [sign_signedTriangleIndexRotation, Finset.prod_const_one]

open Classical in
theorem sign_surfaceVertexRotation (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    Equiv.Perm.sign (surfaceTriangleRotation A p hp himage sigma * surfaceEdgePairing A hcofaces) =
      (-1 : ℤˣ) ^ Fintype.card (Edge A) := by
  rw [map_mul, sign_surfaceTriangleRotation, one_mul, sign_surfaceEdgePairing]

end PreAbstractSimplicialComplex.ModTwoCochains
