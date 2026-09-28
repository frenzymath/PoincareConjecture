import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.VertexFibers

set_option autoImplicit false

open AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {V : Type*} [Fintype V] (A : PreAbstractSimplicialComplex V)

open Classical in
theorem surfaceVertexRotation_sameCycle_of_common_edge (number : V ↪ ℕ)
    (p : Triangle A → Fin 3 → V) (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (hordered : ∀ t, StrictMono (number ∘ p t))
    (sigma : Triangle A → ZMod 2)
    (hcancel : ∀ t u : Triangle A, t ≠ u → ∀ s : Edge A,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (sigma t + boundaryFaceParity number t.val s.val) +
        (sigma u + boundaryFaceParity number u.val s.val) = 1)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (d f : SurfaceDart A) (s : Edge A) (v : V)
    (hv : v ∈ s.val) (hsd : s.val ⊆ d.2.val.val) (hsf : s.val ⊆ f.2.val.val)
    (hd : surfaceDartStart A p hp himage sigma d = v)
    (hf : surfaceDartStart A p hp himage sigma f = v) :
    (surfaceTriangleRotation A p hp himage sigma * surfaceEdgePairing A hcofaces).SameCycle d f := by
  let alpha := surfaceEdgePairing A hcofaces
  let tau := surfaceTriangleRotation A p hp himage sigma
  let rho := tau * alpha
  by_cases he : d.2.val = f.2.val
  · have hdf := surfaceDart_eq_of_triangle_start_eq A p hp himage sigma d f he (hd.trans hf.symm)
    subst f
    exact Equiv.Perm.SameCycle.rfl
  let a : SurfaceDart A := ⟨s, d.2.val, by
    simpa only [triangleCofaces, Finset.mem_filter, Finset.mem_univ, true_and] using hsd⟩
  have halpha : (alpha a).2.val = f.2.val := by
    have hmem : f.2.val ∈ triangleCofaces A a.1 := by
      simpa only [triangleCofaces, Finset.mem_filter, Finset.mem_univ, true_and] using hsf
    rw [surfaceEdgePairing_cofaces A hcofaces a, Finset.mem_insert, Finset.mem_singleton] at hmem
    exact (hmem.resolve_left (Ne.symm he)).symm
  rcases surfaceDart_start_or_end_of_mem_edge A p hp himage sigma a v hv with hvstart | hvend
  · have hda : d = a := surfaceDart_eq_of_triangle_start_eq A p hp himage sigma d a rfl
      (hd.trans hvstart)
    have hrhotri : (rho a).2.val = f.2.val :=
      (surfaceTriangleRotation_triangle A p hp himage sigma (alpha a)).trans halpha
    have hrhostart : surfaceDartStart A p hp himage sigma (rho a) = v :=
      (surfaceVertexRotation_preserves_start A number p hp himage hordered sigma hcancel hcofaces a).trans
        hvstart.symm
    have hfrho : f = rho a := surfaceDart_eq_of_triangle_start_eq A p hp himage sigma f (rho a)
      hrhotri.symm (hf.trans hrhostart.symm)
    rw [hda, hfrho]
    exact Equiv.Perm.SameCycle.rfl.apply_right
  · have halphastart : surfaceDartStart A p hp himage sigma (alpha a) = v :=
      (surfaceEdgePairing_reverses_endpoints A number p hp himage hordered sigma hcancel hcofaces a).1.trans
        hvend.symm
    have hfa : f = alpha a := surfaceDart_eq_of_triangle_start_eq A p hp himage sigma f (alpha a)
      halpha.symm (hf.trans halphastart.symm)
    have htaustart : surfaceDartStart A p hp himage sigma (tau a) = v :=
      (surfaceTriangleRotation_start_eq_end A p hp himage sigma a).trans hvend.symm
    have hdtau : d = tau a := surfaceDart_eq_of_triangle_start_eq A p hp himage sigma d (tau a)
      (surfaceTriangleRotation_triangle A p hp himage sigma a).symm (hd.trans htaustart.symm)
    have hrho : rho (alpha a) = tau a := by
      change tau (alpha (alpha a)) = tau a
      rw [surfaceEdgePairing_involutive A hcofaces a]
    rw [hdtau, hfa, ← hrho]
    exact Equiv.Perm.SameCycle.rfl.apply_left

end PreAbstractSimplicialComplex.ModTwoCochains
