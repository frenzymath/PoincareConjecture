import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.DirectedEndpoints










set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {V : Type*} [Fintype V] (A : PreAbstractSimplicialComplex V)

open Classical in
theorem exists_surfaceDart_of_triangle_vertex
    (p : Triangle A → Fin 3 → V) (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (t : Triangle A) (v : V) (hv : v ∈ t.val) :
    ∃ d : SurfaceDart A, d.2.val = t ∧ surfaceDartStart A p hp himage sigma d = v := by
  rw [← himage t] at hv
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hv
  refine ⟨triangleIndexedDart A p hp himage t ((signedTriangleIndexRotation (sigma t)).symm k),
    rfl, ?_⟩
  rw [surfaceDartStart_indexed, Equiv.apply_symm_apply, hk]

open Classical in
theorem surfaceDart_eq_of_triangle_start_eq
    (p : Triangle A → Fin 3 → V) (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (d e : SurfaceDart A)
    (htri : d.2.val = e.2.val)
    (hstart : surfaceDartStart A p hp himage sigma d = surfaceDartStart A p hp himage sigma e) :
    d = e := by
  obtain ⟨⟨t, i⟩, rfl⟩ := triangleIndexedDart_surjective A p hp himage d
  obtain ⟨⟨u, j⟩, rfl⟩ := triangleIndexedDart_surjective A p hp himage e
  change t = u at htri
  subst u
  rw [surfaceDartStart_indexed, surfaceDartStart_indexed] at hstart
  have hij := (signedTriangleIndexRotation (sigma t)).injective ((hp t) hstart)
  exact congrArg (triangleIndexedDart A p hp himage t) hij

open Classical in
theorem surfaceDart_start_mem_triangle
    (p : Triangle A → Fin 3 → V) (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (d : SurfaceDart A) :
    surfaceDartStart A p hp himage sigma d ∈ d.2.val.val := by
  obtain ⟨⟨t, i⟩, rfl⟩ := triangleIndexedDart_surjective A p hp himage d
  rw [surfaceDartStart_indexed, triangleIndexedDart_triangle, ← himage t]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

open Classical in
theorem surfaceDart_edge_eq_endpoints
    (p : Triangle A → Fin 3 → V) (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (d : SurfaceDart A) :
    d.1.val = {surfaceDartStart A p hp himage sigma d, surfaceDartEnd A p hp himage sigma d} := by
  obtain ⟨⟨t, i⟩, rfl⟩ := triangleIndexedDart_surjective A p hp himage d
  rw [surfaceDartStart_indexed, surfaceDartEnd_indexed]
  change (Finset.univ.erase i).image (p t) =
    {p t (signedTriangleIndexRotation (sigma t) i), p t ((signedTriangleIndexRotation (sigma t)).symm i)}
  have hidx (s : ZMod 2) (k : Fin 3) :
      (Finset.univ.erase k) =
        {signedTriangleIndexRotation s k, (signedTriangleIndexRotation s).symm k} := by
    fin_cases s <;> fin_cases k <;> decide
  rw [hidx (sigma t) i, Finset.image_insert, Finset.image_singleton]

open Classical in
theorem surfaceDart_start_or_end_of_mem_edge
    (p : Triangle A → Fin 3 → V) (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (d : SurfaceDart A) (v : V) (hv : v ∈ d.1.val) :
    v = surfaceDartStart A p hp himage sigma d ∨ v = surfaceDartEnd A p hp himage sigma d := by
  rw [surfaceDart_edge_eq_endpoints A p hp himage sigma d,
    Finset.mem_insert, Finset.mem_singleton] at hv
  exact hv

end PreAbstractSimplicialComplex.ModTwoCochains
