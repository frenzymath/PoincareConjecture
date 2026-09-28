import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.TriangleRotation

set_option autoImplicit false

open AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex.ModTwoCochains

theorem signedTriangleIndexRotation_start (s : ZMod 2) (i : Fin 3) :
    signedTriangleIndexRotation s i =
      i.succAbove (if s + (i.val : ZMod 2) = 0 then 0 else 1) := by
  fin_cases s <;> fin_cases i <;> decide

theorem signedTriangleIndexRotation_end (s : ZMod 2) (i : Fin 3) :
    (signedTriangleIndexRotation s).symm i =
      i.succAbove (if s + (i.val : ZMod 2) = 0 then 1 else 0) := by
  fin_cases s <;> fin_cases i <;> decide

private theorem opposite_endpoint_selectors (s t : ZMod 2) (h : s + t = 1) :
    (if s = 0 then (0 : Fin 2) else 1) = (if t = 0 then 1 else 0) ∧
      (if s = 0 then (1 : Fin 2) else 0) = (if t = 0 then 0 else 1) := by
  fin_cases s <;> fin_cases t <;> revert h <;> decide

variable {V : Type*} [Fintype V] (A : PreAbstractSimplicialComplex V)

open Classical in
noncomputable def surfaceDartStart (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (d : SurfaceDart A) : V :=
  let a := (surfaceDartTriangleIndexEquiv A p hp himage).symm d
  p a.1 (signedTriangleIndexRotation (sigma a.1) a.2)

open Classical in
noncomputable def surfaceDartEnd (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (d : SurfaceDart A) : V :=
  let a := (surfaceDartTriangleIndexEquiv A p hp himage).symm d
  p a.1 ((signedTriangleIndexRotation (sigma a.1)).symm a.2)

open Classical in
theorem surfaceDartStart_indexed (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (t : Triangle A) (i : Fin 3) :
    surfaceDartStart A p hp himage sigma (triangleIndexedDart A p hp himage t i) =
      p t (signedTriangleIndexRotation (sigma t) i) := by
  let index := surfaceDartTriangleIndexEquiv A p hp himage
  change p (index.symm (index (t, i))).1
    (signedTriangleIndexRotation (sigma (index.symm (index (t, i))).1)
      (index.symm (index (t, i))).2) = _
  rw [Equiv.symm_apply_apply]

open Classical in
theorem surfaceDartEnd_indexed (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (t : Triangle A) (i : Fin 3) :
    surfaceDartEnd A p hp himage sigma (triangleIndexedDart A p hp himage t i) =
      p t ((signedTriangleIndexRotation (sigma t)).symm i) := by
  let index := surfaceDartTriangleIndexEquiv A p hp himage
  change p (index.symm (index (t, i))).1
    ((signedTriangleIndexRotation (sigma (index.symm (index (t, i))).1)).symm
      (index.symm (index (t, i))).2) = _
  rw [Equiv.symm_apply_apply]

open Classical in
theorem surfaceEdgePairing_reverses_endpoints (number : V ↪ ℕ)
    (p : Triangle A → Fin 3 → V) (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (hordered : ∀ t, StrictMono (number ∘ p t))
    (sigma : Triangle A → ZMod 2)
    (hcancel : ∀ t u : Triangle A, t ≠ u → ∀ s : Edge A,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (sigma t + boundaryFaceParity number t.val s.val) +
        (sigma u + boundaryFaceParity number u.val s.val) = 1)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (d : SurfaceDart A) :
    surfaceDartStart A p hp himage sigma (surfaceEdgePairing A hcofaces d) =
        surfaceDartEnd A p hp himage sigma d ∧
      surfaceDartEnd A p hp himage sigma (surfaceEdgePairing A hcofaces d) =
        surfaceDartStart A p hp himage sigma d := by
  obtain ⟨⟨t, i⟩, hd⟩ := triangleIndexedDart_surjective A p hp himage d
  obtain ⟨⟨u, j⟩, hpair⟩ := triangleIndexedDart_surjective A p hp himage
    (surfaceEdgePairing A hcofaces d)
  have ht : d.2.val = t := (congrArg (fun a : SurfaceDart A => a.2.val) hd).symm
  have hu : (surfaceEdgePairing A hcofaces d).2.val = u :=
    (congrArg (fun a : SurfaceDart A => a.2.val) hpair).symm
  have htu : t ≠ u := by
    rw [← ht, ← hu]
    exact (surfaceEdgePairing_triangle_ne A hcofaces d).symm
  have hti : (Finset.univ.erase i).image (p t) = d.1.val :=
    congrArg (fun a : SurfaceDart A => a.1.val) hd
  have huj : (Finset.univ.erase j).image (p u) = d.1.val :=
    (congrArg (fun a : SurfaceDart A => a.1.val) hpair).trans
      (congrArg Subtype.val (surfaceEdgePairing_edge A hcofaces d))
  have hst : d.1.val ⊆ t.val := by
    rw [← ht]
    simpa only [triangleCofaces, Finset.mem_filter, Finset.mem_univ, true_and] using d.2.property
  have hsu : d.1.val ⊆ u.val := by
    rw [← hu, ← surfaceEdgePairing_edge A hcofaces d]
    simpa only [triangleCofaces, Finset.mem_filter, Finset.mem_univ, true_and] using
      (surfaceEdgePairing A hcofaces d).2.property
  have hc := hcancel t u htu d.1 hst hsu
  have htiParity := boundaryFaceParity_ordered_triangle number (p t) (hp t) (hordered t) i
  have hujParity := boundaryFaceParity_ordered_triangle number (p u) (hp u) (hordered u) j
  rw [himage t, hti] at htiParity
  rw [himage u, huj] at hujParity
  rw [htiParity, hujParity] at hc
  have horder := numbered_triangle_common_edge_order number (p t) (p u)
    (hordered t) (hordered u) i j (hti.trans huj.symm)
  obtain ⟨hstart, hend⟩ := opposite_endpoint_selectors (sigma t + (i.val : ZMod 2))
    (sigma u + (j.val : ZMod 2)) hc
  rw [← hpair, ← hd, surfaceDartStart_indexed, surfaceDartEnd_indexed,
    surfaceDartStart_indexed, surfaceDartEnd_indexed,
    signedTriangleIndexRotation_start, signedTriangleIndexRotation_start,
    signedTriangleIndexRotation_end, signedTriangleIndexRotation_end]
  constructor
  · rw [← hend]
    exact (congrFun horder _).symm
  · rw [← hstart]
    exact (congrFun horder _).symm

open Classical in
theorem surfaceTriangleRotation_start_eq_end (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2) (d : SurfaceDart A) :
    surfaceDartStart A p hp himage sigma (surfaceTriangleRotation A p hp himage sigma d) =
      surfaceDartEnd A p hp himage sigma d := by
  obtain ⟨⟨t, i⟩, rfl⟩ := triangleIndexedDart_surjective A p hp himage d
  rw [surfaceTriangleRotation_indexed, surfaceDartStart_indexed, surfaceDartEnd_indexed]
  congr 1
  generalize hs : sigma t = s
  fin_cases s <;> fin_cases i <;> dsimp only [Prod.snd] <;> decide

open Classical in
theorem surfaceVertexRotation_preserves_start (number : V ↪ ℕ)
    (p : Triangle A → Fin 3 → V) (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (hordered : ∀ t, StrictMono (number ∘ p t))
    (sigma : Triangle A → ZMod 2)
    (hcancel : ∀ t u : Triangle A, t ≠ u → ∀ s : Edge A,
      s.val ⊆ t.val → s.val ⊆ u.val →
      (sigma t + boundaryFaceParity number t.val s.val) +
        (sigma u + boundaryFaceParity number u.val s.val) = 1)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (d : SurfaceDart A) :
    surfaceDartStart A p hp himage sigma
        ((surfaceTriangleRotation A p hp himage sigma * surfaceEdgePairing A hcofaces) d) =
      surfaceDartStart A p hp himage sigma d := by
  change surfaceDartStart A p hp himage sigma
    (surfaceTriangleRotation A p hp himage sigma (surfaceEdgePairing A hcofaces d)) = _
  rw [surfaceTriangleRotation_start_eq_end]
  exact (surfaceEdgePairing_reverses_endpoints A number p hp himage hordered sigma hcancel hcofaces d).2

open Classical in
theorem surfaceVertexRotation_ne_self (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (sigma : Triangle A → ZMod 2)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (d : SurfaceDart A) :
    (surfaceTriangleRotation A p hp himage sigma * surfaceEdgePairing A hcofaces) d ≠ d := by
  intro he
  have ht := congrArg (fun a : SurfaceDart A => a.2.val) he
  change (surfaceTriangleRotation A p hp himage sigma (surfaceEdgePairing A hcofaces d)).2.val = _ at ht
  rw [surfaceTriangleRotation_triangle] at ht
  exact surfaceEdgePairing_triangle_ne A hcofaces d ht

end PreAbstractSimplicialComplex.ModTwoCochains
