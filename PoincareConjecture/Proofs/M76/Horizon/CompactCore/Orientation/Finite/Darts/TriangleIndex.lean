import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.EdgePairing
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Simplicial.NumberedTriangleParity

set_option autoImplicit false

open AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {V : Type*} [Fintype V] (A : PreAbstractSimplicialComplex V)

open Classical in
noncomputable def triangleIndexedDart (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (t : Triangle A) (i : Fin 3) : SurfaceDart A :=
  let s := (Finset.univ.erase i).image (p t)
  have hst : s ⊆ t.val := himage t ▸ Finset.image_subset_image (Finset.erase_subset _ _)
  have hcard : s.card = 2 := by
    rw [Finset.card_image_iff.mpr (hp t).injOn]
    simp
  let e : Edge A := ⟨s, (A.isRelLowerSet_faces t.property.1).2 hst
    (Finset.card_pos.mp (by omega)), hcard⟩
  ⟨e, t, by simpa only [triangleCofaces, Finset.mem_filter, Finset.mem_univ, true_and] using hst⟩

open Classical in
theorem triangleIndexedDart_triangle (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val)
    (t : Triangle A) (i : Fin 3) :
    (triangleIndexedDart A p hp himage t i).2.val = t := rfl

open Classical in
theorem triangleIndexedDart_injective (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val) :
    Function.Injective (fun a : Triangle A × Fin 3 => triangleIndexedDart A p hp himage a.1 a.2) := by
  rintro ⟨t, i⟩ ⟨u, j⟩ he
  have htu : t = u := congrArg (fun d : SurfaceDart A => d.2.val) he
  subst u
  have hs := congrArg (fun d : SurfaceDart A => d.1.val) he
  have hij := (Finset.erase_inj (Finset.univ : Finset (Fin 3)) (Finset.mem_univ i)).mp
    (Finset.image_injective (hp t) hs)
  exact Prod.ext rfl hij

open Classical in
theorem triangleIndexedDart_surjective (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val) :
    Function.Surjective (fun a : Triangle A × Fin 3 => triangleIndexedDart A p hp himage a.1 a.2) := by
  intro d
  have hst : d.1.val ⊆ d.2.val.val := by
    simpa only [triangleCofaces, Finset.mem_filter, Finset.mem_univ, true_and] using d.2.property
  obtain ⟨i, hi⟩ := exists_triangle_edge_deleted_index (p d.2.val) (hp d.2.val)
    d.1.val d.2.val.val (himage d.2.val) hst d.1.property.2
  refine ⟨⟨d.2.val, i⟩, ?_⟩
  apply Sigma.ext (Subtype.ext hi)
  apply (Subtype.heq_iff_coe_eq (by
    intro t
    rw [show (triangleIndexedDart A p hp himage d.2.val i).1 = d.1 from Subtype.ext hi])).mpr
  rfl

open Classical in
noncomputable def surfaceDartTriangleIndexEquiv (p : Triangle A → Fin 3 → V)
    (hp : ∀ t, Function.Injective (p t))
    (himage : ∀ t, Finset.univ.image (p t) = t.val) :
    (Triangle A × Fin 3) ≃ SurfaceDart A :=
  Equiv.ofBijective _ ⟨triangleIndexedDart_injective A p hp himage,
    triangleIndexedDart_surjective A p hp himage⟩

open Classical in
theorem card_surfaceDart_eq_three_mul_triangles :
    Fintype.card (SurfaceDart A) = 3 * Fintype.card (Triangle A) := by
  have hex (t : Triangle A) : ∃ p : Fin 3 → V,
      Function.Injective p ∧ Finset.univ.image p = t.val := by
    let index := Finset.equivFinOfCardEq t.property.2
    refine ⟨fun i => (index.symm i).val, ?_, ?_⟩
    · exact Subtype.val_injective.comp index.symm.injective
    · ext v
      constructor
      · rintro hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact (index.symm i).property
      · intro hv
        exact Finset.mem_image.mpr ⟨index ⟨v, hv⟩, Finset.mem_univ _, by simp⟩
  choose p hp himage using hex
  have h := Fintype.card_congr (surfaceDartTriangleIndexEquiv A p hp himage)
  simpa [Fintype.card_prod, Nat.mul_comm] using h.symm

open Classical in
theorem twice_edges_eq_three_triangles
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    2 * Fintype.card (Edge A) = 3 * Fintype.card (Triangle A) :=
  (card_surfaceDart A hcofaces).symm.trans (card_surfaceDart_eq_three_mul_triangles A)

open Classical in
theorem even_card_triangles_of_two_cofaces
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    Even (Fintype.card (Triangle A)) := by
  have h := twice_edges_eq_three_triangles A hcofaces
  exact Nat.even_iff.mpr (by omega)

end PreAbstractSimplicialComplex.ModTwoCochains
