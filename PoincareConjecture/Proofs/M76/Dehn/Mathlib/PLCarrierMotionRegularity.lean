import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMotion
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLTransport










set_option autoImplicit false

open Set unitInterval

namespace Geometry.PLCarrierMotion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C P : Set E} {ε : ℝ}




theorem finitePiecewiseAffineOn_carrier
    (H : PLCarrierMotion C P ε) (t : I) :
    FinitePiecewiseAffineOn (H.map t : E → E) C := by
  obtain ⟨d, hd, hval⟩ := H.finitePL t
  obtain ⟨f, hf, hfval⟩ := hd
  apply hf.congr
  intro x hx
  exact (hfval ⟨x, hx⟩).symm.trans (hval ⟨x, hx⟩)




theorem finitePiecewiseAffineOn_finite_polyhedron [FiniteDimensional ℝ E]
    (H : PLCarrierMotion C P ε) (t : I)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn (H.map t : E → E) K.space ∧
      FinitePiecewiseAffineOn ((H.map t).symm : E → E) K.space := by
  have hglobal (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) :
      FinitePiecewiseAffineOn (H.map t : E → E) L.space :=
    (H.finitePiecewiseAffineOn_carrier t).homeomorph_on_finite_polyhedron_of_eq_id_off
      (fun x hx => H.outside t x (fun hi => hx (interior_subset hi))) L hL
  exact ⟨hglobal K hK,
    (H.map t).finitePiecewiseAffineOn_symm_of_forall_finite_polyhedron hglobal K hK⟩




theorem mem_superset_iff (H : PLCarrierMotion C P ε)
    {U : Set E} (hCU : C ⊆ U) (t : I) (x : E) :
    H.map t x ∈ U ↔ x ∈ U := by
  have hfixed (y : E) (hy : y ∉ U) : H.map t y = y :=
    H.outside t y (fun hi => hy (hCU (interior_subset hi)))
  constructor
  · intro hx
    by_contra hn
    exact hn ((hfixed x hn) ▸ hx)
  · intro hx
    by_contra hn
    have heq : H.map t (H.map t x) = H.map t x := hfixed _ hn
    have hpoint : H.map t x = x := (H.map t).injective heq
    exact hn (hpoint.symm ▸ hx)

end Geometry.PLCarrierMotion
