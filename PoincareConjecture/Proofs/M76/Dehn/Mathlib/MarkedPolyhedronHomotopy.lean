import PoincareConjecture.Proofs.M76.Dehn.Mathlib.MarkedSimplicialApproximation
import Mathlib.Topology.Homotopy.Affine











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]





theorem exists_marked_finitePL_homotopy
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (P Z : SimplicialComplex ℝ G) (hP : P.faces.Finite) (hZP : Z ≤ P)
    (f : C(K.space, P.space)) (B : Set K.space) (hB : IsCompact B)
    (O : Set G) (hO : IsOpen ((Subtype.val : Z.space → G) ⁻¹' O))
    (hBO : MapsTo (fun x : K.space => (f x : G)) B (O ∩ Z.space)) :
    ∃ (g : E → G) (a : C(K.space, P.space)),
      FinitePiecewiseAffineOn g K.space ∧
      (∀ x : K.space, (a x : G) = g x) ∧
      ∃ H : f.Homotopy a,
        ∀ (t : unitInterval) (x : K.space), x ∈ B → (H (t, x) : G) ∈ O ∩ Z.space := by
  obtain ⟨g, hg, hall, hmark⟩ :=
    K.exists_marked_finitePL_approximation hK P Z hP hZP f B hB O hO hBO
  have hgc : Continuous (fun x : K.space => g x) :=
    hg.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property)
  let a : C(K.space, P.space) :=
    ⟨fun x => ⟨g x, hall x (right_mem_segment ℝ _ _)⟩, hgc.subtype_mk _⟩
  let fG : C(K.space, G) :=
    ⟨fun x => (f x : G), continuous_subtype_val.comp f.continuous⟩
  let gG : C(K.space, G) := ⟨fun x => g x, hgc⟩
  let H₀ := ContinuousMap.Homotopy.affine fG gG
  have hsegment (z : unitInterval × K.space) :
      H₀ z ∈ segment ℝ (f z.2 : G) (g z.2) :=
    lineMap_mem_segment ℝ _ _ z.1.property
  let H : f.Homotopy a :=
    { toFun := fun z => ⟨H₀ z, hall z.2 (hsegment z)⟩
      continuous_toFun := H₀.continuous.subtype_mk _
      map_zero_left := fun x => Subtype.ext (H₀.map_zero_left x)
      map_one_left := fun x => Subtype.ext (H₀.map_one_left x) }
  exact ⟨g, a, hg, fun _ => rfl, H, fun t x hx => hmark x hx (hsegment (t, x))⟩

end Geometry.SimplicialComplex
