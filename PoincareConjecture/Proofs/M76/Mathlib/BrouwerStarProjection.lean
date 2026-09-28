import PoincareConjecture.Proofs.M76.Mathlib.VertexStarSecantBound
import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import PoincareConjecture.Proofs.M76.Mathlib.TransversePlaneDimension
import Mathlib.Analysis.Normed.Affine.AddTorsorBases











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem nonempty_vertexStarPlanes_of_affineOnFaces (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) {p : E} (hp : {p} ∈ K.faces)
    (f : E → F) (hf : (K.closedFaceStar {p}).AffineOnFaces f)
    (hinj : InjOn f (K.closedFaceStar {p}).space)
    (hfull : (interior (f '' (K.closedFaceStar {p}).space)).Nonempty) :
    Nonempty (SecantTransversePlaneSpace (Module.finrank ℝ F) (K.closedFaceStar {p}).space) := by
  obtain ⟨a, hav⟩ := hK.exists_continuousAffineMap_eqOn f
  have hva : EqOn a f (K.closedFaceStar {p}).vertices :=
    fun x hx => hav (K.closedFaceStar_le {p} hx)
  have haf := ((K.closedFaceStar {p}).affineOnFaces_affine a).eqOn_of_eqOn_vertices hf hva
  have hQ : InjOn a.contLinear (K.closedFaceStar {p}).space := by
    intro x hx y hy he
    have hvsub := a.contLinear_map_vsub x y
    change a.contLinear (x - y) = a x - a y at hvsub
    rw [map_sub, he, sub_self] at hvsub
    exact hinj hx hy ((haf hx).symm.trans ((sub_eq_zero.mp hvsub.symm).trans (haf hy)))
  obtain ⟨c, hc, hb⟩ := K.exists_pos_secant_bound_vertexStar hK hp a.contLinear hQ
  have htrans := Submodule.isSecantTransverse_ker_of_lower_bound a.contLinear hc hb
  let R : AffineSubspace ℝ F := AffineSubspace.map a.toAffineMap ⊤
  have himage : f '' (K.closedFaceStar {p}).space ⊆ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, AffineSubspace.mem_top ℝ E x, haf hx⟩
  have htop : R = ⊤ := by
    apply top_unique
    rw [← isOpen_interior.affineSpan_eq_top hfull]
    exact affineSpan_le.mpr (interior_subset.trans himage)
  have hasurj : Function.Surjective a := by
    intro y
    have hy : y ∈ R := by rw [htop]; trivial
    obtain ⟨x, _, he⟩ := hy
    exact ⟨x, he⟩
  have hsurj : Function.Surjective a.contLinear := a.toAffineMap.linear_surjective_iff.mpr hasurj
  have hrange : LinearMap.range a.contLinear.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := a.contLinear.toLinearMap.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hdim
  refine ⟨⟨⟨a.contLinear.ker⟩, ?_, htrans⟩⟩
  change Module.finrank ℝ a.contLinear.ker + Module.finrank ℝ F = Module.finrank ℝ E
  omega

end Geometry.SimplicialComplex
