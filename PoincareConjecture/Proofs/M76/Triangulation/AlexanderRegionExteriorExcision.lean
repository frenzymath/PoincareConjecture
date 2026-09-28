import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionProtectedExcision
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalPartition
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall












set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem alexander_attached_spherical_exterior_ball {b c d q U V D : Set E}
    (hdim : Module.finrank ℝ E = 3)
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUD : closure U ⊆ interior D) (hVD : closure V ⊆ interior D)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d)
    (hinter : closure U ∩ closure V = d)
    (hUB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure U) (b ∪ d))
    (hVB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure V) (c ∪ d))
    (hUE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) ((b ∪ d) ×ˢ {1}))
    (hVE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1}) ((c ∪ d) ×ˢ {1}))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hKD : K.space = D) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (closure ((frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) \
        closure V ×ˢ {1})) ((b ∪ c) ×ˢ {1}) := by
  let S := frontier (D ×ˢ Icc (-1 : ℝ) 1)
  have hUD' : closure U ⊆ D := hUD.trans interior_subset
  have hVD' : closure V ⊆ D := hVD.trans interior_subset
  have hUout : closure U ⊆ Vᶜ := by
    intro x hxU hxV
    have hxd : x ∈ d := hinter.subset ⟨hxU, subset_closure hxV⟩
    have hxf : x ∈ frontier V := hVf.symm.subset (Or.inr hxd)
    exact hxf.2 (hV.interior_eq.symm ▸ hxV)
  have hVout : closure V ⊆ Uᶜ := by
    intro x hxV hxU
    have hxd : x ∈ d := hinter.subset ⟨subset_closure hxU, hxV⟩
    have hxf : x ∈ frontier U := hUf.symm.subset (Or.inr hxd)
    exact hxf.2 (hU.interior_eq.symm ▸ hxU)
  have hsB : closure V ×ˢ {(1 : ℝ)} ⊆ S \ U ×ˢ {1} := by
    rintro x ⟨hxV, hxone⟩
    exact ⟨prod_singleton_one_subset_frontier_cylinder hVD' ⟨hxV, hxone⟩,
      fun hx => hVout hxV hx.1⟩
  have hOI : closure U ×ˢ {(1 : ℝ)} ⊆ S \ V ×ˢ {1} := by
    rintro x ⟨hxU, hxone⟩
    exact ⟨prod_singleton_one_subset_frontier_cylinder hUD' ⟨hxU, hxone⟩,
      fun hx => hUout hxU hx.1⟩
  have hUb := hUB.prod_singleton (1 : ℝ)
  have hVb := hVB.prod_singleton (1 : ℝ)
  have hUi := hUE
  have hVi := hVE
  rw [union_prod] at hUb hVb hUi hVi
  have hbd' : (b ×ˢ {(1 : ℝ)}) ∩ (d ×ˢ {1}) = q ×ˢ {1} := by
    rw [← inter_prod, hbd]
  have hcd' : (c ×ˢ {(1 : ℝ)}) ∩ (d ×ˢ {1}) = q ×ˢ {1} := by
    rw [← inter_prod, hcd]
  have hsi : (closure V ×ˢ {(1 : ℝ)}) ∩ (S \ V ×ˢ {1}) =
      (c ×ˢ {1}) ∪ (d ×ˢ {1}) := by
    rw [top_face_inter_cylinderExterior hV hVD', hVf, union_prod]
  have hbo : (S \ U ×ˢ {(1 : ℝ)}) ∩ (closure U ×ˢ {1}) =
      (b ×ˢ {1}) ∪ (d ×ˢ {1}) := by
    rw [inter_comm, top_face_inter_cylinderExterior hU hUD', hUf, union_prod]
  have hso : (closure V ×ˢ {(1 : ℝ)}) ∩ (closure U ×ˢ {1}) = d ×ˢ {1} := by
    rw [← inter_prod, inter_comm, hinter]
  have hcover : (S \ U ×ˢ {(1 : ℝ)}) ∪ (closure U ×ˢ {1}) = S := by
    rw [union_comm]
    exact top_face_union_cylinderExterior hUD'
  have hinner : (closure V ×ˢ {(1 : ℝ)}) ∪ (S \ V ×ˢ {1}) = S :=
    top_face_union_cylinderExterior hVD'
  have hball := hUi.excision_of_spherical_balls_in_top_face hdim hUb hVb hVi
    (hc.prod_singleton (1 : ℝ)) (hb.prod_singleton (1 : ℝ))
    (hd.prod_singleton (1 : ℝ)) hcd' hbd' hsB hOI hsi hbo hso hcover hinner
    (prod_mono hVD Subset.rfl) K hK hD hcv hne hKD
  simpa only [union_prod, union_comm] using hball

end Set
