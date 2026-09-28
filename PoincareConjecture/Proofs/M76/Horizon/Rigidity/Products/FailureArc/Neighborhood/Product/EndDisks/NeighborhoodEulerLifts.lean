import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks

theorem exists_finitePL_lift_of_original_embedding
    {E G V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K : SimplicialComplex ℝ E) {S : Set X} (H : K.space ≃ₜ S)
    (a : E → X) (ha : PolyhedralPLInCharts e a K.space)
    (haval : ∀ x : K.space, a x = (H x : X))
    (J : SimplicialComplex ℝ G) (hJ : J.faces.Finite)
    (f : G → X) (hf : PolyhedralPLInCharts e f J.space)
    (hfi : InjOn f J.space) (hfS : MapsTo f J.space S) :
    ∃ g : G → E, FinitePiecewiseAffineOn g J.space ∧ InjOn g J.space ∧
      MapsTo g J.space K.space ∧ ∀ z ∈ J.space, a (g z) = f z := by
  classical
  let v : J.space → S := fun z => ⟨f z,hfS z.property⟩
  have hv : Continuous v := hf.continuousOn.domRestrict.subtype_mk _
  let g : G → E := fun z => if hz : z ∈ J.space then (H.symm (v ⟨z,hz⟩) : E) else 0
  have hgval (z : J.space) : g z = (H.symm (v z) : E) := dif_pos z.property
  have hgK : MapsTo g J.space K.space := by
    intro z hz
    rw [hgval ⟨z,hz⟩]
    exact (H.symm (v ⟨z,hz⟩)).property
  have hgf (z : G) (hz : z ∈ J.space) : a (g z) = f z := by
    rw [hgval ⟨z,hz⟩,haval,H.apply_symm_apply]
  have hgc : ContinuousOn g J.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp (H.symm.continuous.comp hv)).congr
      (fun z => (hgval z).symm)
  have hai : InjOn a K.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((haval ⟨x,hx⟩).symm.trans (hxy.trans (haval ⟨y,hy⟩)))))
  have hcomposed : PolyhedralPLInCharts e (a ∘ g) J.space :=
    hf.congr (fun z hz => (hgf z hz).symm)
  refine ⟨g,ha.finitePiecewiseAffineOn_lift hcompat hai J hJ hgc hgK hcomposed,?_,hgK,hgf⟩
  intro x hx y hy hxy
  exact hfi hx hy ((hgf x hx).symm.trans ((congrArg a hxy).trans (hgf y hy)))

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
