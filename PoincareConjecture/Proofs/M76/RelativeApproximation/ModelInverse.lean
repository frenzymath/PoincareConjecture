import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {X E ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {R C : Set X}

theorem exists_polyhedral_PL_model_inverse
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (H : C ≃ₜ K.space) (F : X → E) (hCR : C ⊆ R) (x0 : R)
    (hHF : ∀ x : C, (H x : E) = F x)
    (hcharts : ∀ x ∈ C,
      ∃ (i : ι) (V : Set X) (a : E →ᴬ[ℝ] (Fin 3 → ℝ)),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V) :
    ∃ f : E → R, ContinuousOn f K.space ∧
      (∀ z : K.space, (f z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (f z : X)) K.space := by
  classical
  let f : E → R := fun z => if hz : z ∈ K.space then
    ⟨H.symm ⟨z, hz⟩, hCR (H.symm ⟨z, hz⟩).property⟩ else x0
  have hval (z : E) (hz : z ∈ K.space) :
      (f z : X) = (H.symm ⟨z, hz⟩ : X) := by
    simp only [f, dif_pos hz]
  have hfc : ContinuousOn f K.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hcont : Continuous (fun z : K.space =>
        (⟨H.symm z, hCR (H.symm z).property⟩ : R)) :=
      (continuous_subtype_val.comp H.symm.continuous).subtype_mk _
    apply hcont.congr
    intro z
    exact Subtype.ext (hval z z.property).symm
  have hfC : MapsTo (fun z => (f z : X)) K.space C := by
    intro z hz
    change (f z : X) ∈ C
    rw [hval z hz]
    exact (H.symm ⟨z, hz⟩).property
  have hFf : EqOn (F ∘ (fun z => (f z : X))) id K.space := by
    intro z hz
    change F (f z) = z
    rw [hval z hz]
    exact (hHF (H.symm ⟨z, hz⟩)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨z, hz⟩))
  refine ⟨f, hfc, fun z => hval z z.property, ?_⟩
  exact polyhedralPLInCharts_of_affine_projections e F C hcharts K hK
    (continuous_subtype_val.comp_continuousOn hfc) hfC
    ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).finitePiecewiseAffineOn hK) hFf

end PoincareConjecture.M76
