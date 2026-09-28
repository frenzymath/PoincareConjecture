import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse
import PoincareConjecture.Proofs.M76.RelativeApproximation.Mathlib.CompactRelativeNeighborhood
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram
import PoincareConjecture.Proofs.M76.Mathlib.RelativeManifoldPLApproximation

set_option autoImplicit false

open Set Geometry unitInterval

namespace PoincareConjecture.M76

variable {X E ι κ : Type*} [TopologicalSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {R C : Set X} {U : Set R}

theorem exists_retained_model_approximation
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (d : κ → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (hidentity : ChartwisePLOn e d (ContinuousMap.id R) U)
    (hCR : C ⊆ interior R)
    (hfront : frontier C ⊆ (Subtype.val : R → X) '' U)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (H : C ≃ₜ K.space) (F : X → E) (x0 : R)
    (hHF : ∀ x : C, (H x : E) = F x)
    (hcharts : ∀ x ∈ C,
      ∃ (i : ι) (V : Set X) (a : E →ᴬ[ℝ] (Fin 3 → ℝ)),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V) :
    ∃ (q : E → X) (T : C(I × K.space, X)) (V : Set C),
      PolyhedralPLInCharts d q K.space ∧ MapsTo q K.space (interior R) ∧
      (∀ z, T z ∈ interior R) ∧ IsOpen V ∧
      (Subtype.val : C → X) ⁻¹' frontier C ⊆ V ∧
      (∀ z : K.space, T (0, z) = (H.symm z : X)) ∧
      (∀ z : K.space, T (1, z) = q z) ∧
      ∀ (t : I) (x : C), x ∈ V → T (t, H x) = (x : X) := by
  classical
  let : LocallyCompactSpace X := hidentity.source_domain.locallyCompactSpace
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (K.isCompact_space_of_finite hK)
  obtain ⟨f, hfc, hfval, _⟩ := exists_polyhedral_PL_model_inverse
    e K hK H F (hCR.trans interior_subset) x0 hHF hcharts
  let fK : C(K.space, R) :=
    ⟨fun z => f z, hfc.comp_continuous continuous_subtype_val (fun z => z.property)⟩
  let Z : Set K.space := (fun z => (fK z : X)) ⁻¹' frontier C
  let O : Set K.space := fK ⁻¹' U
  have hZ : IsCompact Z :=
    (isClosed_frontier.preimage (continuous_subtype_val.comp fK.continuous)).isCompact
  have hO : IsOpen O := hidentity.open_domain.preimage fK.continuous
  have hZO : Z ⊆ O := by
    intro z hz
    obtain ⟨y, hy, heq⟩ := hfront hz
    have hyf : y = fK z := Subtype.ext heq
    change fK z ∈ U
    rwa [← hyf]
  obtain ⟨L, V, hL, hLK, hV, hZV, hVL, hLO⟩ :=
    K.exists_compact_relative_polyhedral_neighborhood hK hZ hO hZO
  have hfC : MapsTo (fun z => (f z : X)) L.space C := by
    intro z hz
    change (f z : X) ∈ C
    rw [hfval ⟨z, hLK hz⟩]
    exact (H.symm ⟨z, hLK hz⟩).property
  have hFf : EqOn (F ∘ (fun z => (f z : X))) id L.space := by
    intro z hz
    change F (f z) = z
    rw [hfval ⟨z, hLK hz⟩]
    exact (hHF (H.symm ⟨z, hLK hz⟩)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨z, hLK hz⟩))
  have hfe : PolyhedralPLInCharts e (fun z => (f z : X)) L.space :=
    polyhedralPLInCharts_of_affine_projections e F C hcharts L hL
      (continuous_subtype_val.comp_continuousOn (hfc.mono hLK)) hfC
      ((L.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).finitePiecewiseAffineOn hL) hFf
  have hfU : MapsTo f L.space U := fun z hz =>
    hLO (show (⟨z, hLK hz⟩ : K.space) ∈ Subtype.val ⁻¹' L.space from hz)
  have hfd : PolyhedralPLInCharts d (fun z => (f z : X)) L.space :=
    hidentity.polyhedralPLInCharts_comp L hL f (hfc.mono hLK) hfe hfU
  have hfR : MapsTo (fun z => (f z : X)) K.space (interior R) := by
    intro z hz
    change (f z : X) ∈ interior R
    rw [hfval ⟨z, hz⟩]
    exact hCR (H.symm ⟨z, hz⟩).property
  obtain ⟨q, hqPL, _, hqR, T, hTR, hT0, hT1, hTfix⟩ :=
    OpenPartialHomeomorph.exists_relative_polyhedralPL_approximation
      d hidentity.target_domain.compatible hidentity.target_domain.cover
      K L hK hL hLK (continuous_subtype_val.comp_continuousOn hfc)
      hfd isOpen_interior hfR
  refine ⟨q, T, H ⁻¹' V, hqPL, hqR, hTR, hV.preimage H.continuous,
    ?_, ?_, hT1, ?_⟩
  · intro x hx
    apply hZV
    change (f (H x) : X) ∈ frontier C
    rw [hfval (H x), H.symm_apply_apply]
    exact hx
  · intro z
    exact (hT0 z).trans (hfval z)
  · intro t x hx
    have hHL : (H x : E) ∈ L.space := hVL (mem_image_of_mem Subtype.val hx)
    exact (hTfix t (H x) hHL).trans
      ((hfval (H x)).trans (congrArg Subtype.val (H.symm_apply_apply x)))

end PoincareConjecture.M76
