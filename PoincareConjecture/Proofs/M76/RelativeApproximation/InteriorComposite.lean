import PoincareConjecture.Proofs.M76.RelativeApproximation.ChartwiseRestriction










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {X Y E ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {R C : Set X} {T : Set Y}




theorem chartwisePLOn_interior_model_composite
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (d : κ → OpenPartialHomeomorph Y (Fin 3 → ℝ))
    (he : PLDomain e R) (hd : PLDomain d T)
    (g : C(R, T)) (hCR : C ⊆ R)
    (K : SimplicialComplex ℝ E) (H : C ≃ₜ K.space)
    (F : X → E) (hF : Continuous F)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hHF : ∀ x : C, (H x : E) = F x)
    (q : E → Y) (hq : PolyhedralPLInCharts d q K.space)
    (hg : ∀ x : R, (x : X) ∈ C → (g x : Y) = q (F x)) :
    ChartwisePLOn e d g ((Subtype.val : R → X) ⁻¹' interior C) := by
  classical
  refine ⟨he, hd, isOpen_interior.preimage continuous_subtype_val, ?_⟩
  intro x hx
  obtain ⟨i, hxi⟩ := he.cover x
  have hFx : F x ∈ K.space := by
    rw [← hHF ⟨x, interior_subset hx⟩]
    exact (H ⟨x, interior_subset hx⟩).property
  obtain ⟨j, J, W, _, hJK, hW, hxW, hWJ, hqJ, hqPL⟩ :=
    hq.coordinates ⟨F x, hFx⟩
  obtain ⟨O, hO, hWO⟩ := isOpen_induced_iff.mp hW
  let B : Set (Fin 3 → ℝ) :=
    (e i).target ∩ (e i).symm ⁻¹' (interior C ∩ F ⁻¹' O)
  have hB : IsOpen B :=
    (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target
      (isOpen_interior.inter (hO.preimage hF))
  have hxB : e i x ∈ B := by
    refine ⟨(e i).map_source hxi, ?_⟩
    change (e i).symm (e i x) ∈ interior C ∩ F ⁻¹' O
    rw [(e i).left_inv hxi]
    refine ⟨hx, ?_⟩
    rw [← hWO] at hxW
    exact hxW
  obtain ⟨P, hP, hxP, hPB, hFP⟩ :=
    (hFPL i).mono hB inter_subset_left (e i x) hxB
  have hPK (z : Fin 3 → ℝ) (hz : z ∈ P.space) : F ((e i).symm z) ∈ K.space := by
    rw [← hHF ⟨(e i).symm z, interior_subset (hPB hz).2.1⟩]
    exact (H ⟨(e i).symm z, interior_subset (hPB hz).2.1⟩).property
  have hPJ : MapsTo (F ∘ (e i).symm) P.space J.space := by
    intro z hz
    apply hWJ
    refine ⟨⟨F ((e i).symm z), hPK z hz⟩, ?_, rfl⟩
    rw [← hWO]
    exact (hPB hz).2.2
  have hformula : FinitePiecewiseAffineOn
      (((d j) ∘ q) ∘ (F ∘ (e i).symm)) P.space :=
    hqPL.comp (hFP.finitePiecewiseAffineOn hP) hPJ
  let V : Set R :=
    (Subtype.val : R → X) ⁻¹' ((e i).source ∩ (e i) ⁻¹' interior P.space)
  have hV : IsOpen V :=
    ((e i).continuousOn.isOpen_inter_preimage (e i).open_source
      isOpen_interior).preimage continuous_subtype_val
  have hVP (y : R) (hy : y ∈ V) : e i y ∈ P.space := interior_subset hy.2
  refine ⟨i, j, P, V, ((d j) ∘ q) ∘ (F ∘ (e i).symm), hP, hV,
    ⟨hxi, hxP⟩, ?_, fun y hy => hy.1, ?_,
    fun z hz => (hPB hz).1, ?_, hformula, ?_⟩
  · intro y hy
    have h := (hPB (hVP y hy)).2.1
    rwa [(e i).left_inv hy.1] at h
  · rintro z ⟨y, hy, rfl⟩
    exact hVP y hy
  · intro z hz
    exact ⟨⟨(e i).symm z, hCR (interior_subset (hPB hz).2.1)⟩,
      (hPB hz).2.1, rfl⟩
  · intro y hy hyP
    have hyC : (y : X) ∈ C := by
      have h := interior_subset (hPB hyP).2.1
      rwa [(e i).left_inv hy] at h
    have hqsource := hqJ (hPJ hyP)
    rw [Function.comp_apply, (e i).left_inv hy] at hqsource
    refine ⟨?_, ?_⟩
    · rwa [hg y hyC]
    · change d j (q (F ((e i).symm (e i y)))) = d j (g y)
      rw [(e i).left_inv hy, hg y hyC]

end PoincareConjecture.M76
