import PoincareConjecture.Proofs.M76.Rigidity.CollarBaseComparison
import PoincareConjecture.Proofs.M76.Rigidity.MatchedCollarGeometry
import PoincareConjecture.Proofs.M76.Rigidity.MatchedCollarStrips









set_option autoImplicit false

open Set

namespace Geometry

local notation "V3" => (Fin 3 → ℝ)

variable {E F X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}




theorem exists_matched_boundary_product
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hR : IsClosed R)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (HB : L.space ≃ₜ frontier R) (HC : K.space ≃ₜ frontier R)
    (c : E × ℝ → X) (d : F × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (0 : ℝ) 1))
    (hd : PolyhedralPLInCharts e d (K.space ×ˢ Icc (0 : ℝ) 1))
    (hci : Topology.IsEmbedding (fun z : (L.space ×ˢ Icc (0 : ℝ) 1) => c z))
    (hdi : Topology.IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) 1) => d z))
    (hcR : MapsTo c (L.space ×ˢ Icc (0 : ℝ) 1) R)
    (hdT : MapsTo d (K.space ×ˢ Icc (0 : ℝ) 1) (interior R)ᶜ)
    (hc0 : ∀ x : L.space, c ((x : E), 0) = HB x)
    (hd0 : ∀ x : K.space, d ((x : F), 0) = HC x)
    (hcf : ∀ z : (L.space ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)),
      c z ∈ frontier R ↔ (z : E × ℝ).2 = 0)
    (hdf : ∀ z : (K.space ×ˢ Icc (0 : ℝ) 1 : Set (F × ℝ)),
      d z ∈ frontier R ↔ (z : F × ℝ).2 = 0)
    (delta0 delta1 : ℝ) (hdelta0 : 0 < delta0) (hdelta1 : 0 < delta1)
    (hdelta0b : delta0 ≤ 1 / 2) (hdelta1b : delta1 ≤ 1 / 2)
    (hcU : MapsTo c (L.space ×ˢ Icc 0 delta0) U)
    (hdU : MapsTo d (K.space ×ˢ Icc 0 delta1) U)
    (hco : ∀ eps : ℝ, 0 < eps → eps ≤ delta0 →
      IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (L.space ×ˢ Ico 0 eps))))
    (hdo : ∀ eps : ℝ, 0 < eps → eps ≤ delta1 →
      IsOpen ((Subtype.val : ((interior R)ᶜ : Set X) → X) ⁻¹' (d '' (K.space ×ˢ Ico 0 eps)))) :
    ∃ C : E × ℝ → X,
      PolyhedralPLInCharts e C (L.space ×ˢ Icc (-1 : ℝ) 1) ∧
      Topology.IsEmbedding (fun z : (L.space ×ˢ Icc (-1 : ℝ) 1) => C z) ∧
      (∀ x : L.space, C ((x : E), 0) = HB x) ∧
      (∀ z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)),
        (C z ∈ frontier R ↔ (z : E × ℝ).2 = 0) ∧
        (C z ∈ R ↔ 0 ≤ (z : E × ℝ).2) ∧
        (C z ∈ (interior R)ᶜ ↔ (z : E × ℝ).2 ≤ 0)) ∧
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 2 ∧
        MapsTo C (L.space ×ˢ Icc (-delta) delta) U ∧
        ∀ eps : ℝ, 0 < eps → eps ≤ delta →
          IsOpen (C '' (L.space ×ˢ Ioo (-eps) eps)) := by
  obtain ⟨Q, hQ, hQval⟩ := exists_finitePL_collar_base_comparison
    hcompat L hL K hK HB HC c d hc hd hc0 hd0
  have hQmap : MapsTo Q L.space K.space := by
    intro x hx
    rw [hQval ⟨x, hx⟩]
    exact (HC.symm (HB ⟨x, hx⟩)).property
  have hQi : InjOn Q L.space := by
    intro x hx y hy hxy
    have heq : (HC.symm (HB ⟨x, hx⟩) : F) = HC.symm (HB ⟨y, hy⟩) :=
      (hQval ⟨x, hx⟩).symm.trans (hxy.trans (hQval ⟨y, hy⟩))
    exact congrArg Subtype.val (HB.injective (HC.symm.injective (Subtype.ext heq)))
  have hQimage : Q '' L.space = K.space := by
    apply Subset.antisymm (by rintro _ ⟨x, hx, rfl⟩; exact hQmap hx)
    intro y hy
    let x := HB.symm (HC ⟨y, hy⟩)
    refine ⟨x, x.property, ?_⟩
    rw [hQval x]
    change (HC.symm (HB (HB.symm (HC ⟨y, hy⟩))) : F) = y
    rw [HB.apply_symm_apply, HC.symm_apply_apply]
  have hzero : ∀ x ∈ L.space, c (x, 0) = d (Q x, 0) := by
    intro x hx
    rw [hQval ⟨x, hx⟩, hd0, HC.apply_symm_apply]
    exact hc0 ⟨x, hx⟩
  have hcInj : InjOn c (L.space ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz w hw heq
    exact congrArg Subtype.val (hci.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) heq)
  have hdInj : InjOn d (K.space ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz w hw heq
    exact congrArg Subtype.val (hdi.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) heq)
  let C := matchedCollarMap Q c d
  have hPL : PolyhedralPLInCharts e C (L.space ×ˢ Icc (-1 : ℝ) 1) :=
    polyhedral_matchedCollarMap hcover hcompat L hL hc hd hQ hQmap hzero
  have hInj : InjOn C (L.space ×ˢ Icc (-1 : ℝ) 1) :=
    injOn_matchedCollarMap hR hQmap hQi hcInj hdInj hcR hdT
      (fun z hz => hcf ⟨z, hz⟩) (fun z hz => hdf ⟨z, hz⟩)
  let : CompactSpace (L.space ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) :=
    isCompact_iff_compactSpace.mp ((L.isCompact_space_of_finite hL).prod isCompact_Icc)
  have hEmbedding : Topology.IsEmbedding
      (fun z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => C z) :=
    (hPL.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hInj x.property y.property hxy))).isEmbedding
  let delta := min delta0 delta1
  have hdelta : 0 < delta := lt_min hdelta0 hdelta1
  have hdeltab : delta ≤ 1 / 2 := by
    change min delta0 delta1 ≤ 1 / 2
    simpa only [min_self] using min_le_min hdelta0b hdelta1b
  refine ⟨C, hPL, hEmbedding, ?_, ?_, delta, hdelta, hdeltab, ?_, ?_⟩
  · intro x
    exact (matchedCollarMap_nonneg Q c d le_rfl).trans (hc0 x)
  · intro z
    exact matchedCollarMap_side_marks hR hQmap hcR hdT
      (fun z hz => hcf ⟨z, hz⟩) (fun z hz => hdf ⟨z, hz⟩) z z.property
  · exact mapsTo_matchedCollarMap_closed_strip hQmap
      (fun z hz => hcU ⟨hz.1, hz.2.1, hz.2.2.trans (min_le_left _ _)⟩)
      (fun z hz => hdU ⟨hz.1, hz.2.1, hz.2.2.trans (min_le_right _ _)⟩)
  · intro eps heps hepsdelta
    exact isOpen_matchedCollarMap_open_strip hR HB hc0 hQimage hzero hcR hdT
      heps (by linarith) (hco eps heps (hepsdelta.trans (min_le_left _ _)))
      (hdo eps heps (hepsdelta.trans (min_le_right _ _)))

end Geometry
