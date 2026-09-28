import PoincareConjecture.Proofs.M76.Rigidity.InwardCollarCoordinates










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q3" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}




theorem exists_homeomorph_collar_level
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    {t : ℝ} (ht : t ∈ I) :
    ∃ H : L.space ≃ₜ (c '' (L.space ×ˢ {t}) : Set X),
      ∀ z : L.space, (H z : X) = c ((z : E), t) := by
  let d : E → X := fun z => c (z, t)
  have hd : PolyhedralPLInCharts e d L.space :=
    PolyhedralPLInCharts.finite_product_slice L hL hc ht
  have hdInj : InjOn d L.space := by
    intro x hx y hy hxy
    have hpairs : (⟨(x, t), ⟨hx, ht⟩⟩ : (L.space ×ˢ I : Set (E × ℝ))) =
        ⟨(y, t), ⟨hy, ht⟩⟩ := hi.injective hxy
    exact congrArg (fun z : (L.space ×ˢ I : Set (E × ℝ)) => z.1.1) hpairs
  let : CompactSpace L.space := isCompact_iff_compactSpace.mp
    (L.isCompact_space_of_finite hL)
  have hdCont : Continuous (fun z : L.space => d z) :=
    continuousOn_iff_continuous_domRestrict.mp hd.continuousOn
  let H : L.space ≃ₜ d '' L.space := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn d L.space hdInj) (hdCont.subtype_mk _)
  have himage : d '' L.space = c '' (L.space ×ˢ {t}) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z, t), ⟨hz, rfl⟩, rfl⟩
    · rintro ⟨⟨z, v⟩, ⟨hz, hv⟩, rfl⟩
      have hv' : v = t := mem_singleton_iff.mp hv
      subst v
      exact ⟨z, hz, rfl⟩
  exact ⟨H.trans (Homeomorph.setCongr himage), fun _ => rfl⟩




theorem ChartwisePLSphere.nonempty_collar_level
    (s : ChartwisePLSphere e (frontier R))
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ frontier R) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hbase : ∀ x : L.space, c ((x : E), 0) = HB x)
    (hinside : MapsTo c (L.space ×ˢ I) R)
    (hproper : ∀ z : (L.space ×ˢ I : Set (E × ℝ)),
      c z ∈ frontier R ↔ (z : E × ℝ).2 = 0)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Nonempty (ChartwisePLSphere e (c '' (L.space ×ˢ {t}))) ∧
      c '' (L.space ×ˢ {t}) ⊆ interior R := by
  have htI : t ∈ I := ⟨ht.le, ht1⟩
  obtain ⟨q, hq, hqval⟩ := s.exists_finitePL_collar_base_parameter
    hcompat L hL HB c hc hi hbase
  obtain ⟨H, hHval⟩ := exists_homeomorph_collar_level L hL c hc hi htI
  obtain ⟨K, hK, hKQ⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hqmap : MapsTo q K.space L.space := by
    intro x hx
    rw [hqval ⟨x, hKQ.subset hx⟩]
    exact (HB.symm (s.parametrization ⟨x, hKQ.subset hx⟩)).property
  have hlevelPL : PolyhedralPLInCharts e ((fun z => c (z, t)) ∘ q) Q3 := by
    have hslice := PolyhedralPLInCharts.finite_product_slice L hL hc htI
    have h := hslice.comp_finitePiecewiseAffineOn K hK (hKQ.symm ▸ hq) hqmap
    exact hKQ ▸ h
  refine ⟨⟨{
    parametrization := (s.parametrization.trans HB.symm).trans H
    map := (fun z => c (z, t)) ∘ q
    map_eq := ?_
    piecewiseAffine := hlevelPL
  }⟩, ?_⟩
  · intro x
    change c (q x, t) = (H (HB.symm (s.parametrization x)) : X)
    rw [hqval x, hHval]
  · rintro x ⟨z, hz, rfl⟩
    have hzt : z.2 = t := mem_singleton_iff.mp hz.2
    have hzI : z ∈ L.space ×ˢ I := by
      refine ⟨hz.1, ?_⟩
      rw [hzt]
      exact htI
    apply (mem_interior_iff_notMem_frontier (hinside hzI)).mpr
    intro hfront
    have hzero := (hproper ⟨z, hzI⟩).mp hfront
    exact ht.ne' (hzt.symm.trans hzero)

end PoincareConjecture.M76
