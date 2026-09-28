import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PlanarSurfaceCarrierInterior









set_option autoImplicit false
open Set Filter Geometry Topology
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem not_mem_interior_planar_carrier_of_halfspace_chart
    {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S E : Set X}
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space)
    (hpi : InjOn p K.space) (hps : p '' K.space ⊆ S ∩ E)
    (T : OpenPartialHomeomorph X V3)
    (hT : ∀ i,(e i).symm.trans T ∈ piecewiseAffineGroupoid V3)
    (hS : ∀ y ∈ T.source,y ∈ S ↔ T y 1 = 0)
    (hE : (∀ y ∈ T.source,y ∈ E ↔ 0 ≤ T y 0) ∨
      (∀ y ∈ T.source,y ∈ E ↔ T y 0 ≤ 0))
    {x : P2} (hx : x ∈ K.space) (hxT : p x ∈ T.source) (hTx : T (p x) = 0) :
    x ∉ interior K.space := by
  intro hxint
  obtain ⟨N,W,hN,hNK,hW,hxW,hWN,hNT,hcoords⟩ :=
    hp.exists_finite_compatible_chart_patch K hK T hT ⟨x,hx⟩ hxT
  have hxN : x ∈ N.space := hWN ⟨⟨x,hx⟩,hxW,rfl⟩
  obtain ⟨U,hU,hUW⟩ :=
    (mem_nhds_subtype K.space ⟨x,hx⟩ W).mp (hW.mem_nhds hxW)
  have hxNint : x ∈ interior N.space := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Filter.inter_mem (mem_interior_iff_mem_nhds.mp hxint) hU)
    rintro z ⟨hzK,hzU⟩
    exact hWN ⟨⟨z,hzK⟩,hUW hzU,rfl⟩
  let pr : V3 →ᴬ[ℝ] P2 :=
    ((ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.proj 2)).toContinuousAffineMap
  let f : P2 → P2 := pr ∘ T ∘ p
  have hf : FinitePiecewiseAffineOn f N.space := hcoords.postcomp pr
  have hzero (z : P2) (hz : z ∈ N.space) : T (p z) 1 = 0 :=
    (hS _ (hNT hz)).mp (hps (mem_image_of_mem p (hNK hz))).1
  have hfi : InjOn f N.space := by
    intro z hz w hw hzw
    apply hpi (hNK hz) (hNK hw)
    apply T.injOn (hNT hz) (hNT hw)
    have h0 : T (p z) 0 = T (p w) 0 := congrArg Prod.fst hzw
    have h2 : T (p z) 2 = T (p w) 2 := congrArg Prod.snd hzw
    funext i
    fin_cases i
    · exact h0
    · exact (hzero z hz).trans (hzero w hw).symm
    · exact h2
  have hf0 : f x = 0 := by
    change pr (T (p x)) = 0
    rw [hTx]
    rfl
  have hi : f x ∈ interior (f '' N.space) :=
    hf.mem_interior_image rfl hfi hxNint
  rw [hf0] at hi
  rcases hE with hE | hE
  · have hs : f '' N.space ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := by
      rintro _ ⟨z,hz,rfl⟩
      exact ⟨(hE _ (hNT hz)).mp (hps (mem_image_of_mem p (hNK hz))).2,mem_univ _⟩
    have hh := interior_mono hs hi
    rw [interior_prod_eq,interior_Ici,interior_univ] at hh
    exact (lt_irrefl (0 : ℝ)) hh.1
  · have hs : f '' N.space ⊆ Iic (0 : ℝ) ×ˢ (univ : Set ℝ) := by
      rintro _ ⟨z,hz,rfl⟩
      exact ⟨(hE _ (hNT hz)).mp (hps (mem_image_of_mem p (hNK hz))).2,mem_univ _⟩
    have hh := interior_mono hs hi
    rw [interior_prod_eq,interior_Iic,interior_univ] at hh
    exact (lt_irrefl (0 : ℝ)) hh.1

theorem planar_exterior_rim_subset_frontier
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S E : Set X}
    (he : PLDomain e E)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    {B : Set P2} (hBK : B ⊆ K.space)
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ E)
    (hproper : ∀ z ∈ K.space,p z ∈ frontier E ↔ z ∈ B)
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0) :
    B ⊆ frontier K.space := by
  intro x hx
  have hxK := hBK hx
  have hxp := hps.subset (mem_image_of_mem p hxK)
  have hxf := (hproper x hxK).mpr hx
  obtain ⟨H,hxH,hH0,hHe,hHS,hHE⟩ := hcross (p x) ⟨hxp.1,hxf⟩
  obtain ⟨T,hxT,hT0,hTe,hTS,_,hTE⟩ :=
    exists_signed_frontier_crossing_chart he hxf H hxH hH0 hHe hHS hHE
  rw [(K.isCompact_space_of_finite hK).isClosed.frontier_eq]
  exact ⟨hxK,not_mem_interior_planar_carrier_of_halfspace_chart
    K hK p hp hpi hps.subset T hTe hTS hTE hxK hxT hT0⟩

theorem ChartwisePLSphere.planar_exterior_frontier_eq
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S E : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e E)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    {B : Set P2} (hBK : B ⊆ K.space)
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ E)
    (hproper : ∀ z ∈ K.space,p z ∈ frontier E ↔ z ∈ B)
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0) :
    frontier K.space = B := by
  apply Subset.antisymm
  · intro x hx
    have hxK := (K.isCompact_space_of_finite hK).isClosed.frontier_subset hx
    by_contra hxB
    exact hx.2 (s.planar_exterior_interior_of_not_rim he K hK p hp hpi hps hproper ⟨hxK,hxB⟩)
  · exact planar_exterior_rim_subset_frontier he K hK hBK p hp hpi hps hproper hcross

end PoincareConjecture.M76
