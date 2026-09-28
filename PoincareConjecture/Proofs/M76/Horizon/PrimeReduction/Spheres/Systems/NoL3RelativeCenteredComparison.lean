import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapAmbientSlide
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapCutComparison
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeMovedSubregions

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem HasNoPuncturedSphereComponents.selected_endpoint_centered_cut_relative
    {X E ι ν μ : Type*} [TopologicalSpace X] [T2Space X] [Finite ν] [Finite μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R U : Set X}
    (hno : HasNoPuncturedSphereComponents e f (R \ interior U))
    (hQ : IsCompact (R \ interior U)) (hPL : PLDomain e (R \ interior U))
    (B : ν → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hfront : frontier (R \ interior U) = frontier R ∪ ⋃ i, B i)
    (hBR : ∀ i, B i ⊆ interior R)
    (hUc : IsConnected U) (hUR : U ⊆ R)
    (c : V3 × ℝ → X)
    (hc : PolyhedralPLInCharts e c (Sphere ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (Sphere ×ˢ Icc (-1 : ℝ) 1))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstripR : MapsTo c (Sphere ×ˢ Icc (-δ) δ) (interior R))
    (hin : MapsTo c (Sphere ×ˢ Icc (-δ) 0) U)
    (hinint : MapsTo c (Sphere ×ˢ Ico (-δ) 0) (interior U))
    (hout : Disjoint (c '' (Sphere ×ˢ Ioc 0 δ)) U)
    (hopen : IsOpen (c '' (Sphere ×ˢ Ioo (-δ/12) (δ/12))))
    (hp : ∃ p ∈ U, p ∉ interior U ∧ p ∉ c '' (Sphere ×ˢ Icc (-δ) δ))
    (hQ' : IsCompact (R \ c '' (Sphere ×ˢ Ioo (-δ/12) (δ/12))))
    (hPL' : PLDomain e (R \ c '' (Sphere ×ˢ Ioo (-δ/12) (δ/12))))
    (B' : μ → Set X) (sB' : ∀ i, ChartwisePLSphere e (B' i))
    (hB'R : ∀ i, B' i ⊆ interior R)
    (hfront' : frontier (R \ c '' (Sphere ×ˢ Ioo (-δ/12) (δ/12))) =
      frontier R ∪ ⋃ i, B' i)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x) :
    HasNoPuncturedSphereComponents e f
      (R \ c '' (Sphere ×ˢ Ioo (-δ/12) (δ/12))) := by
  obtain ⟨F,hfix,_,hslide,_,hforward,_⟩ :=
    exists_original_signed_collar_slide c hc hci hPL.compatible hδ hδ1
  have hi : Topology.IsEmbedding
      (fun z : (Sphere ×ˢ Icc (-1 : ℝ) 1 : Set (V3 × ℝ)) => c z) := by
    let : CompactSpace (Sphere ×ˢ Icc (-1 : ℝ) 1 : Set (V3 × ℝ)) :=
      isCompact_iff_compactSpace.mp ((isCompact_sphere (0 : V3) 1).prod isCompact_Icc)
    exact hc.continuousOn.domRestrict.isClosedEmbedding
      (fun z w h => Subtype.ext (hci z.property w.property h)) |>.isEmbedding
  obtain ⟨hsub,hmeet⟩ := selected_endpoint_cut_meets_moved_exterior
    hUc hUR (isCompact_sphere (0 : V3) 1) c hc.continuousOn hi hδ hδ1
    (fun _ hz => interior_subset (hstripR hz)) hin hinint hout hopen hp F hfix hslide
  have hboundary (M : μ → Set X) (hM : ∀ i, M i ⊆ interior R) :
      Disjoint (frontier R) (⋃ i, M i) := by
    apply disjoint_left.mpr
    intro x hx hm
    obtain ⟨i,hi⟩ := mem_iUnion.mp hm
    exact hx.2 (hM i hi)
  have hboundaryOld : Disjoint (frontier R) (⋃ i, B i) := by
    apply disjoint_left.mpr
    intro x hx hm
    obtain ⟨i,hi⟩ := mem_iUnion.mp hm
    exact hx.2 (hBR i hi)
  have hsupport : c '' (Sphere ×ˢ Icc (-δ/2) (δ/2)) ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    exact hstripR ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  apply hno.of_moved_relative_component_subregions hQ hPL hQ' hPL' isClosed_frontier
    B sB hBdis hboundaryOld hfront B' sB' (hboundary B' hB'R) hfront'
    F hforward hfix (hsupport.trans interior_subset) ?_ sdiff_subset sdiff_subset
    hsub hmeet L g hf hg hgi hreal
  intro x hx
  exact hfix (fun h => hx.2 (hsupport h))

end PoincareConjecture.M76
