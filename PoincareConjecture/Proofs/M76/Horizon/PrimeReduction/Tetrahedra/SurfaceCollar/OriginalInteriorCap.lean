import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalBoundaryInwardMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLChartHomeomorph










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_strictly_interior_cap
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s j, (e j).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedge : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {d r : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d r)
    (hdT : d ⊆ convexHull ℝ (t : Set E))
    (hdfront : d ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = r)
    (hdS : d ∩ g ⁻¹' (⋃ i, S i) = r)
    {O : Set X} (hO : IsOpen O) (hrO : g '' r ⊆ O) :
    ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id Oᶜ ∧ (∀ j x, H x ∈ S j ↔ x ∈ S j) ∧
      PolyhedralPLInCharts e (H ∘ g) d ∧ InjOn (H ∘ g) d ∧
      (H ∘ g) '' d ⊆ interior (g '' convexHull ℝ (t : Set E)) ∧
      ((H ∘ g) '' d) ∩ (⋃ i, S i) = (H ∘ g) '' r ∧
      IsCompact ((H ∘ g) '' d) ∧
      Disjoint ((H ∘ g) '' r) (g '' r) ∧
      (∀ x ∈ g '' convexHull ℝ (t : Set E),
        H x ∈ interior (g '' convexHull ℝ (t : Set E)) ∨ H x = x) := by
  obtain ⟨J,L,hJ,hJs,hL,hLs⟩ := hd.exists_finite_carrier_and_rim_complexes
  have hdK : d ⊆ K.space := hdT.trans (K.convexHull_subset_space ht)
  have hrK : r ⊆ K.space := hd.1.trans hdK
  have hrcompact : IsCompact (g '' r) :=
    (hLs ▸ L.isCompact_space_of_finite hL).image_of_continuousOn (hg.continuousOn.mono hrK)
  have hrS : g '' r ⊆ ⋃ i, S i := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hdS.symm.subset hx).2
  have hrfront : g '' r ⊆ g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) :=
    image_mono (fun _ hx => (hdfront.symm.subset hx).2)
  obtain ⟨H,hHPL,hHiPL,hHfix,hHS,hHin,hHr⟩ := exists_original_boundary_inward_motion
    he hcover K hK g hg hgi Q hQ A hmap hA S sS hdis hSV hedge hposition ht ht4
    hrcompact hrS hrfront hO hrO
  have hgJ : PolyhedralPLInCharts e g J.space := hg.restrict_finite J hJ (hJs.subset.trans hdK)
  have hHg : PolyhedralPLInCharts e (H ∘ g) d := hJs ▸ hgJ.comp_chart_homeomorph J hJ H hcover hHPL
  obtain ⟨ball⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
  have hinside : (H ∘ g) '' d ⊆ interior (g '' convexHull ℝ (t : Set E)) := by
    rintro _ ⟨x,hx,rfl⟩
    by_cases hxr : x ∈ r
    · exact hHr (mem_image_of_mem H (mem_image_of_mem g hxr))
    · have hxint : g x ∈ interior (g '' convexHull ℝ (t : Set E)) := by
        apply (mem_interior_iff_notMem_frontier (mem_image_of_mem g (hdT hx))).mpr
        rw [ball.frontier_eq]
        rintro ⟨y,hy,hyx⟩
        have hyK := K.convexHull_subset_space ht
          (intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed hy)
        have hyx' : y = x := hgi hyK (hdK hx) hyx
        exact hxr (hdfront.subset ⟨hx,hyx' ▸ hy⟩)
      rcases hHin (g x) (mem_image_of_mem g (hdT hx)) with hi | hf
      · exact hi
      · simpa only [Function.comp_apply,hf] using hxint
  refine ⟨H,hHPL,hHiPL,hHfix,hHS,hHg,H.injective.injOn.comp (hgi.mono hdK)
    (mapsTo_univ _ _),hinside,?_,hd.isCompact.image_of_continuousOn hHg.continuousOn,?_,hHin⟩
  · ext y
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hys⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp hys
      exact ⟨x,hdS.subset ⟨hx,mem_iUnion.mpr ⟨i,(hHS i (g x)).mp hi⟩⟩,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp ((hdS.symm.subset hx).2)
      exact ⟨⟨x,hd.1 hx,rfl⟩,mem_iUnion.mpr ⟨i,(hHS i (g x)).mpr hi⟩⟩
  · apply disjoint_left.mpr
    intro y hynew hyold
    have hyint := hinside (image_mono hd.1 hynew)
    have hyfront : y ∈ frontier (g '' convexHull ℝ (t : Set E)) :=
      ball.frontier_eq.symm ▸ hrfront hyold
    exact hyfront.2 hyint

end PoincareConjecture.M76
