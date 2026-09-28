import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.GlobalPulledBackAtlas
import PoincareConjecture.Proofs.M76.PrimeReduction.SphereAmbientTransport



set_option autoImplicit false
open Set Geometry Metric

namespace Geometry

theorem PolyhedralPLInCharts.comp_chart_partialHomeomorph
    {E V X Y ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V} {d : κ → OpenPartialHomeomorph Y V}
    {f : E → X} (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hf : PolyhedralPLInCharts e f K.space) (M : OpenPartialHomeomorph X Y)
    (hmap : MapsTo f K.space M.source) (hcover : ∀ y, ∃ j, y ∈ (d j).source)
    (hM : ∀ i j, (e i).symm.trans (M.trans (d j)) ∈ piecewiseAffineGroupoid V) :
    PolyhedralPLInCharts d (M ∘ f) K.space := by
  have hcont : ContinuousOn (M ∘ f) K.space :=
    M.continuousOn.comp hf.continuousOn hmap
  refine ⟨hcont,?_⟩
  intro x
  obtain ⟨i,J,U,_,_,hU,hxU,hUJ,hfJ,hcoords⟩ := hf.coordinates x
  obtain ⟨j,hxj⟩ := hcover (M (f x))
  let O : Set K.space := U ∩ (fun y => M (f y)) ⁻¹' (d j).source
  have hO : IsOpen O := hU.inter ((d j).open_source.preimage hcont.domRestrict)
  obtain ⟨L,W,hL,hLK,hW,hxW,hWL,hLO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO ⟨hxU,hxj⟩
  have hLV (y : E) (hy : y ∈ L.space) : (⟨y,hLK hy⟩ : K.space) ∈ U :=
    (hLO (show (⟨y,hLK hy⟩ : K.space) ∈ Subtype.val ⁻¹' L.space from hy)).1
  have hLj (y : E) (hy : y ∈ L.space) : M (f y) ∈ (d j).source :=
    (hLO (show (⟨y,hLK hy⟩ : K.space) ∈ Subtype.val ⁻¹' L.space from hy)).2
  have hLJ : L.space ⊆ J.space := by
    intro y hy
    exact hUJ ⟨⟨y,hLK hy⟩,hLV y hy,rfl⟩
  let T := (e i).symm.trans (M.trans (d j))
  have hmaps : MapsTo ((e i) ∘ f) L.space T.source := by
    intro y hy
    have hfi : f y ∈ (e i).source := hfJ (hLJ hy)
    refine ⟨(e i).map_source hfi,?_⟩
    change (e i).symm (e i (f y)) ∈ M.source ∧
      M ((e i).symm (e i (f y))) ∈ (d j).source
    rw [(e i).left_inv hfi]
    exact ⟨hmap (hLK hy),hLj y hy⟩
  refine ⟨j,L,W,hL,hLK,hW,hxW,hWL,fun y hy => hLj y hy,?_⟩
  apply ((hM i j).1.comp_finitePiecewiseAffineOn
    (hcoords.restrict L hL hLJ) hmaps).congr
  intro y hy
  change d j (M ((e i).symm (e i (f y)))) = d j (M (f y))
  rw [(e i).left_inv (hfJ (hLJ hy))]

end Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.nonempty_image_partialHomeomorph
    {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} {d : κ → OpenPartialHomeomorph Y V3}
    {S : Set X} (s : ChartwisePLSphere e S) (M : OpenPartialHomeomorph X Y)
    (hS : S ⊆ M.source) (hcover : ∀ y, ∃ j, y ∈ (d j).source)
    (hM : ∀ i j, (e i).symm.trans (M.trans (d j)) ∈ piecewiseAffineGroupoid V3) :
    Nonempty (ChartwisePLSphere d (M '' S)) := by
  obtain ⟨_,_,_,_,_,_,⟨_,⟨B,hB,hBs,_⟩,_⟩,_⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  let K := B.frontierSubcomplex (closedBall (0 : V3) 1)
  have hK : K.faces.Finite := B.frontierSubcomplex_finite _ hB
  have hKs : K.space = sphere (0 : V3) 1 := by
    rw [B.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hBs,
      frontier_closedBall _ one_ne_zero]
  have hpoly : PolyhedralPLInCharts e s.map K.space := hKs.symm ▸ s.piecewiseAffine
  have hmap : MapsTo s.map K.space M.source := by
    intro x hx
    rw [s.map_eq ⟨x,hKs.subset hx⟩]
    exact hS (s.parametrization ⟨x,hKs.subset hx⟩).property
  refine ⟨{
    parametrization := s.parametrization.trans (M.homeomorphOfImageSubsetSource hS rfl)
    map := M ∘ s.map
    map_eq := ?_
    piecewiseAffine := ?_ }⟩
  · intro x
    change M (s.map x) = M (s.parametrization x)
    rw [s.map_eq]
  · simpa only [hKs] using hpoly.comp_chart_partialHomeomorph K hK M hmap hcover hM

theorem ChartwisePLBall.nonempty_image_partialHomeomorph
    {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} {d : κ → OpenPartialHomeomorph Y V3}
    {D S : Set X} (b : ChartwisePLBall e D S) (M : OpenPartialHomeomorph X Y)
    (hD : D ⊆ M.source) (hcover : ∀ y, ∃ j, y ∈ (d j).source)
    (hM : ∀ i j, (e i).symm.trans (M.trans (d j)) ∈ piecewiseAffineGroupoid V3) :
    Nonempty (ChartwisePLBall d (M '' D) (M '' S)) := by
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  have hpoly : PolyhedralPLInCharts e b.map K.space := hKs.symm ▸ b.piecewiseAffine
  have hmap : MapsTo b.map K.space M.source := by
    intro x hx
    rw [b.map_eq ⟨x,hKs.subset hx⟩]
    exact hD (b.parametrization ⟨x,hKs.subset hx⟩).property
  refine ⟨{
    boundary_subset := image_mono b.boundary_subset
    parametrization := b.parametrization.trans (M.homeomorphOfImageSubsetSource hD rfl)
    map := M ∘ b.map
    map_eq := ?_
    piecewiseAffine := ?_
    boundary_eq := ?_ }⟩
  · intro x
    change M (b.map x) = M (b.parametrization x)
    rw [b.map_eq]
  · simpa only [hKs] using hpoly.comp_chart_partialHomeomorph K hK M hmap hcover hM
  · intro x
    change M (b.parametrization x) ∈ M '' S ↔ _
    rw [←b.boundary_eq x]
    constructor
    · rintro ⟨y,hy,heq⟩
      exact (M.injOn (hD (b.boundary_subset hy)) (hD (b.parametrization x).property) heq) ▸ hy
    · intro hx
      exact mem_image_of_mem M hx

theorem IsPLIrreducible.of_partial_homeomorph
    {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} {d : κ → OpenPartialHomeomorph Y V3}
    {R : Set X} {T : Set Y} (hT : IsPLIrreducible d T) (he : PLDomain e R)
    (M : OpenPartialHomeomorph X Y) (hTM : T ⊆ M.target)
    (hR : R ⊆ M.source) (hregion : M.IsImage R T)
    (hM : ∀ i j, (e i).symm.trans (M.trans (d j)) ∈ piecewiseAffineGroupoid V3) :
    IsPLIrreducible e R := by
  refine ⟨he,?_⟩
  intro S hS hs
  obtain ⟨s⟩ := hs
  have hSM : S ⊆ M.source := hS.trans (interior_subset.trans hR)
  have hs' := s.nonempty_image_partialHomeomorph M hSM hT.1.cover hM
  have hST : M '' S ⊆ interior T := by
    rintro y ⟨x,hx,rfl⟩
    exact (hregion.interior.apply_mem_iff (hSM hx)).mpr (hS hx)
  obtain ⟨D,hDT,⟨b⟩⟩ := hT.2 _ hST hs'
  have hrev (j : κ) (i : ι) : (d j).symm.trans (M.symm.trans (e i)) ∈
      piecewiseAffineGroupoid V3 := by
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).symm (hM i j)
  have hDM : D ⊆ M.symm.source := hDT.trans hTM
  have hball := b.nonempty_image_partialHomeomorph M.symm hDM he.cover hrev
  have hcancel : M.symm '' (M '' S) = S := by
    rw [image_image]
    exact (show EqOn (M.symm ∘ M) id S from fun _ hx => M.left_inv (hSM hx)).image_eq_self
  rw [hcancel] at hball
  refine ⟨M.symm '' D,?_,hball⟩
  rintro x ⟨y,hy,rfl⟩
  apply (hregion.apply_mem_iff (M.map_target (hDM hy))).mp
  rw [M.right_inv (hDM hy)]
  exact hDT hy

theorem IsPLIrreducible.of_partial_homeomorph_image
    {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} {d : κ → OpenPartialHomeomorph Y V3}
    {R : Set X} {T : Set Y} (hT : IsPLIrreducible d T) (he : PLDomain e R)
    (M : OpenPartialHomeomorph X Y)
    (hR : R ⊆ M.source) (himage : M '' R = T)
    (hM : ∀ i j, (e i).symm.trans (M.trans (d j)) ∈ piecewiseAffineGroupoid V3) :
    IsPLIrreducible e R := by
  have hTM : T ⊆ M.target := by
    rw [←himage]
    rintro y ⟨x,hx,rfl⟩
    exact M.map_source (hR hx)
  apply hT.of_partial_homeomorph he M hTM hR _ hM
  intro x hx
  rw [←himage]
  constructor
  · rintro ⟨y,hy,heq⟩
    exact M.injOn (hR hy) hx heq ▸ hy
  · intro hxR
    exact mem_image_of_mem M hxR

end PoincareConjecture.M76
