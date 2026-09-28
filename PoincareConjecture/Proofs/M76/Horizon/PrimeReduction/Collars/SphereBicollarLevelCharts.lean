import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSpherePairCharts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1

variable {X E ι : Type*} [TopologicalSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {e : ι → OpenPartialHomeomorph X V3} {S : Set X}

theorem ChartwisePLSphere.exists_bicollar_level_sphere
    (s : ChartwisePLSphere e S) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) {N : Set E} (hN : N = F '' S)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (N ×ˢ J))
    (hci : Topology.IsEmbedding (fun z : (N ×ˢ J : Set (E × ℝ)) => c z))
    {t : ℝ} (ht : t ∈ J) :
    ∃ q : ChartwisePLSphere e (c '' (N ×ˢ ({t} : Set ℝ))),
      ∀ x : V3, q.map x = c (F (s.map x), t) := by
  classical
  have hsimage : s.map '' sphere (0 : V3) 1 = S := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hx⟩]
      exact (s.parametrization ⟨x, hx⟩).property
    · intro y hy
      obtain ⟨x, hx⟩ := s.parametrization.surjective ⟨y, hy⟩
      refine ⟨x, x.property, ?_⟩
      rw [s.map_eq x, hx]
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  let A := K.frontierSubcomplex (closedBall (0 : V3) 1)
  have hA : A.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hAs : A.space = sphere (0 : V3) 1 := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKs,
      frontier_closedBall _ one_ne_zero]
  have hsA : PolyhedralPLInCharts e s.map A.space := hAs.symm ▸ s.piecewiseAffine
  have hFs : FinitePiecewiseAffineOn (F ∘ s.map) A.space :=
    hsA.finitePiecewiseAffineOn_comp A hA hF
  let insertTime : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E t)
  have hFsN (x : V3) (hx : x ∈ A.space) : F (s.map x) ∈ N :=
    hN.symm.subset (mem_image_of_mem F (hsimage.subset (mem_image_of_mem s.map (hAs.subset hx))))
  have hmap : MapsTo (insertTime ∘ (F ∘ s.map)) A.space (N ×ˢ J) :=
    fun x hx => ⟨hFsN x hx, ht⟩
  let k : V3 → X := fun x => c (F (s.map x), t)
  have hk : PolyhedralPLInCharts e k (sphere (0 : V3) 1) := by
    have h := hc.comp_finitePiecewiseAffineOn A hA (hFs.postcomp insertTime) hmap
    exact hAs ▸ h
  have hki : InjOn k (sphere (0 : V3) 1) := by
    intro x hx y hy hxy
    have hxN := hFsN x (hAs.symm.subset hx)
    have hyN := hFsN y (hAs.symm.subset hy)
    have hpair := congrArg Subtype.val (hci.injective
      (a₁ := ⟨(F (s.map x), t), hxN, ht⟩)
      (a₂ := ⟨(F (s.map y), t), hyN, ht⟩) hxy)
    have hsxy := hFi (hsimage.subset (mem_image_of_mem s.map hx))
      (hsimage.subset (mem_image_of_mem s.map hy)) (congrArg Prod.fst hpair)
    have he : s.parametrization ⟨x, hx⟩ = s.parametrization ⟨y, hy⟩ :=
      Subtype.ext (by rw [← s.map_eq ⟨x, hx⟩, ← s.map_eq ⟨y, hy⟩]; exact hsxy)
    exact congrArg Subtype.val (s.parametrization.injective he)
  have hkimage : k '' sphere (0 : V3) 1 = c '' (N ×ˢ ({t} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(F (s.map x), t), ⟨hFsN x (hAs.symm.subset hx), rfl⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hxS, hxF⟩ := hN.subset hz.1
      obtain ⟨w, hw, hws⟩ := hsimage.symm.subset hxS
      refine ⟨w, hw, ?_⟩
      change c (F (s.map w), t) = c z
      rw [hws, hxF, ← show z.2 = t from hz.2]
  let f : sphere (0 : V3) 1 → X := fun x => k x
  have hfc : Continuous f := hk.continuousOn.domRestrict
  have hfi : Function.Injective f := fun x y h => Subtype.ext (hki x.property y.property h)
  let : CompactSpace (sphere (0 : V3) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let d := hfc.isClosedEmbedding hfi |>.isEmbedding.toHomeomorph
  have hrange : range f = c '' (N ×ˢ ({t} : Set ℝ)) :=
    (image_eq_range k (sphere (0 : V3) 1)).symm.trans hkimage
  exact ⟨{
    parametrization := d.trans (Homeomorph.setCongr hrange)
    map := k
    map_eq := fun _ => rfl
    piecewiseAffine := hk }, fun _ => rfl⟩

theorem ChartwisePLSphere.exists_bicollar_level_pair_chart
    (s : ChartwisePLSphere e S) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) {N : Set E} (hN : N = F '' S)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (N ×ˢ J))
    (hci : Topology.IsEmbedding (fun z : (N ×ˢ J : Set (E × ℝ)) => c z))
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    {t : ℝ} (ht : t ∈ J) {x : X} (hx : x ∈ c '' (N ×ˢ ({t} : Set ℝ))) :
    ∃ B : OpenPartialHomeomorph X V3, x ∈ B.source ∧ B x = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ y ∈ B.source, y ∈ c '' (N ×ˢ ({t} : Set ℝ)) ↔ (B y) 0 = 0 := by
  obtain ⟨q, _⟩ := s.exists_bicollar_level_sphere F hF hFi hN c hc hci ht
  exact q.exists_pair_chart hcompat (fun y _ => hcover y) hx

end PoincareConjecture.M76
