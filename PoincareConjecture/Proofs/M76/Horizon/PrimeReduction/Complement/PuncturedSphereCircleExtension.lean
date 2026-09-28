import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.MarkedPuncturedDoubleSphere
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PeriodCircleLoop
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.SphereConnectivity
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.SphereDiskExtension
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.LocallyFinite
import Mathlib.Geometry.Manifold.Instances.Sphere











set_option autoImplicit false

open Set Metric Geometry

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "Circle" => AddCircle (1 : ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem IsFinitePLBallPair.rim_lifting_topology {D B : Set E}
    (hD : IsFinitePLBallPair V3 D B) :
    IsCompact B ∧ SimplyConnectedSpace B ∧ LocallyPathConnectedSpace B := by
  obtain ⟨e, _, heb⟩ := hD.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  let b := e.restrictSubsets hD.1 isClosed_closedBall.frontier_subset heb
  let c : V3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := b.trans ((Homeomorph.setCongr (frontier_closedBall (0 : V3) one_ne_zero)).trans
    (Poincare.Topology.unitSphereHomeomorph c))
  let : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Poincare.Topology.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  let : LocallyPathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (H := EuclideanSpace ℝ (Fin 2))
      (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  let : CompactSpace B := H.symm.compactSpace
  exact ⟨isCompact_iff_compactSpace.mpr inferInstance,
    H.toHomotopyEquiv.simplyConnectedSpace, H.isOpenEmbedding.locallyPathConnectedSpace⟩



theorem IsFinitePLBallPair.exists_circle_extension {D B : Set E}
    (hD : IsFinitePLBallPair V3 D B) (f : C(B, Circle)) :
    ∃ g : C(D, Circle), ∀ x : B, g ⟨x, hD.1 x.property⟩ = f x := by
  obtain ⟨hB, hsc, hlpc⟩ := hD.rim_lifting_topology
  let : SimplyConnectedSpace B := hsc
  let : LocallyPathConnectedSpace B := hlpc
  let x : B := Classical.choice inferInstance
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (f x)
  obtain ⟨F, ⟨_, hF⟩, _⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts f x r hr
  obtain ⟨G, hG⟩ := F.exists_extension hB.isClosed.isClosedEmbedding_subtypeVal
  refine ⟨⟨fun y => ((G y : ℝ) : Circle),
    (AddCircle.continuous_mk' (1 : ℝ)).comp (G.continuous.comp continuous_subtype_val)⟩,
    fun y => ?_⟩
  change ((G y : ℝ) : Circle) = f y
  have hy : G y = F y := DFunLike.congr_fun hG y
  rw [hy]
  exact congrFun hF y



theorem exists_circle_extension_finite_caps {ι : Type*} [Finite ι]
    {P : Set E} (hP : IsClosed P) (D B : ι → Set E)
    (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hattach : ∀ i, P ∩ D i = B i) (f : C(P, Circle)) :
    ∃ g : C((P ∪ ⋃ i, D i : Set E), Circle),
      ∀ x : P, g ⟨x, Or.inl x.property⟩ = f x := by
  classical
  have hBP (i : ι) : B i ⊆ P := fun x hx => ((hattach i).symm ▸ hx).1
  let fi (i : ι) : C(B i, Circle) :=
    f.comp ⟨Set.inclusion (hBP i), continuous_inclusion (hBP i)⟩
  choose g hg using fun i => (hD i).exists_circle_extension (fi i)
  let F : E → Circle := fun x => if hxP : x ∈ P then f ⟨x, hxP⟩ else
    if hx : ∃ i, x ∈ D i then g hx.choose ⟨x, hx.choose_spec⟩ else 0
  have hFP (x : P) : F x = f x := by simp [F, x.property]
  have hFD (i : ι) (x : D i) : F x = g i x := by
    by_cases hxP : (x : E) ∈ P
    · have hxB : (x : E) ∈ B i := hattach i ▸ And.intro hxP x.property
      rw [show F x = f ⟨x, hxP⟩ by simp [F, hxP]]
      exact (hg i ⟨x, hxB⟩).symm
    · have hx : ∃ j, (x : E) ∈ D j := ⟨i, x.property⟩
      have hji : hx.choose = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hdis hne) hx.choose_spec x.property
      simp only [F, dif_neg hxP, dif_pos hx]
      have heq : ∀ (j : ι) (hj : (x : E) ∈ D j), j = i → g j ⟨x, hj⟩ = g i x := by
        intro j hj h
        subst j
        rfl
      exact heq _ _ hji
  have hFPc : ContinuousOn F P := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact f.continuous.congr (fun x => (hFP x).symm)
  have hFDc (i : ι) : ContinuousOn F (D i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (g i).continuous.congr (fun x => (hFD i x).symm)
  have hFU : ContinuousOn F (⋃ i, D i) :=
    (locallyFinite_of_finite D).continuousOn_iUnion
      (fun i => (hD i).isCompact.isClosed) hFDc
  refine ⟨⟨fun x => F x, (hFPc.union_of_isClosed hFU hP
    (isClosed_iUnion_of_finite fun i => (hD i).isCompact.isClosed)).domRestrict⟩, hFP⟩




theorem exists_circle_extension_closed_punctured_carrier {ι : Type*} [Finite ι]
    {S : Set E} (D B : ι → Set E)
    (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ S)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hclosed : IsClosed (S \ ⋃ i, D i \ B i))
    (f : C((S \ ⋃ i, D i \ B i : Set E), Circle)) :
    ∃ g : C(S, Circle),
      ∀ x : (S \ ⋃ i, D i \ B i : Set E), g ⟨x, x.property.1⟩ = f x := by
  classical
  let P := S \ ⋃ i, D i \ B i
  have hatt (i : ι) : P ∩ D i = B i := by
    ext x
    constructor
    · rintro ⟨hxP, hxi⟩
      by_contra hxB
      exact hxP.2 (mem_iUnion.mpr ⟨i, hxi, hxB⟩)
    · intro hxB
      have hxi := (hD i).1 hxB
      refine ⟨⟨hDS i hxi, ?_⟩, hxi⟩
      intro hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · subst j
        exact hxj.2 hxB
      · exact Set.disjoint_left.mp (hdis hji) hxj.1 hxi
  have hwhole : P ∪ ⋃ i, D i = S := by
    apply Subset.antisymm
    · exact union_subset sdiff_subset (iUnion_subset hDS)
    · intro x hx
      by_cases h : x ∈ ⋃ i, D i
      · exact Or.inr h
      · refine Or.inl ⟨hx, ?_⟩
        intro hi
        obtain ⟨i, hxi, _⟩ := mem_iUnion.mp hi
        exact h (mem_iUnion.mpr ⟨i, hxi⟩)
  obtain ⟨g, hg⟩ := exists_circle_extension_finite_caps hclosed D B hD hdis hatt f
  let e := Homeomorph.setCongr hwhole
  refine ⟨g.comp ⟨e.symm, e.symm.continuous⟩, fun x => ?_⟩
  exact hg x

end Set

namespace Geometry.CubicalThreeSphere

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Circle" => AddCircle (1 : ℝ)


theorem simplyConnectedSpace_sphere : SimplyConnectedSpace sphere := by
  let c : V4 ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := (Homeomorph.setCongr (frontier_closedBall (0 : V4) one_ne_zero)).trans
    (Poincare.Topology.unitSphereHomeomorph c)
  let : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    Poincare.Topology.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  exact H.toHomotopyEquiv.simplyConnectedSpace




theorem exists_circle_extension_punctured_sphere_of_isOpen {ι : Type*} [Finite ι]
    (D B : ι → Set V4) (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ sphere)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hopen : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (D i \ B i)))
    (f : C((sphere \ ⋃ i, D i \ B i : Set V4), Circle)) :
    ∃ g : C(sphere, Circle),
      ∀ x : (sphere \ ⋃ i, D i \ B i : Set V4), g ⟨x, x.property.1⟩ = f x := by
  have hU : IsOpen ((Subtype.val : sphere → V4) ⁻¹' (⋃ i, D i \ B i)) := by
    rw [preimage_iUnion]
    exact isOpen_iUnion hopen
  have himage : (Subtype.val : sphere → V4) ''
      (((Subtype.val : sphere → V4) ⁻¹' (⋃ i, D i \ B i))ᶜ) =
        sphere \ ⋃ i, D i \ B i := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hclosed : IsClosed (sphere \ ⋃ i, D i \ B i) := by
    rw [← himage]
    exact isClosed_frontier.isClosedMap_subtype_val _ hU.isClosed_compl
  exact Set.exists_circle_extension_closed_punctured_carrier D B hD hDS hdis hclosed f




theorem circle_map_loop_nullhomotopic_of_isOpen {ι : Type*} [Finite ι]
    (D B : ι → Set V4) (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ sphere)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hopen : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (D i \ B i)))
    (f : C((sphere \ ⋃ i, D i \ B i : Set V4), Circle))
    (x : (sphere \ ⋃ i, D i \ B i : Set V4)) (gamma : Path x x) :
    (gamma.map f.continuous).Homotopic (Path.refl (f x)) := by
  obtain ⟨g, hg⟩ := exists_circle_extension_punctured_sphere_of_isOpen D B hD hDS hdis hopen f
  let inc : C((sphere \ ⋃ i, D i \ B i : Set V4), sphere) :=
    ⟨fun z => ⟨z, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  let : SimplyConnectedSpace sphere := simplyConnectedSpace_sphere
  have h := (SimplyConnectedSpace.paths_homotopic (gamma.map inc.continuous)
    (Path.refl (inc x))).map g
  have hgf : g.comp inc = f := by
    ext z
    exact hg z
  rw [Path.map_map] at h
  change (gamma.map (g.comp inc).continuous).Homotopic (Path.refl ((g.comp inc) x)) at h
  rwa [hgf] at h




theorem exists_circle_extension_punctured_sphere {ι : Type*} [Finite ι]
    (D B : ι → Set V4) (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDU : ∀ i, D i ⊆ upper \ seam)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (f : C((sphere \ ⋃ i, D i \ B i : Set V4), Circle)) :
    ∃ g : C(sphere, Circle),
      ∀ x : (sphere \ ⋃ i, D i \ B i : Set V4), g ⟨x, x.property.1⟩ = f x := by
  have hclosed : IsClosed (sphere \ ⋃ i, D i \ B i) := by
    rw [← lower_union_upper]
    exact lower_ball.isClosed_punctured_double upper_ball lower_inter_upper D B hD hDU
  exact Set.exists_circle_extension_closed_punctured_carrier D B hD
    (fun i x hx => (hDU i hx).1.1) hdis hclosed f




theorem circle_map_loop_nullhomotopic {ι : Type*} [Finite ι]
    (D B : ι → Set V4) (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDU : ∀ i, D i ⊆ upper \ seam)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (f : C((sphere \ ⋃ i, D i \ B i : Set V4), Circle))
    (x : (sphere \ ⋃ i, D i \ B i : Set V4)) (gamma : Path x x) :
    (gamma.map f.continuous).Homotopic (Path.refl (f x)) := by
  obtain ⟨g, hg⟩ := exists_circle_extension_punctured_sphere D B hD hDU hdis f
  let inc : C((sphere \ ⋃ i, D i \ B i : Set V4), sphere) :=
    ⟨fun z => ⟨z, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  let : SimplyConnectedSpace sphere := simplyConnectedSpace_sphere
  have h := (SimplyConnectedSpace.paths_homotopic (gamma.map inc.continuous)
    (Path.refl (inc x))).map g
  have hgf : g.comp inc = f := by
    ext z
    exact hg z
  rw [Path.map_map] at h
  change (gamma.map (g.comp inc).continuous).Homotopic (Path.refl ((g.comp inc) x)) at h
  rwa [hgf] at h

end Geometry.CubicalThreeSphere
