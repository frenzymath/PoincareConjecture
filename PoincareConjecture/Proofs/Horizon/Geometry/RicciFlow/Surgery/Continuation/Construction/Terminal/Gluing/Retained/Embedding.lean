import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Inclusions
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Topology Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

def retainedPieceOpen : Option ι → Opens S.carrier
  | none => U
  | some i => (I i).retainedCollar

def retainedPieceMap : ∀ j, retainedPieceOpen I U j → (cutCarrier I R U hU hd hc).carrier
  | none => retainedInclusion I R U hU hd hc
  | some i => capInclusion I R U hU hd hc i ∘
      (R i).retainedMap (I i).retainedCollar subset_rfl

theorem retainedPieceMap_localDiffeomorph (j : Option ι) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (retainedPieceMap I R U hU hd hc j) := by
  cases j with
  | none => exact retainedInclusion_localDiffeomorph I R U hU hd hc
  | some i =>
    intro x
    exact ((R i).retainedMap_isLocalDiffeomorph (I i).retainedCollar subset_rfl x).comp
      (𝓡 3) (cutCarrier I R U hU hd hc).carrier
      (capInclusion_localDiffeomorph I R U hU hd hc i _)

theorem retainedPieceMap_openEmbedding (j : Option ι) :
    IsOpenEmbedding (retainedPieceMap I R U hU hd hc j) := by
  cases j with
  | none => exact retainedInclusion_openEmbedding I R U hU hd hc
  | some i =>
    exact (capInclusion_openEmbedding I R U hU hd hc i).comp
      ((R i).retainedMap_openEmbedding (I i).retainedCollar subset_rfl)

variable (hneck : Pairwise (fun i j => Disjoint (I i).neck.carrier (I j).neck.carrier))
  (hUn : ∀ i, (U : Set S.carrier) ∩ (I i).neck.carrier = (I i).negativeHalf)

include hUn in
theorem retainedPieceMap_retained_eq_iff (i : ι) (x : U) (y : (I i).retainedCollar) :
    retainedInclusion I R U hU hd hc x =
      capInclusion I R U hU hd hc i ((R i).collapse y.val) ↔ x.val = y.val := by
  constructor
  · intro hxy
    have hx := (retainedInclusion_mem_cap_iff I R U hU hd hc i x).mp
      ⟨(R i).collapse y.val, hxy.symm⟩
    have he := (capInclusion_openEmbedding I R U hU hd hc i).injective
      ((retainedInclusion_eq_cap I R U hU hd hc i x hx).symm.trans hxy)
    have := congrArg (R i).retained_inverse he
    simpa only [(R i).retained_left_inverse ((I i).negativeHalf_subset_retainedCollar hx),
      (R i).retained_left_inverse y.property] using this
  · intro hxy
    have hx : x.val ∈ (I i).negativeHalf := by
      change x.val ∈ ((I i).negativeHalf : Set S.carrier)
      rw [← hUn i]
      exact ⟨x.property, hxy ▸ y.property.1⟩
    rw [← hxy]
    exact retainedInclusion_eq_cap I R U hU hd hc i x hx

include hneck hUn in
theorem retainedPieceMap_eq_iff (i j : Option ι)
    (x : retainedPieceOpen I U i) (y : retainedPieceOpen I U j) :
    retainedPieceMap I R U hU hd hc i x = retainedPieceMap I R U hU hd hc j y ↔
      x.val = y.val := by
  cases i with
  | none =>
    cases j with
    | none =>
      exact (retainedInclusion_openEmbedding I R U hU hd hc).injective.eq_iff.trans
        Subtype.ext_iff
    | some j => exact retainedPieceMap_retained_eq_iff I R U hU hd hc hUn j x y
  | some i =>
    cases j with
    | none =>
      exact eq_comm.trans ((retainedPieceMap_retained_eq_iff I R U hU hd hc hUn i y x).trans eq_comm)
    | some j =>
      by_cases hij : i = j
      · subst j
        exact (retainedPieceMap_openEmbedding I R U hU hd hc (some i)).injective.eq_iff.trans
          Subtype.ext_iff
      · constructor
        · intro hxy
          exact False.elim (Set.disjoint_left.mp (capInclusion_disjoint I R U hU hd hc hij)
            ⟨(R i).collapse x.val, rfl⟩ ⟨(R j).collapse y.val, hxy.symm⟩)
        · intro hxy
          exact False.elim (Set.disjoint_left.mp (hneck hij) x.property.1
            (hxy ▸ y.property.1))

omit [Countable ι] in
def retainedNeighborhood : Opens S.carrier :=
  ⟨⋃ j, (retainedPieceOpen I U j : Set S.carrier),
    isOpen_iUnion fun j => (retainedPieceOpen I U j).isOpen⟩

omit [Countable ι] in
theorem retainedPieceOpen_subset_neighborhood (j : Option ι) :
    (retainedPieceOpen I U j : Set S.carrier) ⊆ retainedNeighborhood I U :=
  fun _ hx => mem_iUnion.mpr ⟨j, hx⟩

def retainedMap (x : S.carrier) : (cutCarrier I R U hU hd hc).carrier := by
  classical
  exact if hx : x ∈ retainedNeighborhood I U then
    retainedPieceMap I R U hU hd hc (Classical.choose (mem_iUnion.mp hx))
      ⟨x, Classical.choose_spec (mem_iUnion.mp hx)⟩
  else retainedInclusion I R U hU hd hc (Classical.choice hU)

include hneck hUn in
theorem retainedMap_apply_piece (j : Option ι) (x : retainedPieceOpen I U j) :
    retainedMap I R U hU hd hc x.val = retainedPieceMap I R U hU hd hc j x := by
  unfold retainedMap
  split_ifs with hx
  · exact (retainedPieceMap_eq_iff I R U hU hd hc hneck hUn _ j _ x).mpr rfl
  · exact False.elim (hx (retainedPieceOpen_subset_neighborhood I U j x.property))

include hneck hUn in
theorem retainedMap_apply_retained (x : U) :
    retainedMap I R U hU hd hc x.val = retainedInclusion I R U hU hd hc x :=
  retainedMap_apply_piece I R U hU hd hc hneck hUn none x

include hneck hUn in
theorem retainedMap_apply_collar (i : ι) (x : S.carrier) (hx : x ∈ (I i).retainedCollar) :
    retainedMap I R U hU hd hc x = capInclusion I R U hU hd hc i ((R i).collapse x) :=
  retainedMap_apply_piece I R U hU hd hc hneck hUn (some i) ⟨x, hx⟩

include hneck hUn in
theorem retainedMap_injOn : Set.InjOn (retainedMap I R U hU hd hc)
    (retainedNeighborhood I U) := by
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  rw [retainedMap_apply_piece I R U hU hd hc hneck hUn i ⟨x, hi⟩,
    retainedMap_apply_piece I R U hU hd hc hneck hUn j ⟨y, hj⟩] at hxy
  exact (retainedPieceMap_eq_iff I R U hU hd hc hneck hUn i j _ _).mp hxy

include hneck hUn in
theorem retainedMap_localDiffeomorphAt (x : S.carrier) (hx : x ∈ retainedNeighborhood I U) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (retainedMap I R U hU hd hc) x := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  have heq : retainedMap I R U hU hd hc ∘
      (Subtype.val : retainedPieceOpen I U j → S.carrier) =
        retainedPieceMap I R U hU hd hc j :=
    funext (retainedMap_apply_piece I R U hU hd hc hneck hUn j)
  exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3)
    (retainedPieceOpen I U j) ⟨x, hj⟩).of_comp (by
      rw [heq]
      exact retainedPieceMap_localDiffeomorph I R U hU hd hc j ⟨x, hj⟩)

include hneck hUn in
theorem retainedMap_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞
    (retainedMap I R U hU hd hc) (retainedNeighborhood I U) :=
  fun x hx => (retainedMap_localDiffeomorphAt I R U hU hd hc hneck hUn x hx).contMDiffAt.contMDiffWithinAt

def retainedInverse : (cutCarrier I R U hU hd hc).carrier → S.carrier :=
  letI : Nonempty S.carrier := hU.map Subtype.val
  Function.invFunOn (retainedMap I R U hU hd hc) (retainedNeighborhood I U)

include hneck hUn in
theorem retainedInverse_left (x : S.carrier) (hx : x ∈ retainedNeighborhood I U) :
    retainedInverse I R U hU hd hc (retainedMap I R U hU hd hc x) = x := by
  let : Nonempty S.carrier := hU.map Subtype.val
  exact (retainedMap_injOn I R U hU hd hc hneck hUn).leftInvOn_invFunOn hx

theorem retainedInverse_mem (y : (cutCarrier I R U hU hd hc).carrier)
    (hy : y ∈ retainedMap I R U hU hd hc '' (retainedNeighborhood I U : Set S.carrier)) :
    retainedInverse I R U hU hd hc y ∈ retainedNeighborhood I U := by
  let : Nonempty S.carrier := hU.map Subtype.val
  exact Function.invFunOn_mem hy

theorem retainedInverse_right (y : (cutCarrier I R U hU hd hc).carrier)
    (hy : y ∈ retainedMap I R U hU hd hc '' (retainedNeighborhood I U : Set S.carrier)) :
    retainedMap I R U hU hd hc (retainedInverse I R U hU hd hc y) = y := by
  let : Nonempty S.carrier := hU.map Subtype.val
  exact Function.invFunOn_eq hy

include hneck hUn in
theorem retainedInverse_contMDiffAt (x : S.carrier) (hx : x ∈ retainedNeighborhood I U) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (retainedInverse I R U hU hd hc)
      (retainedMap I R U hU hd hc x) := by
  let hf := retainedMap_localDiffeomorphAt I R U hU hd hc hneck hUn x hx
  have hmem : ∀ᶠ y in 𝓝 (retainedMap I R U hU hd hc x),
      hf.localInverse y ∈ retainedNeighborhood I U :=
    hf.localInverse_contMDiffAt.continuousAt.preimage_mem_nhds
      ((retainedNeighborhood I U).isOpen.mem_nhds
        (by rwa [hf.localInverse_left_inv hf.localInverse_mem_target]))
  apply hf.localInverse_contMDiffAt.congr_of_eventuallyEq
  filter_upwards [hmem, hf.localInverse_eventuallyEq_right] with y hy hey
  have hyim : y ∈ retainedMap I R U hU hd hc '' (retainedNeighborhood I U : Set S.carrier) :=
    ⟨hf.localInverse y, hy, hey⟩
  exact retainedMap_injOn I R U hU hd hc hneck hUn
    (retainedInverse_mem I R U hU hd hc y hyim) hy
    ((retainedInverse_right I R U hU hd hc y hyim).trans hey.symm)

include hneck hUn in
theorem retainedInverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞
    (retainedInverse I R U hU hd hc)
    (retainedMap I R U hU hd hc '' (retainedNeighborhood I U : Set S.carrier)) := by
  rintro y ⟨x, hx, rfl⟩
  exact (retainedInverse_contMDiffAt I R U hU hd hc hneck hUn x hx).contMDiffWithinAt

include hneck hUn in
theorem retainedMap_openEmbedding : IsOpenEmbedding
    (fun x : retainedNeighborhood I U => retainedMap I R U hU hd hc x.val) := by
  have hs : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun x : retainedNeighborhood I U => retainedMap I R U hU hd hc x.val) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (retainedNeighborhood I U) x).comp
      (𝓡 3) (cutCarrier I R U hU hd hc).carrier
      (retainedMap_localDiffeomorphAt I R U hU hd hc hneck hUn x.val x.property)
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap hs.contMDiff.continuous
    (fun x y hxy => Subtype.ext (retainedMap_injOn I R U hU hd hc hneck hUn
      x.property y.property hxy)) hs.isOpenMap

end PoincareConjecture.Surgery.Terminal.Gluing
