import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialStar
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentFiniteModel




noncomputable section
open Set Geometry Metric

namespace PoincareConjecture.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hull_subset_of_closed_partition
    (K : SimplicialComplex ℝ E) {D C : Set E}
    (hD : IsClosed D) (hC : IsClosed C) (hdis : Disjoint D C)
    (hcover : K.space ⊆ D ∪ C) {s : Finset E} (hs : s ∈ K.faces)
    (hmeet : (convexHull ℝ (s : Set E) ∩ D).Nonempty) :
    convexHull ℝ (s : Set E) ⊆ D := by
  intro x hx
  by_contra hn
  have hxC := (hcover (SimplicialComplex.convexHull_subset_space hs hx)).resolve_left hn
  obtain ⟨y, _, hyD, hyC⟩ := isPreconnected_closed_iff.mp
    (convex_convexHull ℝ (s : Set E)).isPreconnected D C hD hC
      ((SimplicialComplex.convexHull_subset_space hs).trans hcover) hmeet ⟨x, hx, hxC⟩
  exact disjoint_left.mp hdis hyD hyC



theorem closed_piece_vertexSubcomplex_space
    (K : SimplicialComplex ℝ E) {D C : Set E}
    (hD : IsClosed D) (hC : IsClosed C) (hdis : Disjoint D C)
    (hcover : K.space = D ∪ C) :
    (K.vertexSubcomplex D).space = D := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs.1
    exact hull_subset_of_closed_partition K hD hC hdis hcover.subset hs.1
      ⟨v, subset_convexHull ℝ (s : Set E) hv, hs.2 v hv⟩ hxs
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp
      (hcover.symm.subset (Or.inl hx))
    have hall := hull_subset_of_closed_partition K hD hC hdis hcover.subset hs ⟨x, hxs, hx⟩
    exact SimplicialComplex.mem_space_iff.mpr
      ⟨s, ⟨hs, fun v hv => hall (subset_convexHull ℝ (s : Set E) hv)⟩, hxs⟩


theorem closed_piece_vertexSubcomplex_coface
    (K : SimplicialComplex ℝ E) {D C : Set E}
    (hD : IsClosed D) (hC : IsClosed C) (hdis : Disjoint D C)
    (hcover : K.space ⊆ D ∪ C) {s t : Finset E}
    (hs : s ∈ (K.vertexSubcomplex D).faces) (ht : t ∈ K.faces) (hst : s ⊆ t) :
    t ∈ (K.vertexSubcomplex D).faces := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs.1
  have hall := hull_subset_of_closed_partition K hD hC hdis hcover ht
    ⟨v, subset_convexHull ℝ (t : Set E) (hst hv), hs.2 v hv⟩
  exact ⟨ht, fun w hw => hall (subset_convexHull ℝ (t : Set E) hw)⟩

theorem closed_piece_vertexSubcomplex_link
    [DecidableEq E]
    (K : SimplicialComplex ℝ E) {D C : Set E}
    (hD : IsClosed D) (hC : IsClosed C) (hdis : Disjoint D C)
    (hcover : K.space ⊆ D ∪ C) {v : E}
    (hv : v ∈ (K.vertexSubcomplex D).vertices) :
    (K.vertexSubcomplex D).link v = K.link v := by
  classical
  apply SimplicialComplex.ext
  ext s
  change (s ∈ (K.vertexSubcomplex D).faces ∧ v ∉ s ∧
      insert v s ∈ (K.vertexSubcomplex D).faces) ↔
    (s ∈ K.faces ∧ v ∉ s ∧ insert v s ∈ K.faces)
  constructor
  · exact fun h => ⟨h.1.1, h.2.1, h.2.2.1⟩
  · intro h
    have hbig := closed_piece_vertexSubcomplex_coface K hD hC hdis hcover hv h.2.2
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
    exact ⟨(K.vertexSubcomplex D).down_closed hbig (Finset.subset_insert _ _)
      (K.nonempty_of_mem_faces h.1), h.2.1, hbig⟩



def markedDiskSignCoordinates {ι : Type*} [Fintype ι] [Unique ι] :
    Bool ≃ₜ sphere (0 : ι → ℝ) 1 := by
  let f : Bool → sphere (0 : ι → ℝ) 1 := fun side =>
    ⟨fun _ => if side then (1 : ℝ) else -1, by
      rw [mem_sphere_zero_iff_norm, pi_norm_const, Real.norm_eq_abs]
      cases side <;> norm_num⟩
  have hf : Continuous f := continuous_of_discreteTopology
  have hfi : Function.Injective f := by
    intro a b hab
    have h := congrArg (fun z : sphere (0 : ι → ℝ) 1 => z.val default) hab
    cases a <;> cases b
    · rfl
    · change (-1 : ℝ) = 1 at h
      linarith
    · change (1 : ℝ) = -1 at h
      linarith
    · rfl
  have hfs : Function.Surjective f := by
    intro x
    have hconst : x.val = fun _ => x.val default := by
      funext k
      exact congrArg x.val (Subsingleton.elim _ _)
    have hn : |x.val default| = 1 := by
      have h := mem_sphere_zero_iff_norm.mp x.property
      rw [hconst, pi_norm_const, Real.norm_eq_abs] at h
      exact h
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with h | h
    · refine ⟨true, Subtype.ext ?_⟩
      change (fun _ => (1 : ℝ)) = x.val
      rw [hconst, h]
    · refine ⟨false, Subtype.ext ?_⟩
      change (fun _ => (-1 : ℝ)) = x.val
      rw [hconst, h]
  exact (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorphOfSurjective hfs

theorem markedDiskSignCoordinates_apply {ι : Type*} [Fintype ι] [Unique ι] (side : Bool) :
    (markedDiskSignCoordinates (ι := ι) side : ι → ℝ) =
      fun _ => if side then 1 else -1 := rfl

def markedDiskProductCoordinates {ι κ Y : Type*}
    [Fintype ι] [Unique ι] [Fintype κ] [TopologicalSpace Y]
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ Y) :
    (Bool × closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ Y :=
  (markedDiskSignCoordinates.prodCongr (Homeomorph.refl _)).trans
    ((Homeomorph.Set.prod _ _).symm.trans P)



theorem exists_marked_two_component_models
    [DecidableEq E] {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (P : (Bool × A) ≃ₜ K.space) :
    ∃ (J : Bool → SimplicialComplex ℝ E) (H : ∀ side, A ≃ₜ (J side).space),
      (∀ side, (J side).faces.Finite ∧ J side ≤ K) ∧
      (∀ side x, (H side x : E) = (P (side, x) : E)) ∧
      Disjoint (J false).space (J true).space ∧
      (J false).space ∪ (J true).space = K.space ∧
      (∀ side s t, s ∈ (J side).faces → t ∈ K.faces → s ⊆ t → t ∈ (J side).faces) ∧
      ∀ side v, v ∈ (J side).vertices → (J side).link v = K.link v := by
  let f (side : Bool) : A → E := fun x => (P (side, x) : E)
  let D (side : Bool) : Set E := range (f side)
  have hf (side) : Continuous (f side) := continuous_subtype_val.comp
    (P.continuous.comp (continuous_const.prodMk continuous_id))
  have hfi (side) : Function.Injective (f side) := by
    intro x y hxy
    exact congrArg Prod.snd (P.injective (Subtype.ext hxy))
  have hD (side) : IsClosed (D side) := (isCompact_range (hf side)).isClosed
  have hdis : Disjoint (D false) (D true) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have h := congrArg Prod.fst (P.injective (Subtype.ext hy))
    cases h
  have hcover : K.space = D false ∪ D true := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨⟨side, x⟩, hx⟩ := P.surjective ⟨z, hz⟩
      cases side
      · exact Or.inl ⟨x, congrArg Subtype.val hx⟩
      · exact Or.inr ⟨x, congrArg Subtype.val hx⟩
    · rintro z (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact (P (_, x)).property
  have hdisSide (side) : Disjoint (D side) (D (!side)) := by
    cases side
    · exact hdis
    · exact hdis.symm
  have hcoverSide (side) : K.space = D side ∪ D (!side) := by
    cases side
    · exact hcover
    · exact hcover.trans (union_comm _ _)
  let J (side) := K.vertexSubcomplex (D side)
  have hJs (side) : (J side).space = D side :=
    closed_piece_vertexSubcomplex_space K (hD side) (hD (!side)) (hdisSide side)
      (hcoverSide side)
  let Q (side) : A ≃ₜ D side :=
    (hf side).isClosedEmbedding (hfi side) |>.toHomeomorph
  let H (side) : A ≃ₜ (J side).space := (Q side).trans (Homeomorph.setCongr (hJs side).symm)
  refine ⟨J, H, fun side => ⟨K.vertexSubcomplex_finite _ hK, K.vertexSubcomplex_le _⟩,
    fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · rw [hJs false, hJs true]
    exact hdis
  · rw [hJs false, hJs true]
    exact hcover.symm
  · intro side s t hs ht hst
    exact closed_piece_vertexSubcomplex_coface K (hD side) (hD (!side)) (hdisSide side)
      (hcoverSide side).subset hs ht hst
  · intro side v hv
    exact closed_piece_vertexSubcomplex_link K (hD side) (hD (!side)) (hdisSide side)
      (hcoverSide side).subset hv



theorem exists_marked_disk_component_models
    [DecidableEq E] {ι κ : Type*} [Fintype ι] [Unique ι] [Fintype κ]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ K.space) :
    ∃ (J : Bool → SimplicialComplex ℝ E)
      (H : ∀ side, closedBall (0 : κ → ℝ) (3 / 2) ≃ₜ (J side).space),
      (∀ side, (J side).faces.Finite ∧ J side ≤ K ∧ ContractibleSpace (J side).space) ∧
      (∀ side x, (H side x : E) =
        (P ⟨((markedDiskSignCoordinates (ι := ι) side : ι → ℝ), (x : κ → ℝ)),
          (markedDiskSignCoordinates (ι := ι) side).property, x.property⟩ : E)) ∧
      Disjoint (J false).space (J true).space ∧
      (J false).space ∪ (J true).space = K.space ∧
      (∀ side s t, s ∈ (J side).faces → t ∈ K.faces → s ⊆ t → t ∈ (J side).faces) ∧
      ∀ side v, v ∈ (J side).vertices → (J side).link v = K.link v := by
  let : CompactSpace (closedBall (0 : κ → ℝ) (3 / 2)) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : ContractibleSpace (closedBall (0 : κ → ℝ) (3 / 2)) :=
    (convex_closedBall (0 : κ → ℝ) (3 / 2)).contractibleSpace
      ⟨0, mem_closedBall_self (by norm_num)⟩
  obtain ⟨J, H, hJ, hH, hdis, hcover, hcofaces, hlinks⟩ :=
    exists_marked_two_component_models K hK (markedDiskProductCoordinates P)
  exact ⟨J, H, fun side => ⟨(hJ side).1, (hJ side).2, (H side).symm.contractibleSpace⟩,
    hH, hdis, hcover, hcofaces, hlinks⟩

end PoincareConjecture.M76
