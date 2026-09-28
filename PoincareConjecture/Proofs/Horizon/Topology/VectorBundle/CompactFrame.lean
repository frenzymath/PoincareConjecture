import PoincareConjecture.Proofs.Horizon.Topology.VectorBundle.CompactDisk
import Mathlib.Analysis.InnerProductSpace.Orthonormal








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Topology

namespace Poincare.VectorBundle

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  {I : Type*}


def fiberFamilies (I : Type*) : Set (B × (I → TotalSpace F E)) :=
  {q | ∀ i, (q.2 i).1 = q.1}

namespace FiberFamily


def vector (q : fiberFamilies (F := F) (E := E) I) (i : I) : E q.val.1 :=
  cast (congrArg E (q.property i)) (q.val.2 i).2

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, NormedAddCommGroup (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
lemma totalSpace_vector (q : fiberFamilies (F := F) (E := E) I) (i : I) :
    (⟨q.val.1, vector q i⟩ : TotalSpace F E) = q.val.2 i := by
  exact TotalSpace.mk_cast (q.property i) (q.val.2 i).2

omit [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ x, InnerProductSpace ℝ (E x)] [∀ x, NormedAddCommGroup (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
lemma continuous_vector (i : I) :
    Continuous (fun q : fiberFamilies (F := F) (E := E) I =>
      (⟨q.val.1, vector q i⟩ : TotalSpace F E)) := by
  simp only [totalSpace_vector]
  exact (continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)

lemma continuous_inner (i j : I) :
    Continuous (fun q : fiberFamilies (F := F) (E := E) I =>
      inner ℝ (vector q i) (vector q j)) :=
  (continuous_vector i).inner_bundle (continuous_vector j)

end FiberFamily

omit [NormedSpace ℝ F] [∀ x, InnerProductSpace ℝ (E x)]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
lemma isClosed_fiberFamilies [T2Space B] :
    IsClosed (fiberFamilies (F := F) (E := E) I) := by
  have heq : fiberFamilies (F := F) (E := E) I =
      ⋂ i, {q : B × (I → TotalSpace F E) | (q.2 i).1 = q.1} := by
    ext q
    simp only [fiberFamilies, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_eq
    ((FiberBundle.continuous_proj F E).comp ((continuous_apply i).comp continuous_snd))
    continuous_fst



theorem isCompact_orthonormalFamilies_over [Fintype I] [T2Space B]
    [LocallyCompactSpace B] [FiniteDimensional ℝ F]
    {K : Set B} (hK : IsCompact K) :
    IsCompact {q : fiberFamilies (F := F) (E := E) I |
      q.val.1 ∈ K ∧ Orthonormal ℝ (FiberFamily.vector q)} := by
  classical
  let D : Set (TotalSpace F E) := {q | q.1 ∈ K ∧ ‖q.2‖ ≤ 1}
  have hD : IsCompact D := isCompact_disk_over hK 1
  have hproduct : IsCompact (K ×ˢ Set.pi univ (fun _ : I => D)) :=
    hK.prod (isCompact_univ_pi fun _ => hD)
  have hemb : Topology.IsClosedEmbedding
      (Subtype.val : fiberFamilies (F := F) (E := E) I → B × (I → TotalSpace F E)) :=
    isClosed_fiberFamilies.isClosedEmbedding_subtypeVal
  have horth : IsClosed {q : fiberFamilies (F := F) (E := E) I |
      Orthonormal ℝ (FiberFamily.vector q)} := by
    have heq : {q : fiberFamilies (F := F) (E := E) I |
        Orthonormal ℝ (FiberFamily.vector q)} =
        ⋂ i, ⋂ j, {q | inner ℝ (FiberFamily.vector q i) (FiberFamily.vector q j) =
          if i = j then 1 else 0} := by
      ext q
      simp only [mem_ofPred_eq, mem_iInter, orthonormal_iff_ite]
    rw [heq]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (FiberFamily.continuous_inner i j) continuous_const
  have hclosed : IsClosed {q : fiberFamilies (F := F) (E := E) I |
      q.val.1 ∈ K ∧ Orthonormal ℝ (FiberFamily.vector q)} :=
    (hK.isClosed.preimage (continuous_fst.comp continuous_subtype_val)).inter horth
  apply (hemb.isCompact_preimage hproduct).of_isClosed_subset hclosed
  intro q hq
  refine ⟨hq.1, ?_⟩
  intro i _
  refine ⟨(q.property i).symm ▸ hq.1, ?_⟩
  have hnorm : ‖(q.val.2 i).2‖ = ‖FiberFamily.vector q i‖ :=
    congrArg (fun z : TotalSpace F E => ‖z.2‖) (FiberFamily.totalSpace_vector q i).symm
  rw [hnorm, hq.2.norm_eq_one i]

end Poincare.VectorBundle
