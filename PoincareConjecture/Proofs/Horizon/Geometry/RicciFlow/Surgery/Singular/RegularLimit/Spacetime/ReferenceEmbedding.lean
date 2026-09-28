import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.Geometry








set_option autoImplicit false

open Set Function TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SingularTimeReference

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]


def interiorSpacetimeForward (R : SingularTimeReference F T M)
    (p : Ioo R.tMinus T × M) : F.point :=
  R.spacetime_forward (⟨p.1, ⟨p.1.property.1.le, p.1.property.2⟩⟩, p.2)

@[simp] theorem interiorSpacetimeForward_time (R : SingularTimeReference F T M)
    (p : Ioo R.tMinus T × M) :
    (R.interiorSpacetimeForward p).1 = (p.1 : ℝ) :=
  R.spacetime_time _


theorem interiorSpacetimeForward_range (R : SingularTimeReference F T M) :
    range R.interiorSpacetimeForward = {p : F.point | p.1 ∈ Ioo R.tMinus T} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simpa only [mem_ofPred_eq, interiorSpacetimeForward_time] using q.1.property
  · intro hp
    have hp' : p ∈ range R.spacetime_forward := by
      rw [R.spacetime_image]
      exact ⟨hp.1.le, hp.2⟩
    obtain ⟨⟨t, x⟩, htx⟩ := hp'
    have ht : (t : ℝ) = p.1 := (R.spacetime_time (t, x)).symm.trans (congrArg Sigma.fst htx)
    refine ⟨(⟨t, ht.symm ▸ hp⟩, x), ?_⟩
    exact htx


theorem interiorSpacetimeForward_isOpenEmbedding (R : SingularTimeReference F T M) :
    IsOpenEmbedding R.interiorSpacetimeForward := by
  refine ⟨?_, ?_⟩
  · exact R.spacetime_embedding.comp
      ((IsEmbedding.inclusion (show Ioo R.tMinus T ⊆ Ico R.tMinus T from
        fun _ ht => ⟨ht.1.le, ht.2⟩)).prodMap IsEmbedding.id)
  · rw [R.interiorSpacetimeForward_range]
    exact isOpen_Ioo.preimage F.time_continuous


def openSpacetimeForward (R : SingularTimeReference F T M) (U : Opens M)
    (p : Ioo R.tMinus T × U) : F.point :=
  R.interiorSpacetimeForward (p.1, p.2)

@[simp] theorem openSpacetimeForward_time (R : SingularTimeReference F T M)
    (U : Opens M) (p : Ioo R.tMinus T × U) :
    (R.openSpacetimeForward U p).1 = (p.1 : ℝ) :=
  R.interiorSpacetimeForward_time _


theorem openSpacetimeForward_eq (R : SingularTimeReference F T M)
    (U : Opens M) (p : Ioo R.tMinus T × U) :
    R.openSpacetimeForward U p =
      (⟨p.1, R.forward p.1 ⟨p.1.property.1.le, p.1.property.2⟩ p.2⟩ : F.point) :=
  Sigma.ext (R.spacetime_time _) (R.spacetime_spatial _)


theorem openSpacetimeForward_isOpenEmbedding (R : SingularTimeReference F T M)
    (U : Opens M) : IsOpenEmbedding (R.openSpacetimeForward U) :=
  R.interiorSpacetimeForward_isOpenEmbedding.comp (IsOpenEmbedding.id.prodMap U.isOpenEmbedding')

theorem openSpacetimeForward_injective (R : SingularTimeReference F T M) (U : Opens M) :
    Injective (R.openSpacetimeForward U) :=
  (R.openSpacetimeForward_isOpenEmbedding U).injective


theorem mem_range_openSpacetimeForward_iff (R : SingularTimeReference F T M)
    (U : Opens M) (p : F.point) :
    p ∈ range (R.openSpacetimeForward U) ↔
      ∃ ht : p.1 ∈ Ioo R.tMinus T,
        R.inverse p.1 ⟨ht.1.le, ht.2⟩ p.2 ∈ U := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [R.openSpacetimeForward_eq]
    refine ⟨q.1.property, ?_⟩
    change R.inverse q.1 _ (R.forward q.1 _ q.2) ∈ U
    exact (R.left_inverse q.1 ⟨q.1.property.1.le, q.1.property.2⟩ (q.2 : M)).symm ▸
      q.2.property
  · rintro ⟨ht, hx⟩
    refine ⟨(⟨p.1, ht⟩, ⟨R.inverse p.1 ⟨ht.1.le, ht.2⟩ p.2, hx⟩), ?_⟩
    rw [R.openSpacetimeForward_eq]
    exact Sigma.ext rfl (heq_of_eq (R.right_inverse p.1 ⟨ht.1.le, ht.2⟩ p.2))

end PoincareConjecture.SingularTimeReference
