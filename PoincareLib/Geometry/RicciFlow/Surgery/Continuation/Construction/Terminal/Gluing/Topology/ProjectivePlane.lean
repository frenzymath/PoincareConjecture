import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.Tips
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.Punctures
import PoincareLib.Topology.Gluing.Embedding

/-!
# Preservation of the absence of a two-sided projective plane

The surgery quotient minus its cap tips openly embeds in the original
manifold. An open projective-plane product can avoid finitely many points,
so the original no-projective-plane property passes to the actual quotient.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)
  (hneck : Pairwise (fun i j => Disjoint (I i).neck.carrier (I j).neck.carrier))
  (hUn : ∀ i, (U : Set S.carrier) ∩ (I i).neck.carrier = (I i).negativeHalf)

include hneck hUn in
theorem exists_puncturedCut_openEmbedding :
    ∃ e : ((cutTips I R U hU hd hc)ᶜ : Set (cutCarrier I R U hU hd hc).carrier) → S.carrier,
      IsOpenEmbedding e := by
  obtain ⟨e, he, -⟩ := Poincare.Gluing.exists_isOpenEmbedding_iUnion_ranges
    (puncturedInclusion_openEmbedding I R U hU hd hc)
    (puncturedOriginal_openEmbedding I R U)
    (puncturedOriginal_eq_iff I R U hU hd hc hneck hUn)
  let a := Homeomorph.setCongr (puncturedInclusion_iUnion_range I R U hU hd hc).symm
  exact ⟨e ∘ a, he.comp a.isOpenEmbedding⟩

include hneck hUn in
theorem cutCarrier_noTwoSidedProjectivePlane [Finite ι]
    (hS : SurgeryNoTwoSidedProjectivePlane S) :
    SurgeryNoTwoSidedProjectivePlane (cutCarrier I R U hU hd hc) := by
  obtain ⟨e, he⟩ := exists_puncturedCut_openEmbedding I R U hU hd hc hneck hUn
  exact no_two_sided_projective_plane_of_punctured_embedding
    (cutTips_finite I R U hU hd hc) he hS

end PoincareMT.Surgery.Terminal.Gluing
