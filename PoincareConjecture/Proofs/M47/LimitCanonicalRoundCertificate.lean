import PoincareConjecture.Proofs.M47.LimitCanonicalRoundComparison
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option linter.style.haveILetI false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable def limitCanonical_round_image
    {C D : GeneralizedSliceCarrier.{u}} [ConnectedSpace C.carrier]
    {K : AncientKappaSolution 3 C.carrier} {epsilon : ℝ}
    (N : M27EpsilonRoundComponent K 0 epsilon)
    (g : RiemannianMetric 3 D.carrier)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier D.carrier ∞)
    (hsource : f.source = univ) (y : C.carrier) (Q : ℝ) (hQ : 0 < Q)
    (hcompare :
      letI : TopologicalSpace N.reference := N.reference_topology
      letI : ChartedSpace E3 N.reference := N.reference_charted
      letI : IsManifold (𝓡 3) ∞ N.reference := N.reference_manifold
      ∃ bound : ℝ, bound < epsilon ^ 2 ∧ ∀ x : N.reference,
        singularMetricJetErrorSquared N.reference_metric N.reference_connection
          (fun z v => (N.scale * Q) *
            singularMetricPullback g (f ∘ N.identification) z v)
          (Nat.floor epsilon⁻¹) x ≤ bound) :
    SingularRoundComponent g epsilon := by
  letI : TopologicalSpace N.reference := N.reference_topology
  letI : ChartedSpace E3 N.reference := N.reference_charted
  letI : IsManifold (𝓡 3) ∞ N.reference := N.reference_manifold
  letI : MeasurableSpace N.reference := borel N.reference
  letI : BorelSpace N.reference := ⟨rfl⟩
  letI : T3Space N.reference := N.identification.toHomeomorph.isEmbedding.t3Space
  letI : T2Space N.reference := N.identification.toHomeomorph.isEmbedding.t2Space
  letI : SecondCountableTopology N.reference :=
    N.identification.toHomeomorph.isInducing.secondCountableTopology
  letI : ConnectedSpace N.reference := N.reference_connected
  letI : CompactSpace C.carrier := isCompact_univ_iff.mp N.compact
  let model : GeneralizedSliceCarrier.{u} :=
    { carrier := N.reference
      topologicalSpace := inferInstance
      measurableSpace := inferInstance
      borelSpace := inferInstance
      chartedSpace := inferInstance
      isManifold := inferInstance
      t2Space := inferInstance
      t3Space := inferInstance
      secondCountable := inferInstance }
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    contMDiffOn_univ.mp (hsource ▸ f.contMDiffOn_toFun)
  have himage : f '' univ = f.target := by
    simpa only [hsource] using f.toPartialEquiv.image_source_eq_target
  refine {
    epsilon_pos := N.epsilon_pos
    basepoint := f y
    carrier := f.target
    component_eq := limitCanonical_target_eq_connectedComponent f hsource y
    compact := by rw [← himage]; exact N.compact.image hf.continuous
    model := model
    model_compact := N.reference_compact
    model_connected := isConnected_univ
    model_metric := N.reference_metric
    model_connection := N.reference_connection
    model_curvature_one := ?_
    forward := f ∘ N.identification
    inverse := N.identification.symm ∘ f.symm
    forward_image := ?_
    forward_openEmbedding :=
      (f.toOpenPartialHomeomorph.isOpenEmbedding hsource).comp
        N.identification.toHomeomorph.isOpenEmbedding
    forward_smooth := hf.comp N.identification.contMDiff
    inverse_smooth := N.identification.symm.contMDiff.comp_contMDiffOn f.contMDiffOn_invFun
    left_inverse := ?_
    right_inverse := ?_
    scale := N.scale * Q
    scale_pos := mul_pos N.scale_pos hQ
    metric_comparison := hcompare }
  · intro x v w hvw
    exact N.reference_sectional_one x v w hvw.1 hvw.2.1 hvw.2.2
  · have hrange : range N.identification = univ := N.identification.surjective.range_eq
    rw [range_comp, hrange]
    exact himage
  · intro x
    change N.identification.symm (f.symm (f (N.identification x))) = x
    exact (congrArg N.identification.symm (f.left_inv (hsource ▸ mem_univ _))).trans
      (N.identification.symm_apply_apply x)
  · intro x hx
    change f (N.identification (N.identification.symm (f.symm x))) = x
    rw [N.identification.apply_symm_apply]
    exact f.right_inv hx

end PoincareConjecture.M47
