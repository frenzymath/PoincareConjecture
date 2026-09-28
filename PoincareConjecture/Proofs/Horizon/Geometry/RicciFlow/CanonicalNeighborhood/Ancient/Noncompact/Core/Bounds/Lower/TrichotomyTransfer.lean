import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Lower.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Unlift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

attribute [local instance] RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  AncientKappaSolution.uliftSecondCountable AncientKappaSolution.uliftConnectedSpace

section Lift

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

private theorem ulift_down_metric (K : AncientKappaSolution 3 M)
    (f : UnitTwoSphere × ℝ → ULift.{u} M)
    (hf : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f)
    (t : ℝ) (p : UnitTwoSphere × ℝ)
    (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
    (K.flow.metric t).inner ((f p).down)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (ULift.down ∘ f) p a)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (ULift.down ∘ f) p b) =
      (K.ulift.flow.metric t).inner (f p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f p a)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f p b) := by
  let d : ULift.{u} M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M := Poincare.Manifold.uliftDiffeomorph (𝓡 3) M
  change (K.flow.metric t).inner (d (f p))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (d ∘ f) p a)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (d ∘ f) p b) = _
  rw [mfderiv_comp p (d.mdifferentiable (by simp) (f p)) (hf.mdifferentiable (by simp) p)]
  rfl

def M27SphereLineFlowCertificate.ofUlift
    (C : M27SphereLineFlowCertificate (K.ulift : AncientKappaSolution 3 (ULift.{u} M))) :
    M27SphereLineFlowCertificate K where
  sphere := C.sphere
  identification := C.identification.trans (Poincare.Manifold.uliftDiffeomorph (𝓡 3) M)
  metric_transport := by
    intro t ht p a b
    change (K.flow.metric t).inner ((C.identification p).down)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (ULift.down ∘ C.identification) p a)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (ULift.down ∘ C.identification) p b) = _
    rw [ulift_down_metric K C.identification C.identification.contMDiff]
    exact C.metric_transport t ht p a b

def M27ProjectivePlaneLineFlowCertificate.ofUlift
    (C : M27ProjectivePlaneLineFlowCertificate
      (K.ulift : AncientKappaSolution 3 (ULift.{u} M))) :
    M27ProjectivePlaneLineFlowCertificate K := by
  let d : ULift.{u} M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M := Poincare.Manifold.uliftDiffeomorph (𝓡 3) M
  refine {
    sphere := C.sphere
    cover := d ∘ C.cover
    cover_surjective := d.surjective.comp C.cover_surjective
    cover_local_diffeomorph := fun x =>
      (C.cover_local_diffeomorph x).comp (𝓡 3) M (d.isLocalDiffeomorph _)
    cover_fibers := fun p q => d.injective.eq_iff.trans (C.cover_fibers p q)
    product_homeomorph := d.symm.toHomeomorph.trans C.product_homeomorph
    product_coordinates := ?_
    metric_transport := ?_ }
  · intro p
    change C.product_homeomorph (d.symm (d (C.cover p))) = _
    rw [d.symm_apply_apply]
    exact C.product_coordinates p
  · intro t ht p a b
    change (K.flow.metric t).inner ((C.cover p).down)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (ULift.down ∘ C.cover) p a)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (ULift.down ∘ C.cover) p b) = _
    rw [ulift_down_metric K C.cover C.cover_local_diffeomorph.contMDiff]
    exact C.metric_transport t ht p a b

def M27TwistedSphereLineFlowCertificate.ofUlift
    (C : M27TwistedSphereLineFlowCertificate
      (K.ulift : AncientKappaSolution 3 (ULift.{u} M))) :
    M27TwistedSphereLineFlowCertificate K := by
  let d : ULift.{u} M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M := Poincare.Manifold.uliftDiffeomorph (𝓡 3) M
  refine {
    sphere := C.sphere
    involution_smooth := C.involution_smooth
    involution_free := C.involution_free
    involution_isometry := C.involution_isometry
    cover := d ∘ C.cover
    cover_surjective := d.surjective.comp C.cover_surjective
    cover_local_diffeomorph := fun x =>
      (C.cover_local_diffeomorph x).comp (𝓡 3) M (d.isLocalDiffeomorph _)
    cover_fibers := fun p q => d.injective.eq_iff.trans (C.cover_fibers p q)
    metric_transport := ?_
    puncture := C.puncture
    projective_topology := d.symm.toHomeomorph.trans C.projective_topology
    projective_smooth_cover := {
      cover := d ∘ C.projective_smooth_cover.cover
      image_eq := ?_
      fibers := fun x y hx hy =>
        d.injective.eq_iff.trans (C.projective_smooth_cover.fibers x y hx hy)
      local_diffeomorph := fun x =>
        (C.projective_smooth_cover.local_diffeomorph x).comp (𝓡 3) M
          (d.isLocalDiffeomorph _) } }
  · intro t ht p a b
    change (K.flow.metric t).inner ((C.cover p).down)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (ULift.down ∘ C.cover) p a)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (ULift.down ∘ C.cover) p b) = _
    rw [ulift_down_metric K C.cover C.cover_local_diffeomorph.contMDiff]
    exact C.metric_transport t ht p a b
  · rw [image_comp, C.projective_smooth_cover.image_eq]
    exact image_univ_of_surjective d.surjective

theorem positiveSectionalCurvature_of_ulift
    {t : ℝ} (hpos : M27PositiveSectionalCurvature
      (K.ulift : AncientKappaSolution 3 (ULift.{u} M)) t) :
    (K.flow.connection t).StrictlyPositiveSectionalCurvature := by
  let d : ULift.{u} M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M := Poincare.Manifold.uliftDiffeomorph (𝓡 3) M
  have hi : MetricHomothety (K.flow.metric t) (K.ulift.flow.metric t) d.symm 1 :=
    K.flow.metricHomothety_ulift t
  intro x a b ha hb hab
  have hmetric (v w : TangentSpace (𝓡 3) x) :
      (K.ulift.flow.metric t).inner (d.symm x)
        (mfderiv (𝓡 3) (𝓡 3) d.symm x v) (mfderiv (𝓡 3) (𝓡 3) d.symm x w) =
        (K.flow.metric t).inner x v w := by simpa only [one_mul] using hi x v w
  have hp := hpos (d.symm x) _ _
    ((hmetric a a).trans ha) ((hmetric b b).trans hb) ((hmetric a b).trans hab)
  have hsec := Homothety.homothety_sectionalCurvature_eq
    (K.flow.metric t) (K.ulift.flow.metric t) d.symm 1 zero_lt_one hi
    (K.flow.connection t) (K.ulift.flow.connection t) x a b
  rw [hsec, div_one] at hp
  exact hp

end Lift

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

theorem coreNormalizedCurvatureTrichotomy_of_originalFlow
    (hclassify : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M] (K : AncientKappaSolution 3 M),
      (∀ t : ℝ, t ≤ 0 → M27PositiveSectionalCurvature K t) ∨
        Nonempty (M27SphereLineFlowCertificate K) ∨
        Nonempty (M27ProjectivePlaneLineFlowCertificate K) ∨
        Nonempty (M27TwistedSphereLineFlowCertificate K)) :
    CoreNormalizedCurvatureTrichotomy := by
  intro kappa K
  rcases hclassify (K.flow.ulift : AncientKappaSolution 3 (ULift.{u} K.carrier.carrier)) with
    hpos | hsphere | hprojective | htwisted
  · exact Or.inl (fun t ht => positiveSectionalCurvature_of_ulift (hpos t ht))
  · obtain ⟨C⟩ := hsphere
    exact Or.inr (Or.inl ⟨C.ofUlift⟩)
  · obtain ⟨C⟩ := hprojective
    exact Or.inr (Or.inr (Or.inl ⟨C.ofUlift⟩))
  · obtain ⟨C⟩ := htwisted
    exact Or.inr (Or.inr (Or.inr ⟨C.ofUlift⟩))

end PoincareConjecture
