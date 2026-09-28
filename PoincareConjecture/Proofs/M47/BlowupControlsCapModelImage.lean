import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Lift
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceModelTransport










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} {X : Type (max u v)}
  [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]




noncomputable def capModel_transport_lift
    {kind : CapModelKind} {p : RealProjectiveThree}
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (K : CapModelEquivalence kind p e.source) :
    CapModelEquivalence kind p e.target := by
  letI : TopologicalSpace K.model := K.model_topology
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) K.model := K.model_charted
  letI : IsManifold (𝓡 3) ∞ K.model := K.model_manifold
  let L := ULift.{v} K.model
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L :=
    Poincare.Manifold.uliftChartedSpace _ K.model
  letI : IsManifold (𝓡 3) ∞ L := Poincare.Manifold.uliftIsManifold (𝓡 3) K.model
  let d : Diffeomorph (𝓡 3) (𝓡 3) L K.model ∞ :=
    Poincare.Manifold.uliftDiffeomorph (𝓡 3) K.model
  refine {
    model := L
    model_topology := inferInstance
    model_charted := inferInstance
    model_manifold := inferInstance
    standard_model := ?_
    standard_smooth := ?_
    forward := d.symm ∘ K.forward ∘ e.symm
    inverse := e ∘ K.inverse ∘ d
    inverse_mem := fun y => e.toPartialEquiv.map_source (K.inverse_mem (d y))
    left_inverse := ?_
    right_inverse := ?_
    forward_smooth := ?_
    inverse_smooth := ?_
  }
  · cases kind with
    | euclidean =>
      exact ((d.toHomeomorph.trans K.standard_model).trans Homeomorph.ulift).trans
        Homeomorph.ulift.symm
    | puncturedProjective =>
      exact ((d.toHomeomorph.trans K.standard_model).trans Homeomorph.ulift).trans
        Homeomorph.ulift.symm
  · cases kind with
    | euclidean =>
      obtain ⟨k⟩ := K.standard_smooth
      exact ⟨d.trans k⟩
    | puncturedProjective =>
      obtain ⟨k⟩ := K.standard_smooth
      refine ⟨{
        cover := d.symm ∘ k.cover
        image_eq := ?_
        fibers := ?_
        local_diffeomorph := ?_
      }⟩
      · rw [image_comp, k.image_eq, image_univ]
        exact d.symm.surjective.range_eq
      · intro x y hx hy
        exact d.symm.injective.eq_iff.trans (k.fibers x y hx hy)
      · intro x
        exact (k.local_diffeomorph x).comp (𝓡 3) L (d.symm.isLocalDiffeomorph (k.cover x))
  · intro x hx
    simp only [Function.comp_apply, d.apply_symm_apply]
    exact (congrArg (fun y => e y)
      (K.left_inverse _ (e.toPartialEquiv.map_target hx))).trans (e.toPartialEquiv.right_inv hx)
  · intro y
    simp only [Function.comp_apply]
    exact (congrArg (fun z => d.symm (K.forward z))
      (e.toPartialEquiv.left_inv (K.inverse_mem (d y)))).trans
      ((congrArg d.symm (K.right_inverse (d y))).trans (d.symm_apply_apply y))
  · apply (d.symm.contMDiff.contMDiffOn (s := univ)).comp
      (K.forward_smooth.comp e.contMDiffOn_invFun (fun _ hx => e.toPartialEquiv.map_target hx))
    exact fun _ _ => mem_univ _
  · apply e.contMDiffOn_toFun.comp
      (K.inverse_smooth.comp d.contMDiff.contMDiffOn (fun _ _ => mem_univ _))
    exact fun y _ => K.inverse_mem (d y)

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]



theorem nonempty_cap_image_model {g : RiemannianMetric 3 M} (N : CapCertificate g)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hsource : N.carrier ⊆ e.source) :
    Nonempty (CapModelEquivalence N.model_kind N.puncture (e '' N.carrier)) := by
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞ := {
    toFun := e
    invFun := e.symm
    source := N.carrier
    target := e '' N.carrier
    open_source := N.carrier_open
    open_target := e.isOpen_image_of_subset_source N.carrier_open hsource
    map_source' := fun x hx => ⟨x, hx, rfl⟩
    map_target' := by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [e.left_inv (hsource hx)] using hx
    left_inv' := fun x hx => e.left_inv (hsource hx)
    right_inv' := by
      rintro _ ⟨x, hx, rfl⟩
      exact e.right_inv (e.map_source (hsource hx))
    contMDiffOn_toFun := hf.mono hsource
    contMDiffOn_invFun := hi.mono (by
      rintro _ ⟨x, hx, rfl⟩
      exact e.map_source (hsource hx))
  }
  exact ⟨capModel_transport_lift d N.model_equivalence⟩

end PoincareConjecture.M47
