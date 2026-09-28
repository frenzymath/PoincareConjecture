import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.NonFilling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.NonFilling

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonTubeCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}

theorem no_compact_filling_of_contained_neck
    (tube : EpsilonTubeCertificate g X) (htube : tube.epsilon ≤ 1 / 200)
    (N : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200)
    (hsub : N.carrier ⊆ tube.carrier) (hsep : N.IsSeparating)
    (K : Set M) (hKsub : K ⊆ tube.carrier)
    (hfront : frontier K = N.central_sphere) (hint : (interior K).Nonempty) :
    ¬ IsCompact K := by
  intro hK
  let B := tube.chain
  have hBU : (B.unionOpen : Set M) = tube.carrier := tube.carrier_eq_chain_union.symm
  have hneck (i : ℤ) (hi : i ∈ B.shape.active) : (B.neck i).carrier ⊆ B.unionOpen :=
    fun _ hx => mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  have hNU : N.carrier ⊆ (B.unionOpen : Set M) := hsub.trans hBU.symm.subset
  obtain ⟨⟨i, hi⟩, hci⟩ := mem_iUnion.mp
    (hNU (N.central_sphere_subset N.center_on_central_sphere))
  obtain ⟨D, L, _, hLU, hefix, heS⟩ :=
    N.central_sphere_smooth_transport_of_center_mem (B.neck i) hN
      ((B.epsilon_eq i hi).trans_le htube) hci
  let e := D.toHomeomorph
  change e '' (B.neck i).central_sphere = N.central_sphere at heS
  have hecomp : e '' connectedComponent (B.neck i).center =
      connectedComponent N.center := by
    have himage := e.image_connectedComponentIn (s := univ)
      (x := (B.neck i).center) (mem_univ _)
    simp only [image_univ, e.surjective.range_eq, connectedComponentIn_univ] at himage
    apply himage.trans
    symm
    apply connectedComponent_eq
    apply N.carrier_subset_connectedComponent
    apply N.central_sphere_subset
    rw [← heS]
    exact mem_image_of_mem e (B.neck i).center_on_central_sphere
  have hLU' : L ⊆ (B.unionOpen : Set M) :=
    hLU.trans (union_subset hNU (hneck i hi))
  have heU : e '' (B.unionOpen : Set M) = B.unionOpen :=
    DeepHorn.image_eq_self_of_fixed_compl e
      (fun x hx => hefix x (fun h => hx (hLU' h)))
  have hiseparating : (B.neck i).IsSeparating :=
    ((B.neck i).isSeparating_iff_of_homeomorph N e hecomp heS).mpr hsep
  have hseparating : ∀ j ∈ B.shape.active, (B.neck j).IsSeparating := by
    intro j hj
    obtain ⟨D', _, _, _, _, _, hfS⟩ :=
      B.central_sphere_smooth_transport_of_epsilon_le htube i hi j hj
    let f := D'.toHomeomorph
    change f '' (B.neck i).central_sphere = (B.neck j).central_sphere at hfS
    have hfcomp : f '' connectedComponent (B.neck i).center =
        connectedComponent (B.neck j).center := by
      have himage := f.image_connectedComponentIn (s := univ)
        (x := (B.neck i).center) (mem_univ _)
      simp only [image_univ, f.surjective.range_eq, connectedComponentIn_univ] at himage
      apply himage.trans
      symm
      apply connectedComponent_eq
      apply (B.neck j).carrier_subset_connectedComponent
      apply (B.neck j).central_sphere_subset
      rw [← hfS]
      exact mem_image_of_mem f (B.neck i).center_on_central_sphere
    exact ((B.neck i).isSeparating_iff_of_homeomorph (B.neck j) f hfcomp hfS).mp
      hiseparating
  have hinverse : e.symm '' (B.unionOpen : Set M) = B.unionOpen :=
    (congrArg (fun S => e.symm '' S) heU).symm.trans (e.symm_image_image _)
  have hcore : e.symm '' K ⊆ (B.unionOpen : Set M) := by
    rw [← hinverse]
    exact image_mono (hKsub.trans hBU.symm.subset)
  have hfront' : frontier (e.symm '' K) = (B.neck i).central_sphere := by
    rw [← e.symm.image_frontier, hfront, ← heS]
    exact e.symm_image_image _
  have hint' : (interior (e.symm '' K)).Nonempty := by
    rw [← e.symm.image_interior]
    exact hint.image e.symm
  exact B.no_compact_filling_of_epsilon_le htube hseparating i hi _ hcore hfront' hint'
    (hK.image e.symm.continuous)

end PoincareConjecture.EpsilonTubeCertificate
