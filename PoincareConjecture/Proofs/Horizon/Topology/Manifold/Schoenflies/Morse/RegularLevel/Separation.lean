import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Tube
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Components
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.SphereConnectivity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private theorem exists_sphere_circle_collar_complementary_regions
    {ε : Real} (hε : 0 < ε) (F : OpenPartialHomeomorph (S1 × Real) S2)
    (hsource : F.source = univ ×ˢ Ioo (-ε) ε) :
    let C := range (fun q : S1 => F (q, 0))
    ∃ A B : Set S2,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = Cᶜ ∧ frontier A = C ∧ frontier B = C ∧
      F '' (univ ×ˢ Ioo (-ε) 0) ⊆ A ∧ F '' (univ ×ˢ Ioo 0 ε) ⊆ B := by
  let : SimplyConnectedSpace S2 :=
    Poincare.Topology.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  let : LocallyPathConnectedSpace S2 := ChartedSpace.locallyPathConnectedSpace E2 S2
  let : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E2) (by rw [← Module.finrank_eq_rank]; norm_num)
      0 zero_le_one)
  let e : (S1 × Ioo (-ε) ε) ≃ₜ F.target :=
    ((Homeomorph.Set.prod (univ : Set S1) (Ioo (-ε) ε)).trans
      ((Homeomorph.Set.univ S1).prodCongr (Homeomorph.refl _))).symm.trans
        ((Homeomorph.setCongr hsource.symm).trans F.toHomeomorphSourceTarget)
  obtain ⟨A, B, hA, hB, hAc, hBc, hdis, hcover, hfA, hfB, hneg, hpos⟩ :=
    Poincare.Topology.exists_collar_complementary_regions hε F.open_target e
  refine ⟨A, B, hA, hB, hAc, hBc, hdis, hcover, hfA, hfB, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hneg ⟨(z.1, ⟨z.2, hz.2.1, hz.2.2.trans hε⟩), hz.2.2, rfl⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hpos ⟨(z.1, ⟨z.2, (neg_lt_zero.mpr hε).trans hz.2.1, hz.2.2⟩), hz.2.1, rfl⟩

theorem exists_regular_level_component_complementary_regions
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hfinite : {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0}.Finite)
    (c : Real) (hc : ∀ p, h p = c -> mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (p : S2) (hp : h p = c) :
    let C := connectedComponentIn (h ⁻¹' {c}) p
    ∃ A B : Set S2,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = Cᶜ ∧ frontier A = C ∧ frontier B = C ∧
      ∃ ε : Real, 0 < ε ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
        F.source = univ ×ˢ Ioo (-ε) ε ∧
        ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
        ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
        (∀ q t, t ∈ Ioo (-ε) ε -> h (F (q, t)) = c + t) ∧
        range (fun q : S1 => F (q, 0)) = C ∧
        F '' (univ ×ˢ Ioo (-ε) 0) ⊆ A ∧ F '' (univ ×ˢ Ioo 0 ε) ⊆ B := by
  obtain ⟨ε, hε, F, hsource, hF, hFi, hheight, hcenter⟩ :=
    exists_smooth_regular_level_component_tube hh hfinite c hc p hp
  obtain ⟨A, B, hA, hB, hAc, hBc, hdis, hcover, hfA, hfB, hneg, hpos⟩ :=
    exists_sphere_circle_collar_complementary_regions hε F hsource
  rw [hcenter] at hcover hfA hfB
  exact ⟨A, B, hA, hB, hAc, hBc, hdis, hcover, hfA, hfB,
    ε, hε, F, hsource, hF, hFi, hheight, hcenter, hneg, hpos⟩

end Poincare.Manifold.Schoenflies
