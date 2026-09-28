import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SphereModelCap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereNormalOrientation
import PoincareConjecture.Proofs.Horizon.Topology.Covering.SimplyConnected
import PoincareConjecture.Proofs.M76.Horizon.Dependencies.Topology.Covering.Universal.Proper








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finitePL_sphere_of_original_covering
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X} {T : Set E}
    (s : ChartwisePLSphere e S) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) (hT : IsConnected T)
    (π : T → S) (hπ : IsCoveringMap π)
    (p : E → E) (hp : FinitePiecewiseAffineOn p T)
    (hpval : ∀ x : T, p x = F (π x)) :
    ∃ P : T ≃ₜ S, (∀ x, P x = π x) ∧
      ∃ H : sphere (0 : V3) 1 ≃ₜ T, H.IsFinitePL ∧ H.symm.IsFinitePL ∧
        ∀ z, π (H z) = s.parametrization z := by
  let : ConnectedSpace T := isConnected_iff_connectedSpace.mp hT
  let : CompactSpace T := isCompact_iff_compactSpace.mp hp.isCompact
  let : SimplyConnectedSpace S := s.lifting_connectedness.1
  let : LocallyPathConnectedSpace S := s.lifting_connectedness.2
  have hbij := Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected hπ
  let P : T ≃ₜ S := (Equiv.ofBijective π hbij).toHomeomorphOfContinuousClosed
    hπ.continuous hπ.continuous.isClosedMap
  have hinj : InjOn p T := by
    intro x hx y hy he
    apply congrArg Subtype.val (hbij.1 (show π ⟨x,hx⟩ = π ⟨y,hy⟩ from ?_))
    apply Subtype.ext
    apply hFi (π ⟨x,hx⟩).property (π ⟨y,hy⟩).property
    exact (hpval ⟨x,hx⟩).symm.trans (he.trans (hpval ⟨y,hy⟩))
  obtain ⟨q0,hq0,hq0val⟩ := hp.exists_homeomorph_image hinj
  have himage : p '' T = F '' S := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨π ⟨x,hx⟩,(π ⟨x,hx⟩).property,(hpval ⟨x,hx⟩).symm⟩
    · rintro _ ⟨y,hy,rfl⟩
      obtain ⟨x,hx⟩ := hbij.2 ⟨y,hy⟩
      exact ⟨x,x.property,(hpval x).trans (congrArg (fun z : S => F z) hx)⟩
  let q := q0.trans (Homeomorph.setCongr himage)
  have hq : q.IsFinitePL := hq0.setCongr rfl himage
  have hqval (x : T) : (q x : E) = p x := hq0val x
  obtain ⟨b,hb,hbval⟩ := s.exists_finitePL_model_parametrization F hF hFi (N := F '' S) rfl
  let H := b.trans q.symm
  have hH : H.IsFinitePL := hb.trans hq.symm
  refine ⟨P,fun _ => rfl,H,hH,hH.symm,?_⟩
  intro z
  apply Subtype.ext
  apply hFi (π (H z)).property (s.parametrization z).property
  calc
    F (π (H z)) = (q (H z) : E) := (hqval (H z)).trans (hpval (H z)) |>.symm
    _ = (b z : E) := congrArg Subtype.val (q.apply_symm_apply (b z))
    _ = F (s.map z) := hbval z
    _ = F (s.parametrization z) := congrArg F (s.map_eq z)

theorem exists_finitePL_sphere_of_original_localHomeomorph
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X} {T : Set E}
    (s : ChartwisePLSphere e S) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) (hT : IsConnected T)
    (π : T → S) (hπ : IsLocalHomeomorph π)
    (p : E → E) (hp : FinitePiecewiseAffineOn p T)
    (hpval : ∀ x : T, p x = F (π x)) :
    ∃ P : T ≃ₜ S, (∀ x, P x = π x) ∧
      ∃ H : sphere (0 : V3) 1 ≃ₜ T, H.IsFinitePL ∧ H.symm.IsFinitePL ∧
        ∀ z, π (H z) = s.parametrization z := by
  let : CompactSpace T := isCompact_iff_compactSpace.mp hp.isCompact
  have hcover := Poincare.Topology.isCoveringMap_of_proper_localHomeomorph
    hπ hπ.continuous.isProperMap
  exact exists_finitePL_sphere_of_original_covering s F hF hFi hT π hcover p hp hpval

end PoincareConjecture.M76.PrismBelt
