import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RealizationTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.PLDomainAmbientTransport
import PoincareConjecture.Proofs.M76.PrimeReduction.SphereAmbientTransport









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.transport_relative_cut
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R Q : Set X}
    (S O : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i))
    (hQeq : Q = R \ ⋃ i, O i) (hQ : IsCompact Q) (hQPL : PLDomain e Q)
    (hO : ∀ i, IsOpen (O i)) (hCR : ∀ i, closure (O i) ⊆ interior R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hopen : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC : ∀ i, S i ⊆ closure (O i))
    (B : κ × Bool → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hBsub : ∀ i, B i ⊆ closure (O i.1))
    (hfront : frontier Q = frontier R ∪ ⋃ i, B i)
    (hno : HasNoPuncturedSphereComponents e f Q)
    (F : X ≃ₜ X) (hfix : EqOn F id (interior R)ᶜ)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x) :
    ∃ (sS' : ∀ i, ChartwisePLSphere e (F '' S i))
      (sB' : ∀ i, ChartwisePLSphere e (F '' B i))
      (W' : ∀ i, ((F '' S i) × unitInterval) ≃ₜ closure (F '' O i)),
      F '' R = R ∧ EqOn F id (frontier R) ∧
      F '' Q = R \ ⋃ i, F '' O i ∧ IsCompact (F '' Q) ∧ PLDomain e (F '' Q) ∧
      (∀ i, IsOpen (F '' O i)) ∧ (∀ i, closure (F '' O i) ⊆ interior R) ∧
      Pairwise (fun i j => Disjoint (closure (F '' O i)) (closure (F '' O j))) ∧
      (∀ i z, (W' i z : X) = F (W i ((F.image (S i)).symm z.1,z.2))) ∧
      (∀ i z, (W' i z : X) ∈ F '' O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ i z, (W' i z : X) ∈ F '' S i ↔ (z.2 : ℝ) = 1/2) ∧
      (∀ i, F '' S i ⊆ closure (F '' O i)) ∧
      Pairwise (fun i j => Disjoint (F '' B i) (F '' B j)) ∧
      (∀ i, F '' B i ⊆ closure (F '' O i.1)) ∧
      frontier (F '' Q) = frontier R ∪ ⋃ i, F '' B i ∧
      HasNoPuncturedSphereComponents e f (F '' Q) := by
  classical
  have hFR : F '' R = R := by
    apply Subset.antisymm
    · rintro x ⟨y,hy,rfl⟩
      by_contra hn
      have hh := hfix (fun hi => hn (interior_subset hi))
      exact hn ((F.injective hh).symm ▸ hy)
    · intro x hx
      refine ⟨F.symm x,?_,F.apply_symm_apply x⟩
      by_contra hn
      have hh := hfix (fun hi => hn (interior_subset hi))
      have heq : F.symm x = x := hh.symm.trans (F.apply_symm_apply x)
      exact hn (heq.symm ▸ hx)
  have hFi : F '' interior R = interior R := by rw [F.image_interior,hFR]
  have hFfront : F '' frontier R = frontier R := by rw [F.image_frontier,hFR]
  let W' (i) : ((F '' S i) × unitInterval) ≃ₜ closure (F '' O i) :=
    ((F.image (S i)).symm.prodCongr (Homeomorph.refl unitInterval)).trans
      ((W i).trans ((F.image (closure (O i))).trans (Homeomorph.setCongr (F.image_closure _))))
  have hWval (i) (z) : (W' i z : X) = F (W i ((F.image (S i)).symm z.1,z.2)) := rfl
  have hQimage : F '' Q = R \ ⋃ i, F '' O i := by
    rw [hQeq,image_sdiff F.injective,image_iUnion,hFR]
  refine ⟨fun i => Classical.choice ((sS i).nonempty_image F hQPL.cover hF),
    fun i => Classical.choice ((sB i).nonempty_image F hQPL.cover hF),W',hFR,
    (fun x hx => hfix hx.2),hQimage,hQ.image F.continuous,
    hQPL.image_of_original_atlas_move F hF,
    fun i => F.isOpenMap _ (hO i),?_,?_,hWval,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [←F.image_closure,←hFi]
    exact image_mono (hCR i)
  · intro i j hij
    rw [←F.image_closure,←F.image_closure]
    exact (hdis hij).image F.injective.injOn (subset_univ _) (subset_univ _)
  · intro i z
    rw [hWval,F.injective.mem_set_image]
    exact hopen i _
  · intro i z
    rw [hWval,F.injective.mem_set_image]
    exact hcenter i _
  · intro i
    rw [←F.image_closure]
    exact image_mono (hSC i)
  · intro i j hij
    exact (hBdis hij).image F.injective.injOn (subset_univ _) (subset_univ _)
  · intro i
    rw [←F.image_closure]
    exact image_mono (hBsub i)
  · rw [←F.image_frontier,hfront,image_union,image_iUnion,hFfront]
  · exact hno.image_of_supported_original_move F hQPL.cover hf hF
      (hQeq.subset.trans inter_subset_left) interior_subset hfix L g hg hgi hreal

end PoincareConjecture.M76
