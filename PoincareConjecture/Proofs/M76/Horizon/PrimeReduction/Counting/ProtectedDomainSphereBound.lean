import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalRelativeSphereBound
import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedPureDomainModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalChartStarFaceCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3ChangeRealization

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

theorem exists_protected_domain_sphere_bound
    {X : Type u} {ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (hRPL : PLDomain e R) (hDR : D ⊆ R)
    (b : ChartwisePLBall e D (frontier D)) (hRc : IsConnected R) :
    ∃ N : ℕ, ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] (κ : Type u) [Fintype κ] (f : X → E),
      (∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target) → InjOn f R →
      ∀ (S : κ → Set X), (∀ i, ChartwisePLSphere e (S i)) →
      (∀ i, S i ⊆ interior R) → Pairwise (fun i j => Disjoint (S i) (S j)) →
      ∀ (O : κ → Set X) (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i)),
      IsCompact (R \ ⋃ i, O i) → PLDomain e (R \ ⋃ i, O i) →
      (∀ i, IsOpen (O i)) → (∀ i, closure (O i) ⊆ interior R) →
      Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) →
      (∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) →
      (∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2) →
      (∀ i, S i ⊆ closure (O i)) →
      ∀ (B : κ × Bool → Set X), (∀ j, ChartwisePLSphere e (B j)) →
      Pairwise (fun j k => Disjoint (B j) (B k)) →
      (∀ j, B j ⊆ closure (O j.1)) →
      frontier (R \ ⋃ i, O i) = frontier R ∪ ⋃ j, B j →
      HasNoPuncturedSphereComponents e f (R \ ⋃ i, O i) →
      Fintype.card κ + 1 ≤ N := by
  classical
  obtain ⟨v, phi, K, J, H, g, _, hphi, hK, hJ, hKs, hBs, _, _, hH, _, hg,
      hgPL, hpure, hstars⟩ := exists_protected_pure_domain_model hR hRPL hDR b
  have hgi : InjOn (fun z => (g z : X)) K.space := by
    intro x hx y hy hxy
    have hEq : H.symm ⟨x,hx⟩ = H.symm ⟨y,hy⟩ :=
      Subtype.ext ((hg ⟨x,hx⟩).symm.trans (hxy.trans (hg ⟨y,hy⟩)))
    exact congrArg Subtype.val (H.symm.injective hEq)
  have hmark (z : v → ℝ × V3) (hz : z ∈ K.space) :
      (g z : X) ∈ frontier R ↔ z ∈ (J 0).space := by
    rw [hBs]
    exact original_model_mem_image_iff H phi g hH hg hRPL.closed.frontier_subset ⟨z,hz⟩
  have hstar' : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (B ∘ (fun z => (g z : X))) := by
    intro p hp
    obtain ⟨B,hmap,hcompat,hface,_⟩ := hstars p hp
    exact ⟨B,hmap,hcompat,hface⟩
  obtain ⟨Q,A,hQ,hmap,hA⟩ := exists_original_chart_star_face_coordinates K
    (fun z => (g z : X)) hstar'
  have hreal (x : X) (hx : x ∈ R) :
      phi x ∈ K.space ∧ (g (phi x) : X) = x := by
    have hp : phi x ∈ K.space := hKs.symm.subset ⟨x,hx,rfl⟩
    refine ⟨hp,?_⟩
    have hHx : H ⟨x,hx⟩ = ⟨phi x,hp⟩ := Subtype.ext (hH ⟨x,hx⟩)
    rw [hg ⟨phi x,hp⟩,←hHx,H.symm_apply_apply]
  refine ⟨Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology R 1) +
    4 * Nat.card (K.FaceOfCard 3) + (J 0).vertices.ncard, ?_⟩
  intro E _ _ _ κ _ f hf hfi S sS hSR hdis O W hCut hCutPL hO hCR hCC
    hopen hcenter hSC B sB hBdis hBsub hfront hno
  have hnoPhi := hno.change_original_realization hf hfi inter_subset_left K
    (fun z => (g z : X)) hgPL phi hreal
  exact hnoPhi.card_le_original_model_bound K hK (fun z => (g z : X)) hgPL hgi
    Q hQ A hmap hA hR hRPL
    (by rintro _ ⟨z,_,rfl⟩; exact (g z).property) hphi hreal S sS hSR hdis
    O W hCut hCutPL hO hCR hCC hopen hcenter hSC B sB hBdis hBsub hfront
    (J 0) (hJ 0).1 hpure hmark hRc hstar'

end PoincareConjecture.M76
