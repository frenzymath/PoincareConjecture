import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalDiskLateralAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalDiskLateralOwner
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereAnnulusDisks

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "Annulus" => squareAnnulus 8 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_exterior_annulus_disks
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R H K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (B : Bool → Set X)
    (sB : ∀ b, ChartwisePLSphere e (B b))
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hdis : Disjoint (B false) (B true))
    (hR : R = H ∩ (interior K)ᶜ) (hK : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) (interior H)) :
    ∃ (owner : Bool) (g : P2 → V3) (k q : Bool → Set V3) (C : Bool → Set (V3 × ℝ)),
      (∀ d, P.map '' (Q ×ˢ J) ⊆ B d ↔ d = owner) ∧
      FinitePiecewiseAffineOn g Annulus ∧ MapsTo g Annulus Sphere ∧
      (sB owner).map '' (g '' Annulus) = P.map '' (Q ×ˢ J) ∧
      (∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
        k b ∩ (g '' Annulus) = q b ∧
        (sB owner).map '' q b = P.map '' (Q ×ˢ {if b then (1/2 : ℝ) else -(1/2)}) ∧
        ((sB owner).map '' k b) ∩ (P.map '' (Q ×ˢ J)) = (sB owner).map '' q b) ∧
      Disjoint ((sB owner).map '' k true) ((sB owner).map '' k false) ∧
      (((sB owner).map '' k true) ∪ ((sB owner).map '' k false)) ∪
        (P.map '' (Q ×ˢ J)) = B owner ∧
      ∀ b,
        let A := Sphere \ (k b \ q b)
        IsFinitePLBallPair P2 A (q b) ∧ k (!b) ∪ (g '' Annulus) = A ∧
        IsFinitePLBallPair P2 (C b) (q b ×ˢ {(1 : ℝ)}) ∧
        IsFinitePLBallPair P2 (k (!b) ×ˢ {(1 : ℝ)}) (q (!b) ×ˢ {(1 : ℝ)}) ∧
        IsFinitePLBallPair P3 (A ×ˢ I)
          (((g '' Annulus) ×ˢ {(1 : ℝ)}) ∪ (C b ∪ (k (!b) ×ˢ {(1 : ℝ)}))) ∧
        C b ∩ ((g '' Annulus) ×ˢ {(1 : ℝ)}) = q b ×ˢ {(1 : ℝ)} ∧
        (k (!b) ×ˢ {(1 : ℝ)}) ∩ ((g '' Annulus) ×ˢ {(1 : ℝ)}) =
          q (!b) ×ˢ {(1 : ℝ)} ∧
        Disjoint (k (!b) ×ˢ {(1 : ℝ)}) (C b) := by
  have hclosed (b : Bool) : IsClosed (B b) := by
    have hsource : IsCompact Sphere := isCompact_sphere (0 : V3) 1
    have himage : (sB b).map '' Sphere = B b := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩
        rw [(sB b).map_eq ⟨z,hz⟩]
        exact ((sB b).parametrization ⟨z,hz⟩).property
      · intro hx
        exact ⟨(sB b).parametrization.symm ⟨x,hx⟩,
          ((sB b).parametrization.symm ⟨x,hx⟩).property,
          ((sB b).map_eq _).trans
            (congrArg Subtype.val ((sB b).parametrization.apply_symm_apply _))⟩
    rw [← himage]
    exact (hsource.image_of_continuousOn (sB b).piecewiseAffine.continuousOn).isClosed
  obtain ⟨owner,howner,hunique,x,hx,hpole⟩ :=
    P.exists_unique_exterior_lateral_owner_and_pole B hclosed hdis hR hK hsmall
  obtain ⟨f,hf,hfi,hfimage,hfrim⟩ := P.exists_lateral_annulus
  have hfB : MapsTo f Annulus (B owner) := by
    intro z hz
    apply hunique owner |>.mpr rfl
    exact hfimage.subset (mem_image_of_mem f hz)
  have hpole' : P.map ((x : V2),(3/4 : ℝ)) ∉ f '' Annulus := by
    rwa [hfimage]
  obtain ⟨g,k,q,C,hg,hgS,_,hgimage,hk,hkd,hcover,hprod⟩ :=
    (sB owner).exists_original_annulus_disks hcompat f hf hfi hfB
      ⟨P.map ((x : V2),(3/4 : ℝ)),hx⟩ hpole'
  refine ⟨owner,g,k,q,C,hunique,hg,hgS,hgimage.trans hfimage,?_,hkd,?_,hprod⟩
  · intro b
    exact ⟨(hk b).1,(hk b).2.1,(hk b).2.2.1,
      (hk b).2.2.2.1.trans (hfrim b),by simpa only [hfimage] using (hk b).2.2.2.2⟩
  · simpa only [hfimage] using hcover

end PoincareConjecture.M76.OriginalDiskProduct
