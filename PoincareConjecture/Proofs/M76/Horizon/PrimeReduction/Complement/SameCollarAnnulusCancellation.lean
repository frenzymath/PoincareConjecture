import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalAnnulusDoubleProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereProductFrontier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExteriorAnnulusDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalCollarSphereCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage









set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel PLAnnularStrip

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_same_collar_strip_product_of_marked_caps
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R N K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hN : IsCompact N) (he : PLDomain e N)
    (hPN : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) N) (hKN : K ⊆ N)
    (F : V3 × ℝ → X) (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I)) (hFK : F '' (Sphere ×ˢ I) = K)
    {A band : Set V3} (hAS : A ⊆ Sphere) (hbandA : band ⊆ A)
    (hband : F '' (band ×ˢ {(1 : ℝ)}) = P.map '' (Rim ×ˢ J))
    (hstrip : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (C : Bool → Set (V3 × ℝ)) (q : Bool → Set V3)
    (hball : IsFinitePLBallPair P3 (A ×ˢ I)
      ((band ×ˢ {(1 : ℝ)}) ∪ (C false ∪ C true)))
    (hC : ∀ s, IsFinitePLBallPair P2 (C s) (q s ×ˢ {(1 : ℝ)}))
    (hmeet : ∀ s, C s ∩ (band ×ˢ {(1 : ℝ)}) = q s ×ˢ {(1 : ℝ)})
    (hdis : Disjoint (C true) (C false))
    (hrim : ∀ s, F '' (q s ×ˢ {(1 : ℝ)}) =
      P.map '' (Rim ×ˢ {if s then (1/2 : ℝ) else -(1/2)})) :
    ∃ (H : ((F '' (A ×ˢ I)) ∪ P.closedStrip : Set X) ≃ₜ
        (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)))
      (σ : P3 × ℝ → X),
      PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) ∧
      (∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (H.symm z : X)) ∧
      (∀ s (x : ((F '' (A ×ˢ I)) ∪ P.closedStrip : Set X)),
        (x : X) ∈ (F '' C s) ∪
          (P.map '' (Disk ×ˢ {if s then (1/2 : ℝ) else -(1/2)})) ↔
          (H x : P3 × ℝ).2 = if s then (1 : ℝ) else 0) ∧
      frontier ((F '' (A ×ˢ I)) ∪ P.closedStrip) =
        ((F '' C false) ∪ (P.map '' (Disk ×ˢ {-(1/2 : ℝ)}))) ∪
        ((F '' C true) ∪ (P.map '' (Disk ×ˢ {(1/2 : ℝ)}))) := by
  have hAI : A ×ˢ I ⊆ Sphere ×ˢ I := prod_mono hAS subset_rfl
  have hCI (s : Bool) : C s ⊆ A ×ˢ I := by
    apply subset_trans _ hball.1
    cases s
    · exact subset_union_left.trans subset_union_right
    · exact subset_union_right.trans subset_union_right
  have hbandI : band ×ˢ {(1 : ℝ)} ⊆ A ×ˢ I :=
    prod_mono hbandA (by intro t ht; rw [show t=1 from ht]; norm_num)
  obtain ⟨b⟩ := exists_chartwisePLBall_image hball
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) : P3 ≃L[ℝ] V3)
    hF hAI hFi
  have hbdy : F '' ((band ×ˢ {(1 : ℝ)}) ∪ (C false ∪ C true)) =
      (P.map '' (Rim ×ˢ J)) ∪ ((F '' C false) ∪ (F '' C true)) := by
    rw [image_union,image_union,hband]
  let b' : ChartwisePLBall e (F '' (A ×ˢ I))
      ((P.map '' (Rim ×ˢ J)) ∪ ((F '' C false) ∪ (F '' C true))) := hbdy ▸ b
  have hBK : F '' (A ×ˢ I) ⊆ K := (image_mono hAI).trans hFK.subset
  have hcontact : (F '' (A ×ˢ I)) ∩ P.closedStrip = P.map '' (Rim ×ˢ J) := by
    apply Subset.antisymm
    · exact fun x hx => hstrip.subset ⟨hx.2,hBK hx.1⟩
    · intro x hx
      exact ⟨image_mono hbandI (hband.symm.subset hx),(hstrip.symm.subset hx).1⟩
  have hphysicalmeet (s : Bool) : (F '' C s) ∩ (P.map '' (Rim ×ˢ J)) =
      P.map '' (Rim ×ˢ {if s then (1/2 : ℝ) else -(1/2)}) := by
    rw [←hband,←image_inter_on
      (fun _ hx _ hy hxy => hFi (hAI (hbandI hx)) (hAI (hCI s hy)) hxy),
      hmeet s,hrim s]
  have hphysicaldis : Disjoint (F '' C true) (F '' C false) := by
    apply disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv := hFi (hAI (hCI true hu)) (hAI (hCI false hv)) (hux.trans hvx.symm)
    exact disjoint_left.mp hdis hu (huv.symm ▸ hv)
  obtain ⟨H,σ,hσ,hσval,hmark⟩ := P.exists_original_annulus_double_product hN he hPN (hBK.trans hKN)
    F hF hFi C (fun s => q s ×ˢ {(1 : ℝ)}) hC
    (fun s => (hCI s).trans hAI) b' hrim hphysicalmeet hphysicaldis hcontact
  refine ⟨H,σ,hσ,hσval,hmark,?_⟩
  let ends : Bool → Set X := fun s => (F '' C s) ∪
    (P.map '' (Disk ×ˢ {if s then (1/2 : ℝ) else -(1/2)}))
  have hends (s : Bool) : ends s ⊆ (F '' (A ×ˢ I)) ∪ P.closedStrip := by
    apply union_subset
    · exact (image_mono (hCI s)).trans subset_union_left
    · apply subset_trans _ subset_union_right
      apply image_mono
      intro z hz
      refine ⟨hz.1,?_⟩
      rw [show z.2 = if s then (1/2 : ℝ) else -(1/2) from hz.2]
      cases s <;> norm_num
  exact (original_marked_sphere_product_frontier H σ hσ hσval ends hends hmark).2

end PoincareConjecture.M76.OriginalDiskProduct
