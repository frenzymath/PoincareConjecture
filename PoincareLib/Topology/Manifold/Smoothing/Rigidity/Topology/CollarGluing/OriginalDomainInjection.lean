import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.CollarGluing.OriginalDomainCover
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Gluing.OpenCoverInjection

/-! # Injection of the original closed sides into the ambient manifold -/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

namespace OpenFrontierCollapse

variable {X : Type*} [TopologicalSpace X] {R : Set X}

private theorem inclusion_injective_congr {A B T : Set X}
    (hAB : A = B) (hAT : A ⊆ T) (hBT : B ⊆ T)
    (h : ∀ x : B, Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion hBT) x)) :
    ∀ x : A, Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion hAT) x) := by
  subst B
  exact h

/-- The actual open cover transfers full-frontier injection on both closed
sides to injection of either closed side into the whole ambient space. -/
theorem side_ambient_injective (C : OpenFrontierCollapse R) (_hR : IsClosed R)
    (hpi : ∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X)),
      ∃ hFT : frontier R ⊆ T, ∀ x : frontier R,
        Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hFT) x)) :
    ∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X)), ∀ x : T,
      Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x) := by
  obtain ⟨hFP, hpiP⟩ := hpi R (Or.inl rfl)
  obtain ⟨hFN, hpiN⟩ := hpi (interior R)ᶜ (Or.inr rfl)
  have hWP := C.overlap_inclusion_injective C.positive_eq hFP C.motion_positive hpiP
  have hWN := C.overlap_inclusion_injective C.negative_eq hFN C.motion_negative hpiN
  have hIP : ∀ x : (C.positive ∩ C.negative : Set X),
      Function.Injective (FundamentalGroup.map
        (ContinuousMap.inclusion inter_subset_left) x) := by
    exact inclusion_injective_congr C.inter_eq _ _ hWP
  have hIN : ∀ x : (C.positive ∩ C.negative : Set X),
      Function.Injective (FundamentalGroup.map
        (ContinuousMap.inclusion inter_subset_right) x) := by
    exact inclusion_injective_congr C.inter_eq _ _ hWN
  have hPA := IncompressibleGluing.inclusion_injective_of_overlap_injective
    C.positive C.negative C.positive_open C.negative_open C.cover hIP hIN
  have hNP : ∀ x : (C.negative ∩ C.positive : Set X),
      Function.Injective (FundamentalGroup.map
        (ContinuousMap.inclusion inter_subset_left) x) := by
    exact inclusion_injective_congr (inter_comm _ _) _ _ hIN
  have hNN : ∀ x : (C.negative ∩ C.positive : Set X),
      Function.Injective (FundamentalGroup.map
        (ContinuousMap.inclusion inter_subset_right) x) := by
    exact inclusion_injective_congr (inter_comm _ _) _ _ hIP
  have hNA := IncompressibleGluing.inclusion_injective_of_overlap_injective
    C.negative C.positive C.negative_open C.positive_open
      (by rw [union_comm]; exact C.cover) hNP hNN
  intro T hT x
  rcases hT with rfl | rfl
  · have hSP := C.side_inclusion_injective C.positive_eq hFP C.motion_positive x
    intro a b hab
    apply hSP
    apply hPA (ContinuousMap.inclusion C.positive_subset x)
    rw [← FundamentalGroup.map_comp_apply, ← FundamentalGroup.map_comp_apply]
    exact hab
  · have hSN := C.side_inclusion_injective C.negative_eq hFN C.motion_negative x
    intro a b hab
    apply hSN
    apply hNA (ContinuousMap.inclusion C.negative_subset x)
    rw [← FundamentalGroup.map_comp_apply, ← FundamentalGroup.map_comp_apply]
    exact hab

end OpenFrontierCollapse

/-- A compact original PL domain with compact exterior and nonempty
interiors has both closed sides injective in the ambient space whenever
its entire frontier injects into both sides. The finite bicollar, open cover
and collapse are all constructed from the original PL domain. -/
theorem PLDomain.closed_sides_ambient_injective
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hminus : IsCompact (interior R)ᶜ)
    (hne : (interior R).Nonempty) (hneminus : (interior (interior R)ᶜ).Nonempty)
    (hpi : ∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X)),
      ∃ hFT : frontier R ⊆ T, ∀ x : frontier R,
        Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hFT) x)) :
    ∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X)), ∀ x : T,
      Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x) := by
  obtain ⟨C⟩ := he.nonempty_openFrontierCollapse hR hminus hne hneminus
  exact C.side_ambient_injective he.closed hpi

end PoincareMT.M76
