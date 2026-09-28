import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.DiskCutBoundaryLabels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalComponentCutFrontier










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem cap_models_of_modeled_exterior_component
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (he : PLDomain e R) (hK : PLDomain e K)
    (hKR : K ⊆ interior R) (B : Bool → Set X)
    (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hfrontK : frontier K = B false ∪ B true)
    (owner : Bool) (hband : P.map '' (Rim ×ˢ J) ⊆ B owner)
    (ret : Bool → Set X) (hret : B owner \ P.openStrip = ret false ∪ ret true)
    (sN : ∀ b, ChartwisePLSphere e (ret b ∪ P.capDisk b))
    (hNdis : Disjoint (ret false ∪ P.capDisk false) (ret true ∪ P.capDisk true))
    (hopen : IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    (f : X → E) (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ connectedComponentIn (R ∩ (interior K)ᶜ) (a false),
      f x ∈ L.space ∧ g (f x) = x)
    (hmodel : HasPuncturedSphereModel e f
      (connectedComponentIn (R ∩ (interior K)ᶜ) (a false))) :
    Disjoint (connectedComponentIn P.cutCarrier (a false))
      (connectedComponentIn P.cutCarrier (a true)) ∧
      ∀ b, HasPuncturedSphereModel e f (connectedComponentIn P.cutCarrier (a b)) := by
  classical
  let C := connectedComponentIn (R ∩ (interior K)ᶜ) (a false)
  obtain ⟨hL, hLPL, _, _, _⟩ := he.interior_removal_geometry hR hK hKR
  have haL : a false ∈ R ∩ (interior K)ᶜ := by
    obtain ⟨z, hz, hzx⟩ := ha false
    exact hzx ▸ P.inside (cap_source_subset false hz)
  have hCc : IsCompact C := isCompact_connectedComponentIn_of_mem hL haL
  obtain ⟨n, S, sS, _, hSdis, hSfront⟩ :=
    hmodel.exists_boundary_spheres hCc.isClosed L g hg hgi hreal
  have hBL : B owner ⊆ R ∩ (interior K)ᶜ := by
    intro x hx
    have hxf : x ∈ frontier K := by
      rw [hfrontK]
      cases owner
      · exact Or.inl hx
      · exact Or.inr hx
    exact ⟨interior_subset (hKR (hK.closed.frontier_subset hxf)), hxf.2⟩
  have hBC : B owner ⊆ C := P.selected_sphere_subset_parent_component
    (sB owner).isConnected hBL hband (ha false)
  obtain ⟨i, hi, _, _⟩ := he.exists_selected_component_boundary_label_of_subset
    hR hK hKR B sB hBdis hfrontK owner hBC S sS hSdis hSfront
  obtain ⟨G, hGmap, _, hGopenEq, _, hGcap, hGc, hGPL, hGo, _, hGcutPL, _⟩ :=
    P.exists_component_product hL hLPL hopen hPL (ha false) (ha true)
  have hGcut : G.cutCarrier = C ∩ P.cutCarrier := by
    change C \ G.openStrip = C ∩ P.cutCarrier
    rw [hGopenEq]
    ext x
    exact ⟨fun hx => ⟨hx.1, ⟨connectedComponentIn_subset _ _ hx.1, hx.2⟩⟩,
      fun hx => ⟨hx.1, hx.2.2⟩⟩
  have hGb : G.map '' (Rim ×ˢ J) ⊆ S i := by
    rw [hGmap, hi]
    exact hband
  have hGr : S i \ G.openStrip = ret false ∪ ret true := by
    rw [hi, hGopenEq]
    exact hret
  have hGdis : Disjoint (ret false ∪ G.capDisk false) (ret true ∪ G.capDisk true) := by
    simpa only [hGcap] using hNdis
  obtain ⟨_, hTdis, hTf⟩ := G.replacement_boundary_labels S hSdis hSfront i
    hGb ret hGr hGdis (G.cut_geometry hGc hGo).2.2.1
  let T : {j : Fin n // j ≠ i} ⊕ Bool → Set X :=
    Sum.elim (fun j => S j) (fun b => ret b ∪ G.capDisk b)
  let sT : ∀ j, ChartwisePLSphere e (T j) := fun j => by
    cases j with
    | inl j => exact sS j
    | inr b =>
      change ChartwisePLSphere e (ret b ∪ G.capDisk b)
      rw [hGcap]
      exact sN b
  have hCC : connectedComponentIn C (a false) = C :=
    isPreconnected_connectedComponentIn.connectedComponentIn (mem_connectedComponentIn haL)
  have hmG : HasPuncturedSphereModel e f (connectedComponentIn C (a false)) := by
    rw [hCC]
    exact hmodel
  have hGa (b : Bool) : a b ∈ G.capDisk b := (hGcap b).symm ▸ ha b
  have hmodels := hmG.cap_components G hGc hGo hGcutPL a hGa T sT hTdis hTf
  have hcomp := (P.component_cut_frontier hL hLPL hopen hPL a ha).2.2.2
  change ∀ b, connectedComponentIn (C ∩ P.cutCarrier) (a b) =
    connectedComponentIn P.cutCarrier (a b) at hcomp
  simpa only [hGcut, hcomp] using hmodels

end PoincareConjecture.M76.OriginalDiskProduct
