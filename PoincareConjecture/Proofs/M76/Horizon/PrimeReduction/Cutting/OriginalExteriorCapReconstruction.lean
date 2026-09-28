import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalExteriorCapRemainders
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalTwoCapModelReconstruction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ModeledExteriorDiskCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExteriorCapSpheres

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem punctured_model_iff_disjoint_exterior_cap_models
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (he : PLDomain e R) (hK : PLDomain e K)
    (hKR : K ⊆ interior R) (B : Bool → Set X)
    (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hfrontK : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (owner : Bool) (k q : Bool → Set V3)
    (howner : ∀ d, P.map '' (Rim ×ˢ J) ⊆ B d ↔ d = owner)
    (hk : ∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
      (sB owner).map '' q b = P.capRimSet b ∧
      ((sB owner).map '' k b) ∩ (P.map '' (Rim ×ˢ J)) = (sB owner).map '' q b)
    (hcomp : ∀ b, IsFinitePLBallPair P2 (Sphere \ (k b \ q b)) (q b))
    (hkdis : Disjoint ((sB owner).map '' k true) ((sB owner).map '' k false))
    (hcover : (((sB owner).map '' k true) ∪ ((sB owner).map '' k false)) ∪
      (P.map '' (Rim ×ˢ J)) = B owner)
    (hopen : IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    (f : X → E) (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ connectedComponentIn (R ∩ (interior K)ᶜ) (a false),
      f x ∈ L.space ∧ g (f x) = x) :
    HasPuncturedSphereModel e f (connectedComponentIn (R ∩ (interior K)ᶜ) (a false)) ↔
      Disjoint (connectedComponentIn P.cutCarrier (a false))
        (connectedComponentIn P.cutCarrier (a true)) ∧
      ∀ b, HasPuncturedSphereModel e f (connectedComponentIn P.cutCarrier (a b)) := by
  have hband : P.map '' (Rim ×ˢ J) ⊆ B owner := (howner owner).mpr rfl
  let ret := fun b => (sB owner).map '' k b
  obtain ⟨_, _, hretain, _, _, hnewdis, _, _⟩ :=
    P.three_connected_ports_of_retained_disks hR he hK hKR B sB hBdis hfrontK
      hsmall hstripK owner k q howner hk hcomp hkdis hcover
  obtain ⟨sN, _⟩ := P.exists_original_exterior_retained_caps B sB he.compatible
    hK.closed hfrontK hstripK owner hband k q
    (fun b => ⟨(hk b).1, (hk b).2.1, hcomp b, (hk b).2.2.1⟩)
  have hsN (b : Bool) : ChartwisePLSphere e (ret b ∪ P.capDisk b) := sN b
  constructor
  · intro hm
    exact P.cap_models_of_modeled_exterior_component hR he hK hKR B sB hBdis hfrontK
      owner hband ret hretain hsN hnewdis hopen hPL a ha f L g hg hgi hreal hm
  · rintro ⟨hdis, hm⟩
    obtain ⟨hretc, hretconn, hretstrip, hretout, hTc, hNT, hDf⟩ :=
      P.exterior_cap_component_remainders hR he hK hKR B sB hBdis hfrontK
        hsmall hstripK owner k q howner hk hcomp hkdis hcover hopen hPL a ha hdis
    obtain ⟨hLc, hLPL, _, _, _⟩ := he.interior_removal_geometry hR hK hKR
    exact P.parent_model_of_two_cap_models hLc hLPL hopen hPL a ha hdis ret
      (fun b => connectedComponentIn P.cutCarrier (a b) ∩ (B (!owner) ∪ frontier R))
      hretc hretconn hretstrip hretout hTc hNT hDf f L g hg hgi hreal hm

end PoincareConjecture.M76.OriginalDiskProduct
