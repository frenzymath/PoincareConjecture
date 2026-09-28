import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RetainedCollarProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem not_hasPuncturedSphereModel_of_retained_collar_self_attachment
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R K B B₀ : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (hK : IsClosed K) (hKR : K ⊆ R)
    (hfrontK : frontier K = B₀ ∪ B)
    (hopen : IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier)
    (s : ChartwisePLSphere e B) (F : V3 × ℝ → X)
    (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I)) (hFK : F '' (Sphere ×ˢ I) = K)
    (htop : ∀ z ∈ Sphere, F (z, 1) = s.map z)
    (hbottom : F '' (Sphere ×ˢ {(0 : ℝ)}) = B₀)
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hband : P.map '' (Rim ×ˢ J) ⊆ B)
    {k q : Set V3} (hk : IsFinitePLBallPair P2 k q) (hkS : k ⊆ Sphere)
    (hcontact : (s.map '' k) ∩ (P.map '' (Rim ×ˢ J)) = s.map '' q)
    (b : Bool) (hrim : s.map '' q = P.capRimSet b)
    {a₀ a₁ : X} (ha₀ : a₀ ∈ F '' (k ×ˢ {(0 : ℝ)}))
    (ha₁ : a₁ ∈ F '' (k ×ˢ {(1 : ℝ)}))
    (hsame : a₁ ∈ connectedComponentIn P.cutCarrier a₀) :
    connectedComponentIn (P.cutCarrier ∪ F '' (k ×ˢ I)) a₀ =
      connectedComponentIn P.cutCarrier a₀ ∪ F '' (k ×ˢ I) ∧
      ¬ HasPuncturedSphereModel e f
        (connectedComponentIn (P.cutCarrier ∪ F '' (k ×ˢ I)) a₀) := by
  classical
  let H := F '' (k ×ˢ I)
  let p : Bool → Set X := fun d => F '' (k ×ˢ {if d then (1 : ℝ) else 0})
  obtain ⟨G, _, hGattach, hGends, hattach⟩ := P.exists_retained_collar_product
    hK hKR hfrontK s F hF hFi hFK htop hbottom hstripK hband hk hkS hcontact b hrim
  have hQ := (P.cut_geometry (hR.inter_right isOpen_interior.isClosed_compl) hopen).1
  have hH : IsCompact H := (hk.isCompact.prod isCompact_Icc).image_of_continuousOn
    (hF.continuousOn.mono (prod_mono hkS subset_rfl))
  have hHconn : IsConnected H := (hk.isConnected.prod
    (isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num))).image _
    (hF.continuousOn.mono (prod_mono hkS subset_rfl))
  have hp (d : Bool) : IsConnected (p d) := by
    apply (hk.isConnected.prod (isConnected_singleton (x := if d then (1 : ℝ) else 0))).image
    apply hF.continuousOn.mono
    apply prod_mono hkS
    intro t ht
    rw [show t = (if d then (1 : ℝ) else 0) from ht]
    cases d <;> norm_num
  let : LocallyPathConnectedSpace P.cutCarrier := hPL.locallyPathConnectedSpace
  have haQ : a₀ ∈ P.cutCarrier := (hattach.symm.subset (Or.inl ha₀)).1
  have hcomp := (Topology.componentIn_closed_attachment_of_two_connected_ports
    hQ.isClosed hH.isClosed hHconn (hp false) (hp true) hattach ha₀ ha₁).1
  rw [← connectedComponentIn_eq hsame,union_self] at hcomp
  refine ⟨hcomp, ?_⟩
  rintro ⟨_, n, A, r, M, U, V, hA, hAdis, _, _, _⟩
  have hcomponentClosed : IsClosed (connectedComponentIn P.cutCarrier a₀) :=
    (isCompact_connectedComponentIn_of_mem hQ haQ).isClosed
  have hcomponentPath : IsPathConnected (connectedComponentIn P.cutCarrier a₀) := by
    rw [connectedComponentIn_eq_image haQ,← pathComponent_eq_connectedComponent]
    exact isPathConnected_pathComponent.image continuous_subtype_val
  have hpQ (d : Bool) : p d ⊆ P.cutCarrier := by
    intro x hx
    apply (hattach.symm.subset ?_).1
    cases d
    · exact Or.inl hx
    · exact Or.inr hx
  have hpcomp : p false ∪ p true ⊆ connectedComponentIn P.cutCarrier a₀ := by
    apply union_subset ((hp false).isPreconnected.subset_connectedComponentIn ha₀ (hpQ false))
    rw [connectedComponentIn_eq hsame]
    exact (hp true).isPreconnected.subset_connectedComponentIn ha₁ (hpQ true)
  have hends (z : k × unitInterval) :
      (G z : X) ∈ connectedComponentIn P.cutCarrier a₀ ↔ z.2 = 0 ∨ z.2 = 1 := by
    constructor
    · intro hz
      exact (hGattach z).mp (connectedComponentIn_subset _ _ hz)
    · intro hz
      apply hpcomp
      rcases hz with hz | hz
      · exact Or.inl ((hGends false z).mpr hz)
      · exact Or.inr ((hGends true z).mpr hz)
  let : Nonempty k := hk.isConnected.nonempty.to_subtype
  have hno := Poincare.Topology.not_nonempty_homeomorph_punctured_sphere_of_product_handle
    hcomponentClosed hH.isClosed hcomponentPath G hends
    A r (fun i => (hA i).1) (fun i => (hA i).2.1) hAdis (fun i => (hA i).2.2)
  exact hno ⟨(Homeomorph.setCongr hcomp.symm).trans (U.trans V)⟩

end PoincareConjecture.M76.OriginalDiskProduct
