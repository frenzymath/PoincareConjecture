import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ThreeComponentReattachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RetainedCollarComponentModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RetainedCollarSelfAttachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalExteriorCapReconstruction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskThreePorts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CommonCutComponentDomains
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExteriorCapSpheres
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

set_option maxHeartbeats 1800000 in
theorem exists_same_collar_exchange_without_punctured_components
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) j)
    (hR : IsCompact R) (hRc : IsConnected R) (he : PLDomain e R)
    (hK : PLDomain e K) (hKc : IsConnected K) (hKR : K ⊆ interior R)
    (B : Bool → Set X) (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hfrontK : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hDPL : PLDomain e (K ∪ P.closedStrip))
    (hDfront : frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks)
    (hopen : IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' P.openStrip))
    (owner : Bool) (k q : Bool → Set V3)
    (howner : ∀ d, P.map '' (Rim ×ˢ J) ⊆ B d ↔ d = owner)
    (hk : ∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
      (sB owner).map '' q b = P.capRimSet b ∧
      ((sB owner).map '' k b) ∩ (P.map '' (Rim ×ˢ J)) = (sB owner).map '' q b)
    (hcomp : ∀ b, IsFinitePLBallPair P2 (Sphere \ (k b \ q b)) (q b))
    (hkdis : Disjoint ((sB owner).map '' k true) ((sB owner).map '' k false))
    (hcover : (((sB owner).map '' k true) ∪ ((sB owner).map '' k false)) ∪
      (P.map '' (Rim ×ˢ J)) = B owner)
    (F : V3 × ℝ → X) (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I)) (hFK : F '' (Sphere ×ˢ I) = K)
    (htop : ∀ z ∈ Sphere, F (z, 1) = (sB owner).map z)
    (hbottom : F '' (Sphere ×ˢ {(0 : ℝ)}) = B (!owner))
    (hproducts : ∀ b, ∃ (N : Set X)
      (W : ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip : Set X) ≃ₜ
        (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X),
      PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) ∧
      (∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (W.symm z : X)) ∧
      (∀ x : ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip : Set X),
        (x : X) ∈ N ↔ (W x : P3 × ℝ).2 = if b then (1 : ℝ) else 0) ∧
      (∀ x : ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip : Set X),
        (x : X) ∈ ((sB owner).map '' k (!b)) ∪ P.capDisk (!b) ↔
          (W x : P3 × ℝ).2 = if !b then (1 : ℝ) else 0) ∧
      frontier ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip) =
        N ∪ (((sB owner).map '' k (!b)) ∪ P.capDisk (!b)))
    (f : X → E) (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (hno : ∀ x ∈ R ∩ (interior K)ᶜ,
      ¬ HasPuncturedSphereModel e f (connectedComponentIn (R ∩ (interior K)ᶜ) x)) :
    ∃ b, ∀ x ∈ P.cutCarrier ∪ F '' (k b ×ˢ I),
      ¬ HasPuncturedSphereModel e f
        (connectedComponentIn (P.cutCarrier ∪ F '' (k b ×ˢ I)) x) := by
  classical
  obtain ⟨_, hQeq', hQ, hQPL, hQR, hQD, _, hOldEq, hOldContact⟩ :=
    P.global_common_cut_geometry hR he hDPL hKR rfl hsmall hDfront
  have hQeq : P.cutCarrier = R ∩ (interior (K ∪ P.closedStrip))ᶜ := hQeq'.symm
  rw [← hQeq] at hQ hQPL hQR hQD hOldEq hOldContact
  let : LocallyPathConnectedSpace P.cutCarrier := hQPL.locallyPathConnectedSpace
  have hband := (howner owner).mpr rfl
  obtain ⟨_, _, _, _, hportConn, _, _, hKcut⟩ :=
    P.three_connected_ports_of_retained_disks hR he hK hKR B sB hBdis hfrontK
      hsmall hstripK owner k q howner hk hcomp hkdis hcover
  let port := fun b => ((sB owner).map '' k b) ∪ P.capDisk b
  let p : Fin 3 → Set X := ![B (!owner), port false, port true]
  have hpconn (i : Fin 3) : IsConnected (p i) := by
    fin_cases i
    · exact (sB (!owner)).isConnected
    · exact hportConn false
    · exact hportConn true
  have hunion : (B (!owner) ∪ port false) ∪ port true = ⋃ i, p i := by
    ext x
    simp only [p, Fin.exists_fin_succ, mem_iUnion,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.exists_fin_zero,
      or_false, mem_union]
    tauto
  have hQports : P.cutCarrier ∩ (K ∪ P.closedStrip) = ⋃ i, p i :=
    hQD.trans (hKcut.trans hunion)
  have hstripconn : IsConnected P.closedStrip := by
    apply ((isConnected_closedBall (x := (0 : V2)) zero_le_one).prod
      (isConnected_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2))).image P.map
    apply P.polyhedral.continuousOn.mono
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hmeet : (K ∩ P.closedStrip).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_sphere (by simp) (0 : V2) zero_le_one).nonempty
    have hx : P.map (z, 0) ∈ P.map '' (Rim ×ˢ J) := ⟨(z, 0), ⟨hz, by norm_num⟩, rfl⟩
    exact ⟨_, (hstripK.symm.subset hx).2, (hstripK.symm.subset hx).1⟩
  obtain ⟨w, D, hw, hD, hexhaust, _, _, _, _, _⟩ :=
    hQPL.exists_three_port_component_domains hQ hDPL.closed (hKc.union hmeet hstripconn)
      (hQR.symm ▸ hRc) p hpconn hQports
  let u := w 0
  have hu : u ∈ P.cutCarrier := (hw 0).2.1
  have huB : u ∈ B (!owner) := (hw 0).1
  have hpQ (i : Fin 3) : p i ⊆ P.cutCarrier :=
    (hD i).2.2.2.2.trans (hD i).2.2.2.1
  have hcapQ (b : Bool) : P.capDisk b ⊆ P.cutCarrier := by
    intro x hx
    apply (hOldContact.symm.subset ?_).1
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  choose a ha using fun b => (P.isConnected_capDisk b).nonempty
  have haQ (b : Bool) := hcapQ b (ha b)
  have hportQ (b : Bool) : port b ⊆ P.cutCarrier := by
    cases b
    · exact hpQ 1
    · exact hpQ 2
  have hportD (b : Bool) : port b ⊆ connectedComponentIn P.cutCarrier (a b) :=
    (hportConn b).isPreconnected.subset_connectedComponentIn (Or.inr (ha b)) (hportQ b)
  have hcoverQ : P.cutCarrier = connectedComponentIn P.cutCarrier u ∪
      (connectedComponentIn P.cutCarrier (a false) ∪ connectedComponentIn P.cutCarrier (a true)) := by
    have h0 : D 0 = connectedComponentIn P.cutCarrier u := (hw 0).2.2
    have h1 : D 1 = connectedComponentIn P.cutCarrier (a false) :=
      ((hw 1).2.2).trans (connectedComponentIn_eq (hportD false (hw 1).1)).symm
    have h2 : D 2 = connectedComponentIn P.cutCarrier (a true) :=
      ((hw 2).2.2).trans (connectedComponentIn_eq (hportD true (hw 2).1)).symm
    have heq : (⋃ i, D i) = D 0 ∪ (D 1 ∪ D 2) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        fin_cases i
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr hi)
      · rintro (h0 | h1 | h2)
        · exact mem_iUnion.mpr ⟨0, h0⟩
        · exact mem_iUnion.mpr ⟨1, h1⟩
        · exact mem_iUnion.mpr ⟨2, h2⟩
    exact hexhaust.trans (heq.trans (by rw [h0, h1, h2]))
  let H := fun b => F '' (k b ×ˢ I)
  let cap : Bool → Bool → Set X := fun b d => F '' (k b ×ˢ {if d then (1 : ℝ) else 0})
  choose z hz using fun b => (hk b).1.isConnected.nonempty
  let v : Bool → Bool → X := fun b d => F (z b, if d then (1 : ℝ) else 0)
  have hvCap (b d : Bool) : v b d ∈ cap b d :=
    ⟨(z b, if d then (1 : ℝ) else 0), ⟨hz b, rfl⟩, rfl⟩
  have hfrontK' : frontier K = B (!owner) ∪ B owner := by
    cases owner
    · exact hfrontK.trans (union_comm _ _)
    · exact hfrontK
  have hcontact (b : Bool) : P.cutCarrier ∩ H b = cap b false ∪ cap b true := by
    obtain ⟨_, _, _, _, h⟩ := P.exists_retained_collar_product hK.closed
      (hKR.trans interior_subset) hfrontK' (sB owner) F hF hFi hFK htop hbottom
      hstripK hband (hk b).1 (hk b).2.1 (hk b).2.2.2 b (hk b).2.2.1
    exact h
  have hv (b d : Bool) : v b d ∈ P.cutCarrier ∩ H b := by
    apply (hcontact b).symm.subset
    cases d
    · exact Or.inl (hvCap b false)
    · exact Or.inr (hvCap b true)
  have hv0 (b : Bool) : connectedComponentIn P.cutCarrier (v b false) =
      connectedComponentIn P.cutCarrier u := by
    have hvB : v b false ∈ B (!owner) := hbottom.subset
      ⟨(z b, 0), ⟨(hk b).2.1 (hz b), rfl⟩, rfl⟩
    exact (connectedComponentIn_eq ((sB (!owner)).isConnected.isPreconnected.subset_connectedComponentIn
      huB (hpQ 0) hvB)).symm
  have hv1 (b : Bool) : connectedComponentIn P.cutCarrier (v b true) =
      connectedComponentIn P.cutCarrier (a b) := by
    have hvPort : v b true ∈ port b := Or.inl
      ⟨z b, hz b, (htop (z b) ((hk b).2.1 (hz b))).symm⟩
    exact (connectedComponentIn_eq (hportD b hvPort)).symm
  have hHc (b : Bool) : IsCompact (H b) :=
    ((hk b).1.isCompact.prod isCompact_Icc).image_of_continuousOn
      (hF.continuousOn.mono (prod_mono (hk b).2.1 subset_rfl))
  have hHconn (b : Bool) : IsConnected (H b) := ((hk b).1.isConnected.prod
    (isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num))).image _
    (hF.continuousOn.mono (prod_mono (hk b).2.1 subset_rfl))
  have hcapconn (b d : Bool) : IsConnected (cap b d) := by
    apply ((hk b).1.isConnected.prod
      (isConnected_singleton (x := if d then (1 : ℝ) else 0))).image
    apply hF.continuousOn.mono
    apply prod_mono (hk b).2.1
    intro t ht
    rw [show t = (if d then (1 : ℝ) else 0) from ht]
    cases d <;> norm_num
  have hHattach (b : Bool) : P.cutCarrier ∩ H b ⊆
      connectedComponentIn P.cutCarrier (v b false) ∪ connectedComponentIn P.cutCarrier (v b true) := by
    have hcapQ' (d : Bool) : cap b d ⊆ P.cutCarrier := by
      intro x hx
      apply ((hcontact b).symm.subset ?_).1
      cases d
      · exact Or.inl hx
      · exact Or.inr hx
    rw [hcontact b]
    exact union_subset_union
      ((hcapconn b false).isPreconnected.subset_connectedComponentIn (hvCap b false) (hcapQ' false))
      ((hcapconn b true).isPreconnected.subset_connectedComponentIn (hvCap b true) (hcapQ' true))
  have hSattach : P.cutCarrier ∩ P.closedStrip ⊆
      connectedComponentIn P.cutCarrier (a false) ∪ connectedComponentIn P.cutCarrier (a true) := by
    rw [hOldContact, P.endDisks_eq_capDisks]
    exact union_subset_union
      ((P.isConnected_capDisk false).isPreconnected.subset_connectedComponentIn (ha false) (hcapQ false))
      ((P.isConnected_capDisk true).isPreconnected.subset_connectedComponentIn (ha true) (hcapQ true))
  apply Topology.exists_three_component_reattachment_without_models (S := P.closedStrip)
    (HasPuncturedSphereModel e f) hQ.isClosed
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed hstripconn
    a (fun b => ⟨haQ b, by
      apply (hOldContact.symm.subset ?_).2
      rw [P.endDisks_eq_capDisks]
      cases b
      · exact Or.inl (ha false)
      · exact Or.inr (ha true)⟩) hSattach u hu hcoverQ H
    (fun b => (hHc b).isClosed) hHconn v hv hv0 hv1 hHattach
  · intro x hx
    rw [hOldEq] at hx ⊢
    exact hno x hx
  · intro hdis hm0 hm1
    rw [hOldEq]
    exact (P.punctured_model_iff_disjoint_exterior_cap_models hR he hK hKR B sB hBdis
      hfrontK hsmall hstripK owner k q howner hk hcomp hkdis hcover hopen hQPL a ha
      f L g hg hgi (fun x hx => hreal x ((connectedComponentIn_subset _ _ hx).1))).mpr
        ⟨hdis, fun b => by cases b; exact hm0; exact hm1⟩
  · intro b hm
    obtain ⟨N, W, σ, hσ, hσval, hmark, hmarkOther, hWfront⟩ := hproducts b
    have hHR : P.cutCarrier ∪ H b ⊆ R := by
      apply union_subset (hQeq.subset.trans inter_subset_left)
      apply subset_trans _ (hKR.trans interior_subset)
      rw [← hFK]
      exact image_mono (prod_mono (hk b).2.1 subset_rfl)
    have hmodels := P.component_models_of_retained_collar_exchange hR he hK hKR B sB
      hBdis hfrontK hsmall hstripK owner k q howner hk hcomp hkdis hcover hopen hQPL hQeq
      F hF hFi hFK htop hbottom b N W σ hσ hσval hmark hmarkOther hWfront
      (v b) (hvCap b) L g hg hgi
      (fun x hx => hreal x (hHR (connectedComponentIn_subset _ _ hx))) hm
    exact ⟨hv0 b ▸ hmodels false, hv1 b ▸ hmodels true⟩
  · intro b heq
    have hs : v b true ∈ connectedComponentIn P.cutCarrier (v b false) := by
      rw [hv0 b, heq, ← hv1 b]
      exact mem_connectedComponentIn (hv b true).1
    exact (P.not_hasPuncturedSphereModel_of_retained_collar_self_attachment hR hK.closed
      (hKR.trans interior_subset) hfrontK' hopen hQPL (sB owner) F hF hFi hFK htop hbottom
      hstripK hband (hk b).1 (hk b).2.1 (hk b).2.2.2 b (hk b).2.2.1
      (hvCap b false) (hvCap b true) hs).2

end PoincareConjecture.M76.OriginalDiskProduct
