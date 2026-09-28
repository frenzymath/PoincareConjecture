import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.AttachmentComponentModelRestriction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RetainedCollarOtherPort
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RetainedCollarProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskThreePorts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExteriorCapSpheres
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereProductDomain









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

set_option maxHeartbeats 1000000 in
theorem component_models_of_retained_collar_exchange
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R K : Set X} {j : V2 → X}
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
    (hQPL : PLDomain e P.cutCarrier)
    (hQeq : P.cutCarrier = R ∩ (interior (K ∪ P.closedStrip))ᶜ)
    (F : V3 × ℝ → X) (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I)) (hFK : F '' (Sphere ×ˢ I) = K)
    (htop : ∀ z ∈ Sphere, F (z, 1) = (sB owner).map z)
    (hbottom : F '' (Sphere ×ˢ {(0 : ℝ)}) = B (!owner))
    (b : Bool) (N : Set X)
    (W : ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip : Set X) ≃ₜ
      (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)))
    (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I))
    (hσval : ∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (W.symm z : X))
    (hmark : ∀ x : ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip : Set X),
      (x : X) ∈ N ↔ (W x : P3 × ℝ).2 = if b then (1 : ℝ) else 0)
    (hmarkOther : ∀ x : ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip : Set X),
      (x : X) ∈ ((sB owner).map '' k (!b)) ∪ P.capDisk (!b) ↔
        (W x : P3 × ℝ).2 = if !b then (1 : ℝ) else 0)
    (hWfront : frontier ((F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip) =
      N ∪ (((sB owner).map '' k (!b)) ∪ P.capDisk (!b)))
    (a : Bool → X) (ha : ∀ d, a d ∈ F '' (k b ×ˢ {if d then (1 : ℝ) else 0}))
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ connectedComponentIn (P.cutCarrier ∪ F '' (k b ×ˢ I)) (a false),
      f x ∈ L.space ∧ g (f x) = x)
    (hm : HasPuncturedSphereModel e f
      (connectedComponentIn (P.cutCarrier ∪ F '' (k b ×ˢ I)) (a false))) :
    ∀ d, HasPuncturedSphereModel e f (connectedComponentIn P.cutCarrier (a d)) := by
  classical
  let H := F '' (k b ×ˢ I)
  let U := (F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip
  let ret := fun d => (sB owner).map '' k d
  let port := fun d => ret d ∪ P.capDisk d
  let Z := frontier R ∪ port (!b)
  let p : Bool → Set X := fun d => if d then port b else B (!owner)
  let cap : Bool → Set X := fun d => F '' (k b ×ˢ {if d then (1 : ℝ) else 0})
  have hband := (howner owner).mpr rfl
  obtain ⟨hmarks, hretDis, _, _, _, hportDis, hoppDis, hKcut⟩ :=
    P.three_connected_ports_of_retained_disks hR he hK hKR B sB hBdis hfrontK
      hsmall hstripK owner k q howner hk hcomp hkdis hcover
  obtain ⟨sPort, _⟩ := P.exists_original_exterior_retained_caps B sB he.compatible
    hK.closed hfrontK hstripK owner hband k q
    (fun d => ⟨(hk d).1, (hk d).2.1, hcomp d, (hk d).2.2.1⟩)
  let sp : ∀ d, ChartwisePLSphere e (p d) := fun d => by
    cases d
    · exact sB (!owner)
    · exact sPort b
  have hpdis : Disjoint (p false) (p true) := hoppDis b
  have hBK (d : Bool) : B d ⊆ K := by
    apply subset_trans _ hK.closed.frontier_subset
    rw [hfrontK]
    cases d
    · exact subset_union_left
    · exact subset_union_right
  have hstripInside : P.closedStrip ⊆ interior R := by
    rintro x ⟨z, hz, rfl⟩
    apply hsmall
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hretK (d : Bool) : ret d ⊆ K := by
    rintro x ⟨z, hz, rfl⟩
    apply hBK owner
    rw [(sB owner).map_eq ⟨z, (hk d).2.1 hz⟩]
    exact ((sB owner).parametrization ⟨z, (hk d).2.1 hz⟩).property
  have hcapStrip (d : Bool) : P.capDisk d ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases d
    · exact subset_union_left
    · exact subset_union_right
  have hportInside (d : Bool) : port d ⊆ interior R :=
    union_subset ((hretK d).trans hKR) ((hcapStrip d).trans hstripInside)
  have hpInside (d : Bool) : p d ⊆ interior R := by
    cases d
    · exact (hBK (!owner)).trans hKR
    · exact hportInside b
  have hHK : H ⊆ K := by
    rw [← hFK]
    exact image_mono (prod_mono (hk b).2.1 subset_rfl)
  have hH := ((hk b).1.isCompact.prod isCompact_Icc).image_of_continuousOn
    (hF.continuousOn.mono (prod_mono (hk b).2.1 subset_rfl))
  have hHconn : IsConnected H := ((hk b).1.isConnected.prod
    (isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num))).image _
    (hF.continuousOn.mono (prod_mono (hk b).2.1 subset_rfl))
  have hcapconn (d : Bool) : IsConnected (cap d) := by
    apply ((hk b).1.isConnected.prod
      (isConnected_singleton (x := if d then (1 : ℝ) else 0))).image
    apply hF.continuousOn.mono
    apply prod_mono (hk b).2.1
    intro t ht
    rw [show t = (if d then (1 : ℝ) else 0) from ht]
    cases d <;> norm_num
  have hfrontK' : frontier K = B (!owner) ∪ B owner := by
    cases owner
    · exact hfrontK.trans (union_comm _ _)
    · exact hfrontK
  obtain ⟨_, _, _, _, hcontact⟩ := P.exists_retained_collar_product
    hK.closed (hKR.trans interior_subset) hfrontK' (sB owner) F hF hFi hFK htop hbottom
    hstripK hband (hk b).1 (hk b).2.1 (hk b).2.2.2 b (hk b).2.2.1
  have hcapP (d : Bool) : cap d ⊆ p d := by
    cases d
    · exact (image_mono (prod_mono (hk b).2.1 subset_rfl)).trans hbottom.subset
    · rintro x ⟨⟨z,t⟩, ⟨hz,ht⟩, rfl⟩
      have ht1 : t = 1 := ht
      subst t
      exact Or.inl ⟨z, hz, (htop z ((hk b).2.1 hz)).symm⟩
  have hOther : Disjoint H (port (!b)) :=
    P.retained_collar_disjoint_other_cap_port (sB owner) F hF hFi hFK htop
      hstripK hband k q (fun d => (hk d).1) (fun d => (hk d).2.1)
      (fun d => (hk d).2.2.2) (fun d => (hk d).2.2.1) hretDis b
  have hHZ : Disjoint H Z := disjoint_union_right.mpr ⟨
    disjoint_left.mpr (fun _ hx hf => hf.2 (hKR (hHK hx))), hOther⟩
  have hZ : IsClosed Z := isClosed_frontier.union (sPort (!b)).isCompact.isClosed
  have hpZ (d : Bool) : Disjoint (p d) Z := by
    apply disjoint_union_right.mpr
    refine ⟨disjoint_left.mpr (fun _ hx hf => hf.2 (hpInside d hx)), ?_⟩
    cases d
    · exact hoppDis (!b)
    · cases b
      · exact hportDis
      · exact hportDis.symm
  obtain ⟨hL, _, _, _, hLf⟩ := he.interior_removal_geometry hR hK hKR
  obtain ⟨hQ, _, hQf, _, _, _⟩ := P.cut_geometry hL hopen
  have hRf : frontier R \ P.openStrip = frontier R := sdiff_eq_left.mpr
    (disjoint_left.mpr (fun _ hf ho => hf.2 (hstripInside
      (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self) ho))))
  have hQfront : frontier P.cutCarrier = Z ∪ (p false ∪ p true) := by
    rw [hQf, hLf, union_sdiff_distrib, hRf]
    have htemp : ((frontier K \ P.openStrip) ∪ frontier R) ∪ P.endDisks =
        (((B (!owner) ∪ port false) ∪ port true) ∪ frontier R) := by
      rw [show ((frontier K \ P.openStrip) ∪ frontier R) ∪ P.endDisks =
        ((frontier K \ P.openStrip) ∪ P.endDisks) ∪ frontier R by
          ext x; simp only [mem_union]; tauto]
      exact congrArg (· ∪ frontier R) hKcut
    rw [htemp]
    cases b <;> ext x <;> simp only [Z, p, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, reduceIte, mem_union] <;> tauto
  have hWPL := original_sphere_product_plDomain W σ hσ hσval he.compatible he.cover
  have hUK : U ⊆ K ∪ P.closedStrip := union_subset_union
    ((image_mono (prod_mono sdiff_subset subset_rfl)).trans hFK.subset) subset_rfl
  have hUinside : U ⊆ interior R := hUK.trans (union_subset hKR hstripInside)
  obtain ⟨_, hAPL', _, _, hAf⟩ := he.interior_removal_geometry hR hWPL hUinside
  obtain ⟨_, _, hAeq⟩ := P.retained_collar_exchange_exterior
    (sB owner) F hF hFi hFK htop hstripK hband (hk b).1 (hk b).2.1
      (hk b).2.2.2 b (hk b).2.2.1 R (hKR.trans interior_subset)
  rw [← hQeq] at hAeq
  have hAPL : PLDomain e (P.cutCarrier ∪ H) := hAeq ▸ hAPL'
  have hAfront : frontier (P.cutCarrier ∪ H) = Z ∪ N := by
    rw [← hAeq, hAf, hWfront]
    ext x
    simp only [Z, port, ret, mem_union]
    tauto
  have hNU : N ⊆ U := subset_union_left.trans
    (hWfront.symm.subset.trans hWPL.closed.frontier_subset)
  obtain ⟨sN⟩ := original_sphere_product_marked_endpoint W σ hσ hσval
    (show (if b then (1 : ℝ) else 0) ∈ I by cases b <;> norm_num) hNU hmark
  have hNOther : Disjoint N (port (!b)) := by
    apply disjoint_left.mpr
    intro x hxN hxOther
    have h0 := (hmark ⟨x, hNU hxN⟩).mp hxN
    have h1 := (hmarkOther ⟨x, hNU hxN⟩).mp hxOther
    cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, reduceIte] at h0 h1 <;>
      linarith
  have hNZ : Disjoint N Z := disjoint_union_right.mpr ⟨
    disjoint_left.mpr (fun _ hx hf => hf.2 (hUinside (hNU hx))), hNOther⟩
  have hNH := P.retained_collar_meets_selected_exchange_boundary
    (sB owner) F hF hFi hFK htop hstripK hband (hk b).1 (hk b).2.1
      (hk b).2.2.2 b (hk b).2.2.1 hOther hWPL.closed hWfront
  exact component_models_of_two_port_attachment hQ hQPL hH hHconn hAPL cap hcapconn
    hcontact a ha p sp hpdis hcapP hZ hHZ hpZ sN.isConnected sN.isCompact.isClosed
    hNZ hNH hQfront hAfront L g hg hgi hreal hm

end PoincareConjecture.M76.OriginalDiskProduct
