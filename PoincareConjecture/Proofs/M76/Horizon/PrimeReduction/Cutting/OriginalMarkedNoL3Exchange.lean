import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalFiveCaseNoL3
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalCollarExchange
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExteriorCapSpheres

set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_original_marked_noL3_exchange
    {X E A ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
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
    (N : SimplicialComplex ℝ A) (hN : N.faces.Finite) (c : A × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (N.space ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (hKeq : K = c '' (N.space ×ˢ Icc (-ε) ε))
    (hBeq : ∀ a, B a = c '' (N.space ×ˢ {if a then ε else -ε}))
    (f : X → E) (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f (R ∩ (interior K)ᶜ)) :
    ∃ (owner b : Bool) (k q : Bool → Set V3)
      (t : ∀ a, ChartwisePLSphere e (((sB owner).map '' k a) ∪ P.capDisk a))
      (U : Set X) (W : U ≃ₜ (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)))
      (σ : P3 × ℝ → X),
      (∀ d, P.map '' (Rim ×ˢ J) ⊆ B d ↔ d = owner) ∧
      (∀ a, IsFinitePLBallPair (ℝ × ℝ) (k a) (q a) ∧ k a ⊆ Sphere ∧
        IsFinitePLBallPair (ℝ × ℝ) (Sphere \ (k a \ q a)) (q a) ∧
        (sB owner).map '' q a = P.capRimSet a ∧
        ((sB owner).map '' k a) ∩ P.closedStrip = (sB owner).map '' q a) ∧
      Disjoint ((sB owner).map '' k true) ((sB owner).map '' k false) ∧
      (((sB owner).map '' k true) ∪ ((sB owner).map '' k false)) ∪
        (P.map '' (Rim ×ˢ J)) = B owner ∧
      (∀ a, EqOn (t a).map (sB owner).map (k a) ∧
        (t a).map '' (Sphere \ (k a \ q a)) = P.capDisk a) ∧
      PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) ∧
      (∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (W.symm z : X)) ∧
      IsCompact U ∧ PLDomain e U ∧ U ⊆ K ∪ P.closedStrip ∧
      (((sB owner).map '' k b) ∪ P.capDisk b) ⊆ frontier U ∧
      (∀ x : U, (x : X) ∈ (((sB owner).map '' k b) ∪ P.capDisk b) ↔
        (W x : P3 × ℝ).2 = if b then (1 : ℝ) else 0) ∧
      HasNoPuncturedSphereComponents e f (R ∩ (interior U)ᶜ) := by
  obtain ⟨owner,F,annulusMap,k,q,C,hF,hFi,hFK,htop,hbottom,howner,
      _,_,_,hk,hkdis,hcover,hproducts⟩ :=
    P.exists_original_collar_exchanges B sB hR he (hKR.trans interior_subset)
      hBdis rfl hfrontK hsmall hstripK N hN c hc hci hε hεle hKeq hBeq
  have hk' (b : Bool) : IsFinitePLBallPair (ℝ × ℝ) (k b) (q b) ∧ k b ⊆ Sphere ∧
      (sB owner).map '' q b = P.capRimSet b ∧
      ((sB owner).map '' k b) ∩ (P.map '' (Rim ×ˢ J)) = (sB owner).map '' q b :=
    ⟨(hk b).1,(hk b).2.1,(hk b).2.2.2.1,(hk b).2.2.2.2⟩
  obtain ⟨b,hnew⟩ := P.exists_same_collar_exchange_without_punctured_components
    hR hRc he hK hKc hKR B sB hBdis hfrontK hsmall hstripK hDPL hDfront hopen
    owner k q howner hk' (fun b => (hk b).2.2.1) hkdis hcover
    F hF hFi hFK htop hbottom (fun b => by
      obtain ⟨W,σ,hσ,hσval,hmark,hmarkOther,hfront⟩ := hproducts b
      exact ⟨(F '' C b) ∪ P.capDisk b,W,σ,hσ,hσval,hmark,hmarkOther,hfront⟩)
    f L g hf hg hgi hreal hno
  obtain ⟨t,ht⟩ := P.exists_original_exterior_retained_caps B sB he.compatible hK.closed
    hfrontK hstripK owner ((howner owner).mpr rfl) k q (fun a =>
      ⟨(hk a).1,(hk a).2.1,(hk a).2.2.1,(hk a).2.2.2.1⟩)
  obtain ⟨W,σ,hσ,hσval,_,hmarkOther,hfront⟩ := hproducts b
  let U := (F '' ((Sphere \ (k b \ q b)) ×ˢ I)) ∪ P.closedStrip
  have hUc : IsCompact U :=
    (((hk b).2.2.1.isCompact.prod isCompact_Icc).image_of_continuousOn
      (hF.continuousOn.mono (prod_mono sdiff_subset subset_rfl))).union
      (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hUsub : U ⊆ K ∪ P.closedStrip := union_subset_union
    ((image_mono (prod_mono sdiff_subset subset_rfl)).trans hFK.subset) subset_rfl
  have hQeq : P.cutCarrier = R ∩ (interior (K ∪ P.closedStrip))ᶜ :=
    (P.global_common_cut_geometry hR he hDPL hKR rfl hsmall hDfront).2.1.symm
  obtain ⟨_,_,hout⟩ := P.retained_collar_exchange_exterior
    (sB owner) F hF hFi hFK htop hstripK ((howner owner).mpr rfl)
    (hk b).1 (hk b).2.1 (hk b).2.2.2.2 b (hk b).2.2.2.1 R
    (hKR.trans interior_subset)
  rw [←hQeq] at hout
  refine ⟨owner,!b,k,q,t,U,W,σ,howner,?_,hkdis,hcover,ht,hσ,hσval,hUc,
    original_sphere_product_plDomain W σ hσ hσval he.compatible he.cover,hUsub,
    (fun x hx => hfront.symm.subset (Or.inr hx)),hmarkOther,?_⟩
  · intro a
    refine ⟨(hk a).1,(hk a).2.1,(hk a).2.2.1,(hk a).2.2.2.1,?_⟩
    have hretK : (sB owner).map '' k a ⊆ K := by
      rintro x ⟨z,hz,rfl⟩
      have hzB : (sB owner).map z ∈ B owner := by
        rw [(sB owner).map_eq ⟨z,(hk a).2.1 hz⟩]
        exact ((sB owner).parametrization ⟨z,(hk a).2.1 hz⟩).property
      apply hK.closed.frontier_subset
      rw [hfrontK]
      cases owner
      · exact Or.inl hzB
      · exact Or.inr hzB
    calc
      ((sB owner).map '' k a) ∩ P.closedStrip =
          ((sB owner).map '' k a) ∩ (P.closedStrip ∩ K) := by
        ext x
        exact ⟨fun hx => ⟨hx.1,hx.2,hretK hx.1⟩,fun hx => ⟨hx.1,hx.2.1⟩⟩
      _ = (sB owner).map '' q a := by rw [hstripK]; exact (hk a).2.2.2.2
  · intro x hx
    change x ∈ R ∩ (interior U)ᶜ at hx
    rw [hout] at hx ⊢
    exact hnew x hx

end PoincareConjecture.M76.OriginalDiskProduct
