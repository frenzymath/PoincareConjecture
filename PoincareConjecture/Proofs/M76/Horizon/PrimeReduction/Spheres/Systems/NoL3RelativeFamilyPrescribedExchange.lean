import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeRegionLocalization
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3PrescribedProductExchange
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3ComponentReassembly










set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem HasNoPuncturedSphereComponents.exists_relative_family_prescribed_product_noL3_exchange
    {X E ι κ : Type*} [MetricSpace X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R Q₀ D : Set X} (O₀ S : κ → Set X)
    (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O₀ i))
    (hQ₀eq : Q₀ = R \ ⋃ i, O₀ i) (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (hO₀ : ∀ i, IsOpen (O₀ i)) (hCR₀ : ∀ i, closure (O₀ i) ⊆ interior R)
    (hdis₀ : Pairwise fun i j => Disjoint (closure (O₀ i)) (closure (O₀ j)))
    (hopen₀ : ∀ i z, (W₀ i z : X) ∈ O₀ i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter₀ : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : ∀ i, S i ⊆ closure (O₀ i))
    (B₀ : κ × Bool → Set X) (sB₀ : ∀ i, ChartwisePLSphere e (B₀ i))
    (hB₀dis : Pairwise fun i j => Disjoint (B₀ i) (B₀ j))
    (hB₀sub : ∀ i, B₀ i ⊆ closure (O₀ i.1))
    (hfront₀ : frontier Q₀ = frontier R ∪ ⋃ i, B₀ i)
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R) (hSR : ∀ i, S i ⊆ interior R)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (i : κ) (hD : IsCompact D) (hDc : IsConnected D)
    (hDR : D ⊆ interior R) (hDother : ∀ k, k ≠ i → Disjoint D (S k))
    (hmeet : (S i ∩ D).Nonempty)
    (p : V2 × ℝ → X) (hp : PolyhedralPLInCharts e p (Disk ×ˢ Icc (-1 : ℝ) 1))
    (hpi : InjOn p (Disk ×ˢ Icc (-1 : ℝ) 1))
    (hpD : MapsTo p (Disk ×ˢ Icc (-1 : ℝ) 1) D)
    (hpS : ∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, p z ∈ S i ↔ z.1 ∈ Rim) :
    ∃ (Q : Set X) (B : κ × Bool → Set X) (sB : ∀ b, ChartwisePLSphere e (B b))
      (O : κ → Set X) (W : ∀ k, (S k × unitInterval) ≃ₜ closure (O k)) (a : X),
      let A := R \ ⋃ k : {k : κ // k ≠ i}, O k.val
      let C := connectedComponentIn A a
      Q = R \ ⋃ k, O k ∧ IsCompact Q ∧ PLDomain e Q ∧
      HasNoPuncturedSphereComponents e f Q ∧
      (∀ k, IsOpen (O k) ∧ IsCompact (closure (O k)) ∧
        IsConnected (closure (O k)) ∧ closure (O k) ⊆ interior R) ∧
      Pairwise (fun k l => Disjoint (closure (O k)) (closure (O l))) ∧
      (∀ k z, (W k z : X) ∈ O k ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ k z, (W k z : X) ∈ S k ↔ (z.2 : ℝ) = 1/2) ∧
      (∀ k, S k ⊆ closure (O k)) ∧
      frontier Q = frontier R ∪ ⋃ k, B k ∧
      Pairwise (fun k l => Disjoint (B k) (B l)) ∧
      (∀ k, B k ⊆ closure (O k.1)) ∧
      IsCompact C ∧ IsConnected C ∧ PLDomain e C ∧ S i ⊆ interior C ∧
      closure (O i) ⊆ interior C ∧ D ⊆ interior C ∧
    ∃ (K Bopp : Set X)
      (P : OriginalDiskProduct e (C ∩ (interior K)ᶜ) (fun z => p (z,0)))
      (k q : Bool → Set V3) (b : Bool)
      (caps : ∀ b, ChartwisePLSphere e (((sS i).map '' k b) ∪ P.capDisk b))
      (U : Set X) (WU : U ≃ₜ (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)))
      (σ : P3 × ℝ → X),
      IsCompact K ∧ PLDomain e K ∧ K ⊆ O i ∩ interior C ∧
      P.map = p ∧
      MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior C ∩ Boppᶜ) ∧
      (∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ S i ↔ z.1 ∈ Rim) ∧
      IsOpen ((Subtype.val : S i → X) ⁻¹' (P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2)))) ∧
      (∀ b, IsFinitePLBallPair (ℝ × ℝ) (k b) (q b) ∧ k b ⊆ Sphere ∧
        IsFinitePLBallPair (ℝ × ℝ) (Sphere \ (k b \ q b)) (q b) ∧
        (sS i).map '' q b = P.capRimSet b ∧
        ((sS i).map '' k b) ∩ P.closedStrip = (sS i).map '' q b) ∧
      Disjoint ((sS i).map '' k true) ((sS i).map '' k false) ∧
      (((sS i).map '' k true) ∪ ((sS i).map '' k false)) ∪ (P.map '' (Rim ×ˢ J)) = S i ∧
      (∀ b, EqOn (caps b).map (sS i).map (k b) ∧
        (caps b).map '' (Sphere \ (k b \ q b)) = P.capDisk b) ∧
      PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) ∧
      (∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (WU.symm z : X)) ∧
      IsCompact U ∧ PLDomain e U ∧ U ⊆ K ∪ P.closedStrip ∧ U ⊆ interior C ∧
      (((sS i).map '' k b) ∪ P.capDisk b) ⊆ frontier U ∧
      (∀ x : U, (x : X) ∈ (((sS i).map '' k b) ∪ P.capDisk b) ↔
        (WU x : P3 × ℝ).2 = if b then (1 : ℝ) else 0) ∧
      HasNoPuncturedSphereComponents e f (C \ interior U) ∧
      HasNoPuncturedSphereComponents e f (A \ interior U) := by
  classical
  obtain ⟨Q,B,sB,O,W,a,hQeq,hQ,hQPL,hnoQ,hO,hOdis,hW,hWcenter,hSC,hfront,hmarksdis,
      hBsub,ha,hCc,hCconn,hCPL,hZC,hOiC,hCut,hCutPL,hCutNo,hCutFront,hOf,hcomponents⟩ :=
    hno.exists_relative_region_component_localization O₀ S W₀ hQ₀eq hQ₀ hQ₀PL hO₀ hCR₀ hdis₀
      hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ sS hdis hR he hSR
      L g hg hgi hreal i hD hDc hDR hDother hmeet
  let A := R \ ⋃ k : {k : κ // k ≠ i}, O k.val
  let C := connectedComponentIn A a
  have hCR : C ⊆ R := (connectedComponentIn_subset A a).trans inter_subset_left
  obtain ⟨K,Bopp,P,k,q,b,caps,U,WU,σ,hK,hKPL,hKO,hPmap,hP,hmark,hopen,hk,hkd,
      hkcover,hcaps,hnoK,hσ,hσval,hU,hUPL,hUsub,hcap,hcapmark,hnoU⟩ :=
    (sS i).exists_original_prescribed_product_noL3_exchange hCc hCconn hCPL
      (fun x hx => hZC (Or.inl hx))
      (W i) (hO i).1 hOiC (hW i) (hWcenter i) (hSC i)
      hCut hCutPL (fun b => B (i,b)) (fun b => sB (i,b))
      (fun b c hbc => hmarksdis (by simpa using hbc))
      (fun b => hBsub (i,b)) (by
        rw [hCutFront]
        congr 1
        ext x
        simp only [mem_union,mem_iUnion,Bool.exists_bool])
      f L g hf hg hgi (fun x hx => hreal x (hCR hx)) hCutNo p hp hpi
      (fun z hz => hZC (Or.inr (hpD hz))) hpS
  have hUi : U ⊆ interior C := by
    intro x hx
    rcases hUsub hx with hxK | hxP
    · exact (hKO hxK).2
    · obtain ⟨z,hz,rfl⟩ := hxP
      exact (hP ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩).1
  have hAQ : A \ O i = Q := by
    rw [hQeq]
    ext x
    simp only [A,mem_sdiff,mem_iUnion,Subtype.exists,not_exists]
    constructor
    · rintro ⟨⟨hxR,hxO⟩,hxi⟩
      refine ⟨hxR,fun j hj => ?_⟩
      by_cases hji : j = i
      · exact hxi (hji ▸ hj)
      · exact hxO j hji hj
    · rintro ⟨hxR,hxO⟩
      exact ⟨⟨hxR,fun j _ => hxO j⟩,hxO i⟩
  have hnoGlobal : HasNoPuncturedSphereComponents e f (A \ interior U) :=
    (hAQ.symm ▸ hnoQ).replace_component_cut
      (subset_closure.trans (hOiC.trans interior_subset))
      (interior_subset.trans (hUi.trans interior_subset)) hnoU
  exact ⟨Q,B,sB,O,W,a,hQeq,hQ,hQPL,hnoQ,hO,hOdis,hW,hWcenter,hSC,hfront,hmarksdis,hBsub,
    hCc,hCconn,hCPL,fun x hx => hZC (Or.inl hx),hOiC,(fun x hx => hZC (Or.inr hx)),
    K,Bopp,P,k,q,b,caps,U,WU,σ,hK,hKPL,hKO,hPmap,hP,hmark,hopen,hk,hkd,hkcover,
    hcaps,hσ,hσval,hU,hUPL,hUsub,hUi,hcap,hcapmark,hnoU,hnoGlobal⟩

end PoincareConjecture.M76
