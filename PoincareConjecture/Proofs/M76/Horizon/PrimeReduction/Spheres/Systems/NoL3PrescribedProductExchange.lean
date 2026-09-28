import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PrescribedWholeProductCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PrescribedProductOnOppositeDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeOppositeCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalMarkedNoL3Exchange









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
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem ChartwisePLSphere.exists_original_prescribed_product_noL3_exchange
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S O₀ : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (hRc : IsConnected R)
    (he : PLDomain e R) (hSR : S ⊆ interior R)
    (W₀ : (S × unitInterval) ≃ₜ closure O₀) (hO₀open : IsOpen O₀)
    (hCR₀ : closure O₀ ⊆ interior R)
    (hO₀ : ∀ z, (W₀ z : X) ∈ O₀ ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS₀ : ∀ z, (W₀ z : X) ∈ S ↔ (z.2 : ℝ) = 1 / 2)
    (hSC₀ : S ⊆ closure O₀)
    (hQ₀ : IsCompact (R \ O₀)) (hQ₀PL : PLDomain e (R \ O₀))
    (D₀ : Bool → Set X) (sD₀ : ∀ i, ChartwisePLSphere e (D₀ i))
    (hD₀dis : Pairwise fun i j => Disjoint (D₀ i) (D₀ j))
    (hD₀sub : ∀ i, D₀ i ⊆ closure O₀)
    (hD₀front : frontier (R \ O₀) = frontier R ∪ ⋃ i, D₀ i)
    (f : X → E) (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f (R \ O₀))
    (p : V2 × ℝ → X) (hp : PolyhedralPLInCharts e p (Disk ×ˢ Icc (-1 : ℝ) 1))
    (hpi : InjOn p (Disk ×ˢ Icc (-1 : ℝ) 1))
    (hpR : MapsTo p (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R))
    (hpS : ∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, p z ∈ S ↔ z.1 ∈ Rim) :
    ∃ (K B : Set X) (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) (fun z => p (z,0)))
      (k q : Bool → Set V3) (b : Bool)
      (t : ∀ a, ChartwisePLSphere e ((s.map '' k a) ∪ P.capDisk a))
      (U : Set X) (W : U ≃ₜ (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)))
      (σ : P3 × ℝ → X),
      IsCompact K ∧ PLDomain e K ∧ K ⊆ O₀ ∩ interior R ∧
      P.map = p ∧ MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior R ∩ Bᶜ) ∧
      (∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ S ↔ z.1 ∈ Rim) ∧
      IsOpen ((Subtype.val : S → X) ⁻¹' (P.map '' (Rim ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))) ∧
      (∀ a, IsFinitePLBallPair (ℝ × ℝ) (k a) (q a) ∧ k a ⊆ Sphere ∧
        IsFinitePLBallPair (ℝ × ℝ) (Sphere \ (k a \ q a)) (q a) ∧
        s.map '' q a = P.capRimSet a ∧ (s.map '' k a) ∩ P.closedStrip = s.map '' q a) ∧
      Disjoint (s.map '' k true) (s.map '' k false) ∧
      ((s.map '' k true) ∪ (s.map '' k false)) ∪ (P.map '' (Rim ×ˢ J)) = S ∧
      (∀ a, EqOn (t a).map s.map (k a) ∧
        (t a).map '' (Sphere \ (k a \ q a)) = P.capDisk a) ∧
      HasNoPuncturedSphereComponents e f (R ∩ (interior K)ᶜ) ∧
      PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ I) ∧
      (∀ z : (frontier (halfBall 1) ×ˢ I : Set (P3 × ℝ)), σ z = (W.symm z : X)) ∧
      IsCompact U ∧ PLDomain e U ∧ U ⊆ K ∪ P.closedStrip ∧
      ((s.map '' k b) ∪ P.capDisk b) ⊆ frontier U ∧
      (∀ x : U, (x : X) ∈ ((s.map '' k b) ∪ P.capDisk b) ↔
        (W x : P3 × ℝ).2 = if b then (1 : ℝ) else 0) ∧
      HasNoPuncturedSphereComponents e f (R ∩ (interior U)ᶜ) := by
  have hSO₀ : S ⊆ O₀ := by
    intro x hx
    let z := W₀.symm ⟨x,hSC₀ hx⟩
    have hz : (W₀ z : X) = x := congrArg Subtype.val (W₀.apply_symm_apply _)
    have ht := (hS₀ z).mp (hz.symm ▸ hx)
    exact hz ▸ (hO₀ z).mpr (by rw [ht]; norm_num)
  let T := Icc (-1 : ℝ) 1
  letI : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let j : V2 × T → X := fun z => p (z.1,z.2)
  have hj : Continuous (fun z : Disk × T => j (z.1,z.2)) :=
    hp.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨z.1.property,z.2.property⟩)
  have hjS (z : V2) (hz : z ∈ Disk) (t : T) : j (z,t) ∈ S ↔ z ∈ Rim :=
    hpS (z,t) ⟨hz,t.property⟩
  have himage (A : Set V2) :
      j '' (A ×ˢ (univ : Set T)) = p '' (A ×ˢ T) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z,t⟩,⟨hz,_⟩,rfl⟩
      exact ⟨(z,t),⟨hz,t.property⟩,rfl⟩
    · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      exact ⟨(z,⟨t,ht⟩),⟨hz,mem_univ _⟩,rfl⟩
  obtain ⟨a,N,C,K,B,hN,hC,hCi,hCK,hCS,hCB,hK,hKPL,hKO,hB,hBS,hfront,hcontact,
      c,ε,positive,hc,hci,hε,hεsmall,hNc,hzero,hsmall,hcopen,hKeq,hKi,F,hF,hFi,hNF⟩ :=
    s.exists_original_opposite_unit_product_collar hR he hSR hO₀open hSO₀ j hj hjS
  have hcontact' : K ∩ (p '' (Disk ×ˢ T)) = p '' (Rim ×ˢ T) := by
    simpa only [himage] using hcontact
  obtain ⟨P,hPmap,hPsmall,hopen,hcut,hcutPL,hstrip,hD,hDPL,hDfront,hwidths⟩ :=
    exists_prescribed_product_on_opposite_domain hR he hK hKPL
      (fun x hx => (hKO hx).2) hBS hfront p hp hpi hpR hpS hcontact'
  have hPmark (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ Icc (-1 : ℝ) 1) :
      P.map z ∈ S ↔ z.1 ∈ Rim := by rw [hPmap]; exact hpS z hz
  have hKc : IsConnected K := by
    rw [hKeq]
    have hI : IsConnected (if positive then Icc (-ε) 0 else Icc 0 ε) := by
      cases positive <;> simp only [Bool.false_eq_true,reduceIte] <;>
        exact isConnected_Icc (by linarith)
    apply (hNc.prod hI).image _
    apply hc.continuousOn.mono (prod_mono subset_rfl ?_)
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] <;>
      exact Icc_subset_Icc (by linarith) (by linarith)
  obtain ⟨sB⟩ := hB
  let Bs : Bool → Set X := fun b => if b then S else B
  let sBs : ∀ b, ChartwisePLSphere e (Bs b) := fun b => by
    cases b
    · exact sB
    · exact s
  have hnoK : HasNoPuncturedSphereComponents e f (R ∩ (interior K)ᶜ) :=
    hno.original_relative_opposite_collar_cut s hR he W₀ hCR₀
      hO₀ hS₀ hSC₀ hQ₀ hQ₀PL D₀ sD₀ hD₀dis hD₀sub hD₀front
      F hF hFi hNF (N.isCompact_space_of_finite hN) hNc c hc hci hε
      (by linarith) hsmall hcopen hzero positive hKi
      hKPL (fun x hx => (hKO hx).2) Bs sBs hfront L g hg hgi hreal
  have hBeq (b : Bool) : Bs b = C '' (N.space ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)}) := by
    cases b
    · exact hCB
    · exact hCS
  obtain ⟨owner,b,k,q,t,U,W,σ,howner,hk,hdis,hcover,ht,hσ,hσval,hU,hUPL,hUsub,
      hcap,hmark,hnoU⟩ :=
    P.exists_original_marked_noL3_exchange hR hRc he hKPL hKc
      (fun x hx => (hKO hx).2) Bs sBs hBS hfront
      (fun z hz => (hPsmall hz).1) hstrip hDPL hDfront hopen
      N hN C hC hCi (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hCK hBeq
      f L g hf hg hgi hreal hnoK
  have hownerTrue : owner = true := by
    symm
    apply (howner true).mp
    rintro x ⟨z,hz,rfl⟩
    exact (hPmark z ⟨sphere_subset_closedBall hz.1,
      by linarith [hz.2.1],by linarith [hz.2.2]⟩).mpr hz.1
  subst owner
  exact ⟨K,B,P,k,q,b,t,U,W,σ,hK,hKPL,hKO,hPmap,hPsmall,hPmark,
    (hwidths (1 / 2) (by norm_num) (by norm_num)).2,hk,hdis,hcover,ht,hnoK,
    hσ,hσval,hU,hUPL,hUsub,hcap,hmark,hnoU⟩

end PoincareConjecture.M76
