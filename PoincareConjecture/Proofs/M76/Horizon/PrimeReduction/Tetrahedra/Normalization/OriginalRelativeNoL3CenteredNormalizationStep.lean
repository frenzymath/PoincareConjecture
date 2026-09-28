import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.OriginalRelativeNoL3NormalizationStep
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeFamilyCenteredExchange









set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.exists_original_relative_centered_normalization_step
    {E : Type u} {X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [MetricSpace X]
    [Finite κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s j, (e j).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (havoid : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedge : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {R Q₀ : Set X} (hR : IsCompact R) (hRPL : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hTR : g '' convexHull ℝ (t : Set E) ⊆ R)
    (hf : ∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (O₀ : κ → Set X) (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O₀ i))
    (hQ₀eq : Q₀ = R \ ⋃ i, O₀ i) (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (hO₀ : ∀ i, IsOpen (O₀ i)) (hCR₀ : ∀ i, closure (O₀ i) ⊆ interior R)
    (hdis₀ : Pairwise fun i j => Disjoint (closure (O₀ i)) (closure (O₀ j)))
    (hopen₀ : ∀ i z, (W₀ i z : X) ∈ O₀ i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter₀ : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : ∀ i, S i ⊆ closure (O₀ i))
    (B₀ : κ × Bool → Set X) (sB₀ : ∀ j, ChartwisePLSphere e (B₀ j))
    (hB₀dis : Pairwise fun j k => Disjoint (B₀ j) (B₀ k))
    (hB₀sub : ∀ j, B₀ j ⊆ closure (O₀ j.1))
    (hfront₀ : frontier Q₀ = frontier R ∪ ⋃ j, B₀ j)
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    (hpositive : boundaryComponentExcess (⋃ i, S i) (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) ≠ 0) :
    ∃ (S' : κ → Set X) (sS' : ∀ j, ChartwisePLSphere e (S' j))
      (O' : κ → Set X) (W' : ∀ j, (S' j × unitInterval) ≃ₜ closure (O' j))
      (B' : κ × Bool → Set X) (_sB' : ∀ j, ChartwisePLSphere e (B' j)),
      (∀ j, S' j ⊆ g '' K.space) ∧ (∀ j, S' j ⊆ interior R) ∧
      Pairwise (fun j k => Disjoint (S' j) (S' k)) ∧
      Disjoint (⋃ j, S' j) (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((⋃ j, S' j) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ j a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S' j) K g a) ∧
      (∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ j, S' j) g s.1 (A s)) ∧
      Nat.card (Set.range S') = Nat.card κ ∧
      totalTetrahedralBoundaryExcess K hK g (⋃ j, S' j) <
        totalTetrahedralBoundaryExcess K hK g (⋃ j, S j) ∧
      (∀ j, IsOpen (O' j) ∧ closure (O' j) ⊆ interior R) ∧
      Pairwise (fun j k => Disjoint (closure (O' j)) (closure (O' k))) ∧
      (∀ j z, (W' j z : X) ∈ O' j ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ j z, (W' j z : X) ∈ S' j ↔ (z.2 : ℝ) = 1/2) ∧
      (∀ j, S' j ⊆ closure (O' j)) ∧
      IsCompact (R \ ⋃ j, O' j) ∧ PLDomain e (R \ ⋃ j, O' j) ∧
      HasNoPuncturedSphereComponents e f (R \ ⋃ j, O' j) ∧
      Pairwise (fun j k => Disjoint (B' j) (B' k)) ∧
      (∀ j, B' j ⊆ closure (O' j.1)) ∧
      frontier (R \ ⋃ j, O' j) = frontier R ∪ ⋃ j, B' j := by
  classical
  obtain ⟨i,new,b,hs,hspace,hinside,hdis',havoid',hfinite,hcofaces,hposition',hcard,hdecrease,
      O,W,B,sB,a,hcut,hcutPL,hnoCut,hO,hOdis,hWopen,hWcenter,hSC,hfront,hBdis,hBsub,
      hC,hCconn,hCPL,hSiC,hOiC,U,WU,σ,hσ,hσval,hU,hUPL,hUC,hcapfront,hmark,hnoC,hnoA⟩ :=
    hno.exists_original_relative_selected_normalization_step K hK g hg hgi Q hQ A hmap hA
      S sS hS hdis havoid hedge hedges hposition ht ht4 hR hRPL hSR hTR hf hreal
      O₀ W₀ hQ₀eq hQ₀ hQ₀PL hO₀ hCR₀ hdis₀ hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ hpositive
  have cap : ChartwisePLSphere e (new b) := by
    simpa [selectedCircleSurgeryFamily] using ((Classical.choice hs) i)
  obtain ⟨Oc,Hc,sS',W',G,sG,hOc,hOcC,hHcO,hHcS,hO',hO'dis,hW'O,hW'S,hS'C,
      hunchanged,hS'dis,hcut',hcutPL',hno',hGdis,hGsub,hGfront⟩ :=
    hnoA.exists_fixed_relative_family_centered_exchange O S W hR hRPL hcutPL
      (fun j => (hO j).1) (fun j => (hO j).2.2.2) hOdis hWopen hWcenter hSC sS
      B sB hBdis hBsub hfront i a hC hCPL cap WU σ hσ hσval b
      (hcapfront.trans hU.isClosed.frontier_subset) hUC hmark hnoC K g hf hg hgi hreal
  exact ⟨Function.update S i (new b),sS',Function.update O i Oc,W',G,sG,
    hspace,hinside,hdis',havoid',hfinite,hcofaces,hposition',hcard,hdecrease,
    hO',hO'dis,hW'O,hW'S,hS'C,hcut',hcutPL',hno',hGdis,hGsub,hGfront⟩

end PoincareConjecture.M76
