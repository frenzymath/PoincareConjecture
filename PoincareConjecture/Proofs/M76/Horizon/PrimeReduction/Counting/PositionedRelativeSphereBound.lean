import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.NormalizedRelativeSphereBound
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.RelativeNoL3NonreturningPosition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalRelativeNoL3CircleFreeTriangles








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
theorem HasNoPuncturedSphereComponents.card_le_original_model_bound_of_edge_position
    {E X κ : Type u} {ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] [MetricSpace X] [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s j, (e j).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    {R : Set X} (hR : IsCompact R) (hRPL : PLDomain e R)
    (hKR : g '' K.space ⊆ R)
    (hf : ∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSR : ∀ i, S i ⊆ interior R)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (havoid : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedge : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (O₀ : κ → Set X) (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O₀ i))
    (hQ₀ : IsCompact (R \ ⋃ i, O₀ i)) (hQ₀PL : PLDomain e (R \ ⋃ i, O₀ i))
    (hO₀ : ∀ i, IsOpen (O₀ i)) (hCR₀ : ∀ i, closure (O₀ i) ⊆ interior R)
    (hdis₀ : Pairwise fun i j => Disjoint (closure (O₀ i)) (closure (O₀ j)))
    (hopen₀ : ∀ i z, (W₀ i z : X) ∈ O₀ i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter₀ : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : ∀ i, S i ⊆ closure (O₀ i))
    (B₀ : κ × Bool → Set X) (sB₀ : ∀ j, ChartwisePLSphere e (B₀ j))
    (hB₀dis : Pairwise fun j k => Disjoint (B₀ j) (B₀ k))
    (hB₀sub : ∀ j, B₀ j ⊆ closure (O₀ j.1))
    (hfront₀ : frontier (R \ ⋃ i, O₀ i) = frontier R ∪ ⋃ j, B₀ j)
    (hno : HasNoPuncturedSphereComponents e f (R \ ⋃ i, O₀ i))
    (J : SimplicialComplex ℝ E) (hJK : J ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hmark : ∀ z ∈ K.space, g z ∈ frontier R ↔ z ∈ J.space)
    (hfc : Continuous f) (hRc : IsConnected R) :
    Fintype.card κ + 1 ≤ Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology R 1) +
      4 * Nat.card (K.FaceOfCard 3) + J.vertices.ncard := by
  classical
  have hcover := hRPL.cover
  have hmarkZ : ∀ z ∈ K.space, g z ∈ (interior R)ᶜ ↔ z ∈ J.space := by
    intro z hz
    constructor
    · intro hn
      exact (hmark z hz).mp ⟨subset_closure (hKR ⟨z,hz,rfl⟩),hn⟩
    · intro hj
      exact ((hmark z hz).mpr hj).2
  have hSZ : Disjoint (⋃ i,S i) (interior R)ᶜ :=
    disjoint_left.mpr (fun x hx hn => hn (iUnion_subset hSR hx))
  obtain ⟨F₁,_,_,_,_,_,_,⟨s₁⟩,hdis₁,havoid₁,hedges₁,hcofaces₁,_,hpos₁,
      sB₁,W₁,_,_,hQeq₁,hCut₁,hCutPL₁,hO₁,hCR₁,hCC₁,_,hstrip₁,hcenter₁,hSC₁,
      hBdis₁,hBsub₁,hfront₁,hno₁⟩ :=
    exists_relative_noL3_nonreturning_position S sS hdis hcover hRPL.compatible
      K J hK hJK g hg.continuousOn hgi isOpen_interior.isClosed_compl hmarkZ
      hSZ havoid hedges hedge Q hQ A hmap hA O₀ W₀ rfl hQ₀ hQ₀PL hO₀ hCR₀
      hdis₀ hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ f hf hg hreal hno subset_rfl
  have hunion : (⋃ i,F₁ '' S i) = F₁ '' (⋃ i,S i) := image_iUnion.symm
  obtain ⟨S₂,s₂,hdis₂,_,hSR₂,havoid₂,hedges₂,hcofaces₂,_,_,hpos₂,
      O₂,W₂,B₂,sB₂,hO₂,hCC₂,hstrip₂,hcenter₂,hSC₂,hCut₂,hCutPL₂,hno₂,hBdis₂,hBsub₂,hfront₂⟩ :=
    exists_original_relative_noL3_circle_free_triangles (Z := (interior R)ᶜ)
      (fun i => F₁ '' S i) s₁ hdis₁
      K J hK hJK g hg hgi hKR hR hRPL (fun i => (hSC₁ i).trans (hCR₁ i))
      (fun _ hx => hx.2) isOpen_interior.isClosed_compl hmarkZ hf hreal
      (fun i => F₁ '' O₀ i) W₁ hQeq₁ hCut₁ hCutPL₁ hO₁ hCR₁ hCC₁ hstrip₁ hcenter₁ hSC₁
      (fun i => F₁ '' B₀ i) sB₁ hBdis₁ hBsub₁ hfront₁ hno₁
      (by simpa only [hunion] using havoid₁.mono_right subset_union_left)
      (by simpa only [hunion] using havoid₁.mono_right subset_union_right)
      (by simpa only [hunion] using hedges₁) hcofaces₁ hRPL.compatible hcover Q hQ A hmap hA
      (by simpa only [hunion] using hpos₁)
  have hS₂ : ∀ i, S₂ i ⊆ g '' K.space := by
    intro i x hx
    have hh := hreal x (interior_subset (hSR₂ i hx))
    exact ⟨f x,hh.1,hh.2⟩
  exact hno₂.card_le_original_model_bound_of_circle_free_position K hK g hg hgi Q hQ A hmap hA
    hR hRPL hKR hf hreal S₂ s₂ hS₂ hSR₂ hdis₂ havoid₂ hcofaces₂ hedges₂ hpos₂
    O₂ W₂ hCut₂ hCutPL₂ (fun i => (hO₂ i).1) (fun i => (hO₂ i).2) hCC₂ hstrip₂ hcenter₂
    hSC₂ B₂ sB₂ hBdis₂ hBsub₂ hfront₂ J hJK hpure hmark hfc hRc

end PoincareConjecture.M76
