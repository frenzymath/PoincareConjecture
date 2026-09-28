import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.PositionedRelativeSphereBound
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ProtectedFamilyEdgeCofacePosition








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
theorem HasNoPuncturedSphereComponents.card_le_original_model_bound
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
    (hRc : IsConnected R)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g)) :
    Fintype.card κ + 1 ≤ Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology R 1) +
      4 * Nat.card (K.FaceOfCard 3) + J.vertices.ncard := by
  classical
  have hfc : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨i,hi⟩ := hRPL.cover x
    have hh := (hf i).continuousOn.comp (e i).continuousOn (fun _ hy => (e i).map_source hy)
    have hh' : ContinuousOn f (e i).source := hh.congr
      (fun y hy => (congrArg f ((e i).left_inv hy)).symm)
    exact hh'.continuousAt ((e i).open_source.mem_nhds hi)
  have hmarkZ : ∀ z ∈ K.space, g z ∈ (interior R)ᶜ ↔ z ∈ J.space := by
    intro z hz
    constructor
    · intro hn
      exact (hmark z hz).mp ⟨subset_closure (hKR ⟨z,hz,rfl⟩),hn⟩
    · intro hj
      exact ((hmark z hz).mpr hj).2
  have hSZ : Disjoint (⋃ i,S i) (interior R)ᶜ :=
    disjoint_left.mpr (fun x hx hn => hn (iUnion_subset hSR hx))
  obtain ⟨F₁,C,hC,hCZ,hFfix,hFPL,_,⟨s₁⟩,havoid₁,hedges₁⟩ :=
    exists_protected_sphere_system_finite_edge_coface_position S sS hdis hRPL.cover hRPL.compatible
      K J hK hJK g hg.continuousOn hgi hstars isOpen_interior.isClosed_compl hmarkZ hSZ
  have hfix : EqOn F₁ id (interior R)ᶜ := fun x hx =>
    hFfix (fun hc => disjoint_left.mp hCZ hc hx)
  obtain ⟨_,sB₁,W₁,_,_,hQeq₁,hCut₁,hCutPL₁,hO₁,hCR₁,hCC₁,_,hstrip₁,hcenter₁,hSC₁,
      hBdis₁,hBsub₁,hfront₁,hno₁⟩ :=
    hno.transport_relative_cut S O₀ sS W₀ rfl hQ₀ hQ₀PL hO₀ hCR₀ hdis₀ hopen₀ hcenter₀
      hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ F₁ hfix hFPL K g hf hg hgi hreal
  have hdis₁ : Pairwise fun i j => Disjoint (F₁ '' S i) (F₁ '' S j) := by
    intro i j hij
    exact (hdis hij).image (F₁.injective.injOn (s := univ))
      (subset_univ _) (subset_univ _)
  have hunion : (⋃ i,F₁ '' S i) = F₁ '' (⋃ i,S i) := image_iUnion.symm
  have hedge₁ : ∀ i a, a ∈ K.faces → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (F₁ '' S i) K g a := by
    intro i a ha hac
    apply HasOriginalEdgeCofaceCharts.of_finite_sphere_system (fun i => F₁ '' S i) s₁ hdis₁
    simpa only [hunion] using (hedges₁ a ha hac).2
  have hbound := (hQeq₁ ▸ hno₁).card_le_original_model_bound_of_edge_position K hK g hg hgi
    Q hQ A hmap hA hR hRPL hKR hf hreal (fun i => F₁ '' S i) s₁
    (fun i => (hSC₁ i).trans (hCR₁ i)) hdis₁
    (by simpa only [hunion] using havoid₁) hedge₁
    (by simpa only [hunion] using fun a ha hac => (hedges₁ a ha hac).1)
    (fun i => F₁ '' O₀ i) W₁ (hQeq₁ ▸ hCut₁) (hQeq₁ ▸ hCutPL₁) hO₁ hCR₁ hCC₁
    hstrip₁ hcenter₁ hSC₁ (fun i => F₁ '' B₀ i) sB₁ hBdis₁ hBsub₁ (hQeq₁ ▸ hfront₁)
    J hJK hpure hmark hfc hRc
  exact hbound

end PoincareConjecture.M76
