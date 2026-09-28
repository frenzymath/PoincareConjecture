import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalModelSphereBound
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.OriginalRelativeNoL3FiniteNormalization
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.InteriorSphereLinks







set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
theorem HasNoPuncturedSphereComponents.card_le_original_model_bound_of_circle_free_position
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
    (hS : ∀ i, S i ⊆ g '' K.space) (hSR : ∀ i, S i ⊆ interior R)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (havoid : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedge : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
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
  let : LocallyPathConnectedSpace (sphere (0 : V3) 1) := unitThreeSphere_lifting_properties.2
  obtain ⟨N,sN,hNK,hNR,hNdis,hNavoid,_,_,hNpos,_,⟨B⟩,O,W,hCut,hCutPL,hno',
      hO,hCR,hCC,hstrip,hcenter,hNC,Sb,sSb,hbdis,_,hfront⟩ :=
    hno.exists_original_finite_relative_noL3_normalization K hK g hg hgi Q hQ A hmap hA
      hR hRPL hKR hf hreal S sS hS hSR hdis havoid hedge hedges hposition O₀ W₀
      hQ₀ hQ₀PL hO₀ hCR₀ hdis₀ hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀
  have hFg : ∀ z ∈ K.space, f (g z) = z := by
    intro z hz
    have hh := hreal (g z) (hKR ⟨z,hz,rfl⟩)
    exact hgi hh.1 hz hh.2
  let W' (i) : ((sphere (0 : V3) 1) × unitInterval) ≃ₜ closure (O i) :=
    ((sN i).parametrization.prodCongr (Homeomorph.refl unitInterval)).trans (W i)
  have hSO (i) : N i ⊆ O i := by
    intro x hx
    let z := (W i).symm ⟨x,hNC i hx⟩
    have hz : (W i z : X) = x := congrArg Subtype.val ((W i).apply_symm_apply _)
    have ht : (z.2 : ℝ) = 1/2 := (hcenter i z).mp (hz.symm ▸ hx)
    exact hz ▸ (hstrip i z).mpr (by rw [ht]; norm_num)
  exact B.card_le_original_model_homology_bound K J hK hJK hpure g hg
    (mapsTo_iff_image_subset.mpr hKR) f hfc (fun _ hx => (hreal _ hx).1)
    hFg (fun _ hx => (hreal _ hx).2) hf hmark N sN hNdis (iUnion_subset hNR)
    Q A hmap hA hNavoid hNpos O W' hO (fun i => (hCR i).trans interior_subset) hSO
    (fun i z => hcenter i ((sN i).parametrization z.1,z.2))
    (fun i z => hstrip i ((sN i).parametrization z.1,z.2))
    hCC rfl hCut hCutPL hno' Sb sSb hbdis hfront hR hRPL hRc

end PoincareConjecture.M76
