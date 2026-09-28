import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.OriginalRelativeNoL3CenteredNormalizationStep
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.NoL3ZeroExcessRelativeDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalTetrahedralCutFamily












set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.exists_original_finite_relative_noL3_normalization
    {E : Type u} {X ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] [MetricSpace X] [Finite κ]
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
    (hno : HasNoPuncturedSphereComponents e f (R \ ⋃ i, O₀ i)) :
    ∃ (N : κ → Set X) (sN : ∀ i, ChartwisePLSphere e (N i)),
      (∀ i, N i ⊆ g '' K.space) ∧ (∀ i, N i ⊆ interior R) ∧
      Pairwise (fun i j => Disjoint (N i) (N j)) ∧
      Disjoint (⋃ i, N i) (g '' K.vertices) ∧
      (∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (N i) K g a) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((⋃ i, N i) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, N i) g s.1 (A s)) ∧
      totalTetrahedralBoundaryExcess K hK g (⋃ i, N i) = 0 ∧
      Nonempty (PrismBelt.OriginalTetrahedralCutFamily K g (⋃ i, N i)) ∧
      ∃ (O : κ → Set X) (W : ∀ i, (N i × unitInterval) ≃ₜ closure (O i)),
        IsCompact (R \ ⋃ i, O i) ∧ PLDomain e (R \ ⋃ i, O i) ∧
        HasNoPuncturedSphereComponents e f (R \ ⋃ i, O i) ∧
        (∀ i, IsOpen (O i)) ∧ (∀ i, closure (O i) ⊆ interior R) ∧
        Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) ∧
        (∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
        (∀ i z, (W i z : X) ∈ N i ↔ (z.2 : ℝ) = 1/2) ∧
        (∀ i, N i ⊆ closure (O i)) ∧
        ∃ (B : κ × Bool → Set X) (_sB : ∀ j, ChartwisePLSphere e (B j)),
          Pairwise (fun j k => Disjoint (B j) (B k)) ∧
          (∀ j, B j ⊆ closure (O j.1)) ∧
          frontier (R \ ⋃ i, O i) = frontier R ∪ ⋃ j, B j := by
  classical
  have hfi : InjOn f (g '' K.space) := by
    intro x hx y hy hxy
    exact (hreal x (hKR hx)).2.symm.trans
      ((congrArg g hxy).trans (hreal y (hKR hy)).2)
  induction hn : totalTetrahedralBoundaryExcess K hK g (⋃ i, S i)
      using Nat.strong_induction_on generalizing S O₀ B₀ with
  | h n ih =>
    by_cases hz : n = 0
    · refine ⟨S,sS,hS,hSR,hdis,havoid,hedge,hedges,hposition,hn.trans hz,?_,
        O₀,W₀,hQ₀,hQ₀PL,hno,hO₀,hCR₀,hdis₀,hopen₀,hcenter₀,hSC₀,
        B₀,sB₀,hB₀dis,hB₀sub,hfront₀⟩
      apply PrismBelt.exists_original_tetrahedral_cut_family
      intro t ht ht4
      exact hno.exists_original_zero_excess_disks_relative_boundary hRPL.compatible
        K hK g hg hgi Q A hmap hA S sS hS hdis havoid hedges hposition
        hQ₀ hQ₀PL B₀ sB₀ hB₀dis hfront₀ hf hfi O₀ W₀ rfl hO₀ (fun i => (hCR₀ i).trans interior_subset) hdis₀
        hSC₀ hopen₀ hcenter₀ ht ht4
        ((image_mono (K.convexHull_subset_space ht)).trans hKR)
        (boundaryComponentExcess_eq_zero_of_total_eq_zero K hK g (⋃ i, S i) (hn.trans hz) ht ht4)
    obtain ⟨t,ht,ht4,hpositive⟩ := exists_tetrahedron_of_totalBoundaryExcess_ne_zero
      K hK g (⋃ i, S i) (by rwa [hn])
    obtain ⟨N,sN,O,W,B,sB,hNK,hNR,hNdis,hNavoid,hNfinite,hNedge,hNpos,
        hcard,hdecrease,hO,hOdis,hWopen,hWcenter,hNC,hcut,hcutPL,hno',hBdis,hBsub,hfront⟩ :=
      hno.exists_original_relative_centered_normalization_step K hK g hg hgi Q hQ A hmap hA
        S sS hS hdis havoid hedge hedges hposition ht ht4 hR hRPL hSR
        ((image_mono (K.convexHull_subset_space ht)).trans hKR) hf hreal
        O₀ W₀ rfl hQ₀ hQ₀PL hO₀ hCR₀ hdis₀ hopen₀ hcenter₀
        hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ hpositive
    have hlt : totalTetrahedralBoundaryExcess K hK g (⋃ i, N i) < n := by
      rwa [hn] at hdecrease
    exact ih _ hlt N sN hNK hNR hNdis hNavoid hNedge hNfinite hNpos O W
      hcut hcutPL (fun i => (hO i).1) (fun i => (hO i).2)
      hOdis hWopen hWcenter hNC B sB hBdis hBsub hfront hno' rfl

end PoincareConjecture.M76
