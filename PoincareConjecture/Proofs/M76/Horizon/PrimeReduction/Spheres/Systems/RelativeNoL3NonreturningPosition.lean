import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.RelativeCutAmbientTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SimultaneousNoReturningFacePosition

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_relative_noL3_nonreturning_position
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z)
    (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    (hSZ : Disjoint (⋃ i, S i) Z) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    {R Q₀ : Set X} (O : κ → Set X)
    (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O i))
    (hQ₀eq : Q₀ = R \ ⋃ i, O i) (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (hO : ∀ i, IsOpen (O i)) (hCR : ∀ i, closure (O i) ⊆ interior R)
    (hOdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hopen : ∀ i z, (W₀ i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC : ∀ i, S i ⊆ closure (O i))
    (B : κ × Bool → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hBsub : ∀ i, B i ⊆ closure (O i.1))
    (hfront : frontier Q₀ = frontier R ∪ ⋃ i, B i)
    (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    (hprotect : (interior R)ᶜ ⊆ Z) :
    ∃ (F : X ≃ₜ X) (W : Set X),
      IsOpen W ∧ Z ∪ g '' K.vertices ⊆ W ∧
      EqOn F id W ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (∀ i, ChartwisePLSphere e (F '' S i)) ∧
      (Pairwise fun i j => Disjoint (F '' S i) (F '' S j)) ∧
      Disjoint (F '' (⋃ i, S i)) (Z ∪ g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (F '' S i) K g a) ∧
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
        (F '' (⋃ i, S i))).ncard ≤
        ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩ (⋃ i, S i)).ncard ∧
      (∀ s : K.FaceOfCard 3,
        InNonreturningTriangleGraphPosition (Q s) (F '' (⋃ i, S i)) g s.1 (A s)) ∧
      ∃ (sB' : ∀ i, ChartwisePLSphere e (F '' B i))
        (W' : ∀ i, ((F '' S i) × unitInterval) ≃ₜ closure (F '' O i)),
        F '' R = R ∧ EqOn F id (frontier R) ∧
        F '' Q₀ = R \ ⋃ i, F '' O i ∧
        IsCompact (F '' Q₀) ∧ PLDomain e (F '' Q₀) ∧
        (∀ i, IsOpen (F '' O i)) ∧ (∀ i, closure (F '' O i) ⊆ interior R) ∧
        Pairwise (fun i j => Disjoint (closure (F '' O i)) (closure (F '' O j))) ∧
        (∀ i z, (W' i z : X) = F (W₀ i ((F.image (S i)).symm z.1,z.2))) ∧
        (∀ i z, (W' i z : X) ∈ F '' O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
        (∀ i z, (W' i z : X) ∈ F '' S i ↔ (z.2 : ℝ) = 1/2) ∧
        (∀ i, F '' S i ⊆ closure (F '' O i)) ∧
        Pairwise (fun i j => Disjoint (F '' B i) (F '' B j)) ∧
        (∀ i, F '' B i ⊆ closure (F '' O i.1)) ∧
        frontier (F '' Q₀) = frontier R ∪ ⋃ i, F '' B i ∧
        HasNoPuncturedSphereComponents e f (F '' Q₀) := by
  obtain ⟨F,W,hW,hZW,hfix,hF,hFinv,sF,hdisF,havoid,hedge,hcoface,hbound,hpos⟩ :=
    exists_simultaneous_protected_sphere_system_position_without_returns
      S sS hdis hcover he K N hK hNK g hgc hgi hZ hmark hSZ hSV
      hedges hcofaces Q hQ A hmap hA
  have hfixR : EqOn F id (interior R)ᶜ :=
    hfix.mono (hprotect.trans (subset_union_left.trans hZW))
  obtain ⟨_,sB',W',hFR,hFfront,hQeq,hQc,hQpl,hO',hCR',hdis',hWval,hWopen,hWcenter,
      hSCl,hBdis',hBsub',hfront',hno'⟩ :=
    hno.transport_relative_cut S O sS W₀ hQ₀eq hQ₀ hQ₀PL hO hCR hOdis
      hopen hcenter hSC B sB hBdis hBsub hfront F hfixR hF K g hf hg hgi hreal
  exact ⟨F,W,hW,hZW,hfix,hF,hFinv,sF,hdisF,havoid,hedge,hcoface,hbound,hpos,
    sB',W',hFR,hFfront,hQeq,hQc,hQpl,hO',hCR',hdis',hWval,hWopen,hWcenter,
    hSCl,hBdis',hBsub',hfront',hno'⟩

end PoincareConjecture.M76
