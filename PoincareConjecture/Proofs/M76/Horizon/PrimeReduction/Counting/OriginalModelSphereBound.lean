import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalNonexceptionalCutHomology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.PrescribedCollarComponentCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CenteredCollarBase

set_option autoImplicit false
open Set Metric Geometry CategoryTheory Limits
namespace PoincareConjecture.M76.PrismBelt
universe u
local notation "V3" => (Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
theorem OriginalTetrahedralCutFamily.card_le_original_model_homology_bound
    {E X κ : Type u} {A ι ν : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace A] [LocallyPathConnectedSpace A]
    [Fintype κ] [DecidableEq κ] [Finite ν] {e : ι → OpenPartialHomeomorph X V3} {R Qcut : Set X}
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hJK : J ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgR : MapsTo g K.space R)
    (F : X → E) (hFc : Continuous F) (hFK : MapsTo F R K.space)
    (hFg : ∀ x ∈ K.space, F (g x) = x) (hgF : ∀ x ∈ R, g (F x) = x)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hmark : ∀ z ∈ K.space, g z ∈ frontier R ↔ z ∈ J.space)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (hSR : (⋃ i,S i) ⊆ interior R)
    (B : OriginalTetrahedralCutFamily K g (⋃ i,S i))
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (a : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (ha : ∀ s, EqOn ((Q s) ∘ g) (a s) (convexHull ℝ (s.1 : Set E)))
    (havoid : Disjoint (⋃ i,S i) (g '' K.vertices))
    (hposition : ∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i,S i) g s.1 (a s))
    (O : κ → Set X) (W : ∀ i, (A × unitInterval) ≃ₜ closure (O i))
    (hO : ∀ i, IsOpen (O i)) (hCR : ∀ i, closure (O i) ⊆ R)
    (hSO : ∀ i, S i ⊆ O i)
    (hcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hstrip : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hCC : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hQeq : Qcut = R \ ⋃ i,O i) (hQ : IsCompact Qcut) (hQPL : PLDomain e Qcut)
    (hno : HasNoPuncturedSphereComponents e F Qcut)
    (Sb : ν → Set X) (sSb : ∀ i, ChartwisePLSphere e (Sb i))
    (hbdis : Pairwise fun i j => Disjoint (Sb i) (Sb j))
    (hfront : frontier Qcut = frontier R ∪ ⋃ i,Sb i)
    (hR : IsCompact R) (hRPL : PLDomain e R) (hRc : IsConnected R) :
    Fintype.card κ + 1 ≤ Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology R 1) +
      4 * Nat.card (K.FaceOfCard 3) + J.vertices.ncard := by
  classical
  let M := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  obtain ⟨_,_,_,_,hzero⟩ := B.exists_nonexceptional_cut_homology K J hK hJK hpure
    g hg hgR F hFc hFK hFg hgF hF hmark S sS hdis hSR Q a hmap ha havoid hposition
    O W hO hCR hSO hcenter hstrip hCC hQeq hQ hQPL hno Sb sSb hbdis hfront M
  choose Y hY using fun i => exists_centered_collar_base_homeomorph (W i)
    ((hSO i).trans subset_closure) (hcenter i)
  let W' (i) : (S i × unitInterval) ≃ₜ closure (O i) :=
    ((Y i).symm.prodCongr (Homeomorph.refl unitInterval)).trans (W i)
  have hstrip' (i) (z) : (W' i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1 :=
    hstrip i ((Y i).symm z.1,z.2)
  obtain ⟨D,hD,hcount⟩ := exists_prescribed_collar_zero_component_count R Qcut hR hRPL hRc
    S sS O W' hQeq hQ hQPL hO hCR hCC hstrip'
  have hz : {v | IsZero (ModTwoMayerVietoris.homology (D v) 1)}.ncard ≤
      4 * Nat.card (K.FaceOfCard 3) + J.vertices.ncard := hzero D hD
  omega

end PoincareConjecture.M76.PrismBelt
