import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.OriginalFamilyCocore
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FamilyNoL3CocoreFree








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Square" => Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)
local notation "Cube" => Set.prod Square (Icc (-1 : ℝ) 1)
local notation "OpenCube" => Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-1 : ℝ) 1)

section
variable {ι κ α β E : Type*} [Fintype ι] [Fintype κ] [Finite β] [DecidableEq β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
local notation "X" => LatticeHandleAmbient ι κ L
local notation "R" => latticeHandleDomain ι κ L

theorem HamiltonMarkedProtectedBall.exists_original_family_noL3_cocore_free
    {e : α → OpenPartialHomeomorph X V3} {f : X → E} {D Q₀ : Set X}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e R)
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 2)
    (O₀ S : β → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O₀ i))
    (hQ₀eq : Q₀ = R \ ⋃ i, O₀ i) (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (hO₀ : ∀ i, IsOpen (O₀ i)) (hCR₀ : ∀ i, closure (O₀ i) ⊆ interior R)
    (hdis₀ : Pairwise fun i j => Disjoint (closure (O₀ i)) (closure (O₀ j)))
    (hopen₀ : ∀ i z, (W₀ i z : X) ∈ O₀ i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter₀ : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : ∀ i, S i ⊆ closure (O₀ i))
    (B₀ : β × Bool → Set X) (sB₀ : ∀ i, ChartwisePLSphere e (B₀ i))
    (hB₀dis : Pairwise fun i j => Disjoint (B₀ i) (B₀ j))
    (hB₀sub : ∀ i, B₀ i ⊆ closure (O₀ i.1))
    (hfront₀ : frontier Q₀ = frontier R ∪ ⋃ i, B₀ i)
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x) :
    ∃ (p : P3 → X) (t : ℝ),
      t ∈ Ioo (-(1/2 : ℝ)) (1/2) ∧
      PolyhedralPLInCharts e p Cube ∧ InjOn p Cube ∧ p '' Cube = D ∧
      (∀ z ∈ Cube, p z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1) ∧
      MapsTo p OpenCube (interior R) ∧
      ∃ (S' : β → Set X) (_sS' : ∀ i, ChartwisePLSphere e (S' i)),
        Pairwise (fun i j => Disjoint (S' i) (S' j)) ∧ (∀ i, S' i ⊆ interior R) ∧
        Disjoint (⋃ i, S' i) (p '' (Square ×ˢ {t})) ∧
        ∃ (O' : β → Set X) (W' : ∀ i, (S' i × unitInterval) ≃ₜ closure (O' i))
          (B' : β × Bool → Set X) (_sB' : ∀ i, ChartwisePLSphere e (B' i)),
          (∀ i, IsOpen (O' i) ∧ closure (O' i) ⊆ interior R) ∧
          Pairwise (fun i j => Disjoint (closure (O' i)) (closure (O' j))) ∧
          (∀ i z, (W' i z : X) ∈ O' i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
          (∀ i z, (W' i z : X) ∈ S' i ↔ (z.2 : ℝ) = 1/2) ∧
          (∀ i, S' i ⊆ closure (O' i)) ∧
          IsCompact (R \ ⋃ i, O' i) ∧ PLDomain e (R \ ⋃ i, O' i) ∧
          HasNoPuncturedSphereComponents e f (R \ ⋃ i, O' i) ∧
          Pairwise (fun i j => Disjoint (B' i) (B' j)) ∧
          (∀ i, B' i ⊆ closure (O' i.1)) ∧ frontier (R \ ⋃ i, O' i) = frontier R ∪ ⋃ i, B' i := by
  have hdis : Pairwise fun i j => Disjoint (S i) (S j) :=
    fun i j hij => (hdis₀ hij).mono (hSC₀ i) (hSC₀ j)
  have hSR : ∀ i, S i ⊆ interior R := fun i => (hSC₀ i).trans (hCR₀ i)
  obtain ⟨p,Q,J,t,ht,hp,hpi,hpD,hQs,hQt,hQinv,hQ,hJ,hJQ,hJcv,hJR,
      hall,_,hinner,hpres,hinside,hcross,_,hproper⟩ :=
    b.exists_original_family_cocore he hdim hi S sS hdis hSR
  obtain ⟨S',sS',hdis',hSR',hsupport,hfree,hcut⟩ :=
    exists_family_noL3_cocore_free O₀ S sS hdis W₀ hQ₀eq hQ₀ hQ₀PL
      hO₀ hCR₀ hdis₀ hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ hno
      (isCompact_latticeHandleDomain ι κ L) he hSR K g hf hg hgi hreal
      Q hQ J hJ hJQ hJcv hJR markedProductCoordinates t hpres hinside hcross
  have hsliceCube : Square ×ˢ {t} ⊆ Cube := by
    intro z hz
    have hzt : z.2 = t := hz.2
    exact ⟨hz.1,by constructor <;> linarith [ht.1,ht.2]⟩
  have hcapture : ∀ z ∈ Square ×ˢ {t}, p z ∈ ⋃ i, S' i →
      markedProductCoordinates.symm z ∈ interior J.space := by
    apply cocore_contact_capture_of_supported_subset p hpi Q markedProductCoordinates
      (fun _ hx => hJQ (interior_subset hx)) hQt hQinv _ hsliceCube ?_ hsupport
    intro z hz hzS
    have hzt : z.2 = t := hz.2
    exact hall z (hsliceCube hz) (hzt ▸ ht) hzS
  refine ⟨p,t,ht,hp,hpi,hpD,hproper,hinner,S',sS',hdis',hSR',?_,hcut⟩
  exact disjoint_physical_cocore_of_empty_chart_section _ p Q markedProductCoordinates
    J.space hJQ hQt hQinv t (fun z hz hzS => interior_subset (hcapture z hz hzS)) hfree

end
end PoincareConjecture.M76

