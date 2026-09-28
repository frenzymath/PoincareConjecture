import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCutComparison








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_marked_cut_from_relative_collars
    {X E ι κ : Type*} [MetricSpace X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R Q₀ : Set X}
    (O₀ S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
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
    (hR : IsCompact R) (he : PLDomain e R) (hSR : ∀ i, S i ⊆ interior R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    {U : Set X} (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ d : MarkedSphereCut e R κ, d.spheres = S ∧
      (∀ i, closure (d.collar i) ⊆ U) ∧ Q₀ ⊆ d.carrier ∧
      HasNoPuncturedSphereComponents e f d.carrier := by
  classical
  have hSO (i : κ) : S i ⊆ O₀ i := by
    intro x hx
    obtain ⟨z,hz⟩ := (W₀ i).surjective ⟨x,hSC₀ i hx⟩
    have hval : (W₀ i z : X) = x := congrArg Subtype.val hz
    have ht : (z.2 : ℝ) = 1/2 := (hcenter₀ i z).mp (hval.symm ▸ hx)
    have ho := (hopen₀ i z).mpr (by rw [ht]; norm_num)
    exact hval ▸ ho
  obtain ⟨d,hs,hsmall⟩ := exists_marked_sphere_cut S sS hdis hR he hSR
    (hU.inter (isOpen_iUnion hO₀))
    (fun i x hx => ⟨hSU i hx,mem_iUnion.mpr ⟨i,hSO i hx⟩⟩)
  have hnest : Q₀ ⊆ d.carrier := by
    intro x hx
    have hh := hQ₀eq.subset hx
    refine ⟨hh.1,?_⟩
    intro hd
    obtain ⟨i,hi⟩ := mem_iUnion.mp hd
    exact hh.2 (hsmall i (subset_closure hi)).2
  let cuts : Bool → Set X := fun b => if b then d.carrier else Q₀
  let collars : Bool → κ → Set X := fun b => if b then d.collar else O₀
  let ports : Bool → κ × Bool → Set X := fun b => if b then d.ports else B₀
  let A (i : κ) : S i ≃ₜ d.spheres i := Homeomorph.setCongr (congrFun hs i).symm
  let W : ∀ b i, (S i × unitInterval) ≃ₜ closure (collars b i) := fun b i => by
    cases b
    · exact W₀ i
    · exact ((A i).prodCongr (Homeomorph.refl unitInterval)).trans (d.product i)
  have hcut (b : Bool) : cuts b = R \ ⋃ i,collars b i := by
    cases b
    · exact hQ₀eq
    · rfl
  have hc (b : Bool) : IsCompact (cuts b) := by
    cases b
    · exact hQ₀
    · exact d.compactCut
  have hpl (b : Bool) : PLDomain e (cuts b) := by
    cases b
    · exact hQ₀PL
    · exact d.plCut
  have hinside (b : Bool) (i : κ) : closure (collars b i) ⊆ interior R := by
    cases b
    · exact hCR₀ i
    · exact d.collarInterior i
  have hdisjoint (b : Bool) : Pairwise fun i j =>
      Disjoint (closure (collars b i)) (closure (collars b j)) := by
    cases b
    · exact hdis₀
    · exact d.collarDisjoint
  have hopen (b : Bool) (i : κ) (z) :
      (W b i z : X) ∈ collars b i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1 := by
    cases b
    · exact hopen₀ i z
    · exact d.openCoordinates i (A i z.1,z.2)
  have hcenter (b : Bool) (i : κ) (z) :
      (W b i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2 := by
    cases b
    · exact hcenter₀ i z
    · exact (Set.ext_iff.mp (congrFun hs i) _).symm.trans
        (d.centerCoordinates i (A i z.1,z.2))
  have hclosure (b : Bool) (i : κ) : S i ⊆ closure (collars b i) := by
    cases b
    · exact hSC₀ i
    · exact (congrFun hs i).symm.subset.trans (d.sphereClosure i)
  have spl (b : Bool) (j) : ChartwisePLSphere e (ports b j) := by
    cases b
    · exact sB₀ j
    · exact d.portPL j
  have hpdis (b : Bool) : Pairwise fun i j => Disjoint (ports b i) (ports b j) := by
    cases b
    · exact hB₀dis
    · exact d.portDisjoint
  have hpsub (b : Bool) (j) : ports b j ⊆ closure (collars b j.1) := by
    cases b
    · exact hB₀sub j
    · exact d.portClosure j
  have hfront (b : Bool) : frontier (cuts b) = frontier R ∪ ⋃ i, ports b i := by
    cases b
    · exact hfront₀
    · exact d.frontierCut
  exact ⟨d,hs,(fun i => (hsmall i).trans inter_subset_left),hnest,
    hno.mono_original_collar_cut_relative_boundary R hR.isClosed cuts collars S W hcut
      hc hpl hinside hdisjoint hopen hcenter hclosure ports spl hpdis hpsub hfront
      hnest K g hg hgi hreal⟩

end PoincareConjecture.M76
