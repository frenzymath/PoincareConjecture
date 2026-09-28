import PoincareConjecture.Proofs.M02.Topology.EuclideanBoxCover
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenCapProperty
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenCapUnion
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenCapDirectedInduction
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenCapPropertyHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Basic








set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe v

namespace PoincareConjecture.Proofs.M02.Topology

private abbrev E := EuclideanSpace Real (Fin 3)

variable {X : Type} [TopologicalSpace X]

def integralChartBox (e : OpenPartialHomeomorph X E) (a b : Fin 3 → Real) : Set X :=
  e.source ∩ e ⁻¹' euclideanThreeOpenBox a b

theorem integralChartBox_isOpen (e : OpenPartialHomeomorph X E) (a b : Fin 3 → Real) :
    IsOpen (integralChartBox e a b) :=
  e.isOpen_inter_preimage (euclideanThreeOpenBox_isOpen a b)

theorem integralChartBox_image (e : OpenPartialHomeomorph X E) (a b : Fin 3 → Real)
    (hB : euclideanThreeOpenBox a b ⊆ e.target) :
    e '' integralChartBox e a b = euclideanThreeOpenBox a b := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    refine ⟨e.symm y, ⟨e.map_target (hB hy), ?_⟩, e.right_inv (hB hy)⟩
    change e (e.symm y) ∈ euclideanThreeOpenBox a b
    rw [e.right_inv (hB hy)]
    exact hy

def integralChartBoxHomeomorph (e : OpenPartialHomeomorph X E) (a b : Fin 3 → Real)
    (hB : euclideanThreeOpenBox a b ⊆ e.target) :
    integralChartBox e a b ≃ₜ euclideanThreeOpenBox a b :=
  e.homeomorphOfImageSubsetSource inter_subset_left (integralChartBox_image e a b hB)

theorem integralChartBox_inter (e : OpenPartialHomeomorph X E)
    (a b c d : Fin 3 → Real) :
    integralChartBox e a b ∩ integralChartBox e c d =
      integralChartBox e (fun i => max (a i) (c i)) (fun i => min (b i) (d i)) := by
  dsimp only [integralChartBox]
  rw [← euclideanThreeOpenBox_inter]
  ext x
  simp only [mem_inter_iff, mem_preimage]
  tauto

def integralChartBoxFiniteUnion {I : Type v} (e : OpenPartialHomeomorph X E)
    (s : Finset I) (a b : I → Fin 3 → Real) : Set X :=
  ⋃ i ∈ s, integralChartBox e (a i) (b i)

theorem integralChartBoxFiniteUnion_isOpen {I : Type v}
    (e : OpenPartialHomeomorph X E) (s : Finset I) (a b : I → Fin 3 → Real) :
    IsOpen (integralChartBoxFiniteUnion e s a b) :=
  isOpen_iUnion fun i => isOpen_iUnion fun _ => integralChartBox_isOpen e (a i) (b i)

def integralChartBoxesInside (e : OpenPartialHomeomorph X E) (W : Set X) :=
  {p : (Fin 3 → Real) × (Fin 3 → Real) // euclideanThreeOpenBox p.1 p.2 ⊆ e '' W}

def integralChartBoxCoverStage (e : OpenPartialHomeomorph X E) (W : Set X)
    (s : Finset (integralChartBoxesInside e W)) : Set X :=
  integralChartBoxFiniteUnion e s (fun p => p.1.1) (fun p => p.1.2)

theorem integralChartBoxCoverStage_isOpen (e : OpenPartialHomeomorph X E) (W : Set X)
    (s : Finset (integralChartBoxesInside e W)) :
    IsOpen (integralChartBoxCoverStage e W s) :=
  integralChartBoxFiniteUnion_isOpen e s _ _

theorem integralChartBoxCoverStage_subset (e : OpenPartialHomeomorph X E)
    (W : Set X) (hWs : W ⊆ e.source) (s : Finset (integralChartBoxesInside e W)) :
    integralChartBoxCoverStage e W s ⊆ W := by
  intro x hx
  obtain ⟨p, _, hp⟩ := mem_iUnion₂.mp hx
  obtain ⟨y, hyW, hy⟩ := p.2 hp.2
  have hyx : y = x := e.injOn (hWs hyW) hp.1 hy
  exact hyx ▸ hyW

theorem integralChartBoxCoverStage_mono (e : OpenPartialHomeomorph X E) (W : Set X)
    {s t : Finset (integralChartBoxesInside e W)} (hst : s ⊆ t) :
    integralChartBoxCoverStage e W s ⊆ integralChartBoxCoverStage e W t := by
  intro x hx
  obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨p, hst hp, hx⟩

theorem integralChartBoxCoverStage_directed (e : OpenPartialHomeomorph X E) (W : Set X) :
    Directed (fun A B : Set X => A ⊆ B) (integralChartBoxCoverStage e W) := by
  classical
  intro s t
  exact ⟨s ∪ t, integralChartBoxCoverStage_mono e W Finset.subset_union_left,
    integralChartBoxCoverStage_mono e W Finset.subset_union_right⟩

theorem integralChartBoxCoverStage_iUnion (e : OpenPartialHomeomorph X E)
    (W : Set X) (hW : IsOpen W) (hWs : W ⊆ e.source) :
    (⋃ s, integralChartBoxCoverStage e W s) = W := by
  classical
  apply Set.Subset.antisymm
  · exact iUnion_subset (integralChartBoxCoverStage_subset e W hWs)
  · intro x hx
    have himage : IsOpen (e '' W) := e.isOpen_image_of_subset_source hW hWs
    obtain ⟨a, b, hxab, habW⟩ := exists_euclideanThreeOpenBox_subset himage ⟨x, hx, rfl⟩
    let p : integralChartBoxesInside e W := ⟨(a, b), habW⟩
    refine mem_iUnion.mpr ⟨{p}, mem_iUnion₂.mpr ⟨p, Finset.mem_singleton_self p, ?_⟩⟩
    exact ⟨hWs hx, hxab⟩

section CapProperty

variable [T2Space X] [RegularSpace X] [LocallyCompactSpace X]
  (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
  (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
  (hlocalX : ∀ x : X, ∃ B : Set X, IsOpen B ∧ x ∈ B ∧
    ∃ c : integralSupportHomology B 3, ∀ y : X, ∀ hy : y ∈ B,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)

private theorem chartOpenCapProperty_congr {U V : Set X}
    (h : U = V) (hU : IsOpen U) (hV : IsOpen V)
    (hprop : integralOpenCapProperty hDX omegaX hlocalX U hU) :
    integralOpenCapProperty hDX omegaX hlocalX V hV := by
  subst V
  exact hprop

private theorem finite_chart_box_cap_property
    (e : OpenPartialHomeomorph X E)
    (hbox : ∀ (a b : Fin 3 → Real), euclideanThreeOpenBox a b ⊆ e.target →
      integralOpenCapProperty hDX omegaX hlocalX (integralChartBox e a b)
        (integralChartBox_isOpen e a b))
    {I : Type v} (s : Finset I) (a b : I → Fin 3 → Real)
    (hB : ∀ i, euclideanThreeOpenBox (a i) (b i) ⊆ e.target) :
    integralOpenCapProperty hDX omegaX hlocalX (integralChartBoxFiniteUnion e s a b)
      (integralChartBoxFiniteUnion_isOpen e s a b) := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
      simpa only [integralChartBoxFiniteUnion, Finset.notMem_empty,
        iUnion_of_empty, iUnion_empty] using integralOpenCapProperty_empty hDX omegaX hlocalX
  | @insert i s hi ih =>
      let a' : I → Fin 3 → Real := fun j k => max (a i k) (a j k)
      let b' : I → Fin 3 → Real := fun j k => min (b i k) (b j k)
      have hB' : ∀ j, euclideanThreeOpenBox (a' j) (b' j) ⊆ e.target := by
        intro j
        change euclideanThreeOpenBox (fun k => max (a i k) (a j k))
          (fun k => min (b i k) (b j k)) ⊆ e.target
        rw [← euclideanThreeOpenBox_inter]
        exact Set.inter_subset_left.trans (hB i)
      have hI : integralChartBox e (a i) (b i) ∩ integralChartBoxFiniteUnion e s a b =
          integralChartBoxFiniteUnion e s a' b' := by
        simp only [integralChartBoxFiniteUnion, inter_iUnion₂,
          integralChartBox_inter, a', b']
      have hIP := chartOpenCapProperty_congr hDX omegaX hlocalX hI.symm
        (integralChartBoxFiniteUnion_isOpen e s a' b')
        ((integralChartBox_isOpen e (a i) (b i)).inter
          (integralChartBoxFiniteUnion_isOpen e s a b)) (ih a' b' hB')
      have hP := integralOpenCapProperty_union hDX omegaX hlocalX
        (integralChartBox e (a i) (b i)) (integralChartBoxFiniteUnion e s a b)
        (integralChartBox_isOpen e (a i) (b i))
        (integralChartBoxFiniteUnion_isOpen e s a b)
        (hbox (a i) (b i) (hB i)) (ih a b hB) hIP
      have hS : integralChartBox e (a i) (b i) ∪ integralChartBoxFiniteUnion e s a b =
          integralChartBoxFiniteUnion e (insert i s) a b := by
        simp only [integralChartBoxFiniteUnion, Finset.set_biUnion_insert]
      exact chartOpenCapProperty_congr hDX omegaX hlocalX hS _ _ hP

theorem integralOpenCapProperty_of_chart
    (hgenX : ∀ x : X, ∃ g : Int ≃ₗ[Int]
      integralSupportHomology ({x} : Set X) 3, g 1 = omegaX x)
    (e : OpenPartialHomeomorph X E)
    (W : Set X) (hW : IsOpen W) (hWs : W ⊆ e.source) :
    integralOpenCapProperty hDX omegaX hlocalX W hW := by
  have hbox (a b : Fin 3 → Real) (hB : euclideanThreeOpenBox a b ⊆ e.target) :
      integralOpenCapProperty hDX omegaX hlocalX (integralChartBox e a b)
        (integralChartBox_isOpen e a b) := by
    rcases (euclideanThreeOpenBox a b).eq_empty_or_nonempty with hempty | hn
    · have he : integralChartBox e a b = ∅ := by
        simp only [integralChartBox, hempty, preimage_empty, inter_empty]
      exact chartOpenCapProperty_congr hDX omegaX hlocalX he.symm isOpen_empty
        (integralChartBox_isOpen e a b) (integralOpenCapProperty_empty hDX omegaX hlocalX)
    · exact integralOpenCapProperty_of_homeomorph_euclidean hDX omegaX hlocalX hgenX
        (integralChartBox e a b) (integralChartBox_isOpen e a b)
        ((integralChartBoxHomeomorph e a b hB).trans
          (euclideanThreeOpenBoxHomeomorph a b hn))
  have hstage (s : Finset (integralChartBoxesInside e W)) :
      integralOpenCapProperty hDX omegaX hlocalX (integralChartBoxCoverStage e W s)
        (integralChartBoxCoverStage_isOpen e W s) := by
    apply finite_chart_box_cap_property hDX omegaX hlocalX e hbox s
      (fun p => p.1.1) (fun p => p.1.2)
    intro p y hy
    obtain ⟨x, hxW, rfl⟩ := p.2 hy
    exact e.map_source (hWs hxW)
  have hP := integralOpenCapProperty_directed_union hDX omegaX hlocalX
    (integralChartBoxCoverStage e W) (integralChartBoxCoverStage_isOpen e W)
    (integralChartBoxCoverStage_directed e W) hstage
  exact chartOpenCapProperty_congr hDX omegaX hlocalX
    (integralChartBoxCoverStage_iUnion e W hW hWs) _ hW hP

end CapProperty

end PoincareConjecture.Proofs.M02.Topology
