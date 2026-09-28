import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Actual
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Intervals.Family
import PoincareConjecture.Proofs.Horizon.Topology.Connected.IntervalNeighborhoods

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "IR2" => 𝓘(Real, Real × Real)

private theorem component_eq_of_class_eq {K : Set S2} {x y : K}
    (hxy : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    connectedComponentIn K x = connectedComponentIn K y := by
  rw [connectedComponentIn_eq_image x.property, connectedComponentIn_eq_image y.property,
    ConnectedComponents.coe_eq_coe.mp hxy]

private theorem class_eq_of_component_eq {K : Set S2} {x y : K}
    (hxy : connectedComponentIn K x = connectedComponentIn K y) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  apply ConnectedComponents.coe_eq_coe'.mpr
  have hx : (x : S2) ∈ connectedComponentIn K y := hxy ▸ mem_connectedComponentIn x.property
  rw [connectedComponentIn_eq_image y.property] at hx
  obtain ⟨z, hz, heq⟩ := hx
  have hzx : z = x := Subtype.ext heq
  exact hzx ▸ hz

theorem exists_disjoint_actual_exterior_strips
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p ->
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 -> q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) :
    let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
    ∃ (a b : Fin 2 -> Real) (w : Real)
        (F : Fin 2 -> OpenPartialHomeomorph (Real × Real) S2),
      0 < w ∧ (∀ i, a i < b i) ∧
      (∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
      (∀ i z, z ∈ (F i).source -> h (F i z) = h p + z.2) ∧
      (⋃ i, F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) = K ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      (∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
          (F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) =
        {F i (a i, 0), F i (b i, 0)}) ∧
      ∀ i, ∃ q ∈ K, F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real)) =
        connectedComponentIn K q := by
  classical
  dsimp only
  let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
  have hcard : Nat.card (ConnectedComponents K) = 2 :=
    card_exterior_connectedComponents_eq_two hh hunique e he0 hep he hei hform hr hrs
  have hn : Nat.card (ConnectedComponents K) ≠ 0 := by rw [hcard]; decide
  let E : ConnectedComponents K ≃ Fin 2 :=
    (Nat.equivFinOfCardPos hn).trans (finCongr hcard)
  choose q hq using fun i : Fin 2 => ConnectedComponents.surjective_coe (E.symm i)
  choose γ a b η δ F hdata using fun i : Fin 2 =>
    exists_actual_exterior_interval_strips hh hunique e he0 hep he hei hform hr hrs
      (q i) (q i).property
  have hab (i : Fin 2) : a i < b i := (hdata i).2.2.2.1
  have hcomponent (i : Fin 2) : γ i '' Icc (a i) (b i) =
      connectedComponentIn K (q i) := (hdata i).2.2.2.2.1
  have hends (i : Fin 2) : range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      connectedComponentIn K (q i) = {γ i (a i), γ i (b i)} :=
    (hdata i).2.2.2.2.2.1
  have hη (i : Fin 2) : 0 < η i := (hdata i).2.2.2.2.2.2.1
  have hδ (i : Fin 2) : 0 < δ i := (hdata i).2.2.2.2.2.2.2.1
  have hFs (i : Fin 2) : (F i).source =
      Ioo (a i - η i) (b i + η i) ×ˢ Ioo (-δ i) (δ i) :=
    (hdata i).2.2.2.2.2.2.2.2.1
  have hF (i : Fin 2) : ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source :=
    (hdata i).2.2.2.2.2.2.2.2.2.1
  have hFi (i : Fin 2) : ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target :=
    (hdata i).2.2.2.2.2.2.2.2.2.2.1
  have hcentral (i : Fin 2) (s : Real) : F i (s, 0) = γ i s :=
    (hdata i).2.2.2.2.2.2.2.2.2.2.2.1 s
  have hheight (i : Fin 2) : ∀ z ∈ (F i).source, h (F i z) = h p + z.2 :=
    (hdata i).2.2.2.2.2.2.2.2.2.2.2.2
  have hcentralImage (i : Fin 2) :
      F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real)) = connectedComponentIn K (q i) := by
    rw [← hcomponent i]
    ext x
    constructor
    · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, hx⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨s, hs, (hcentral i s).symm.trans hx⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨(s, 0), ⟨hs, rfl⟩, (hcentral i s).trans hx⟩
  have hcentralSource (i : Fin 2) :
      Icc (a i) (b i) ×ˢ ({0} : Set Real) ⊆ (F i).source := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have ht0 : t = 0 := ht
    subst t
    rw [hFs i]
    constructor
    · constructor <;> linarith [hη i, hs.1, hs.2]
    · constructor <;> linarith [hδ i]
  have hdisj : Pairwise (fun i j =>
      Disjoint (F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real)))
        (F j '' (Icc (a j) (b j) ×ˢ ({0} : Set Real)))) := by
    intro i j hij
    rw [hcentralImage i, hcentralImage j]
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have heq := (connectedComponentIn_eq hxi).trans (connectedComponentIn_eq hxj).symm
    have hc := class_eq_of_component_eq heq
    rw [hq i, hq j] at hc
    exact hij (E.symm.injective hc)
  obtain ⟨w, hw, U, _, hUdisj, hrect⟩ :=
    Poincare.Topology.exists_disjoint_closed_interval_rectangles
      (fun i => F i) a b (fun i => (hab i).le) (fun i => (F i).source)
      (fun i => (F i).open_source) (fun i => (hF i).continuousOn) hcentralSource hdisj
      (fun _ => univ) (fun _ => isOpen_univ) (fun _ => subset_univ _)
  let B (i : Fin 2) : Set (Real × Real) := Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w
  have hB (i : Fin 2) : IsOpen (B i) := isOpen_Ioo.prod isOpen_Ioo
  have hBrect (i : Fin 2) : B i ⊆ Icc (a i - w) (b i + w) ×ˢ Icc (-w) w :=
    prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  let G (i : Fin 2) := (F i).restrOpen (B i) (hB i)
  have hGs (i : Fin 2) : (G i).source = B i := by
    rw [(F i).restrOpen_source (B i) (hB i)]
    exact inter_eq_right.mpr ((hBrect i).trans (hrect i).1)
  have hGU (i : Fin 2) : (G i).target ⊆ U i := by
    intro x hx
    have hy : (G i).symm x ∈ B i := hGs i ▸ (G i).map_target hx
    have hxy : F i ((G i).symm x) = x := (G i).right_inv hx
    exact hxy ▸ (hrect i).2 (mem_image_of_mem (F i) (hBrect i hy))
  refine ⟨a, b, w, G, hw, hab, hGs,
    (fun i => (hF i).mono inter_subset_left),
    (fun i => (hFi i).mono inter_subset_left),
    (fun i z hz => hheight i z hz.1), ?_, ?_, ?_, ?_⟩
  · apply subset_antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      change x ∈ F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real)) at hi
      rw [hcentralImage i] at hi
      exact connectedComponentIn_subset K (q i) hi
    · intro x hx
      let y : K := ⟨x, hx⟩
      let i : Fin 2 := E (ConnectedComponents.mk y)
      have heq : ConnectedComponents.mk (q i) = ConnectedComponents.mk y := by
        rw [hq i]
        exact E.symm_apply_apply _
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change x ∈ F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))
      rw [hcentralImage i, component_eq_of_class_eq heq]
      exact mem_connectedComponentIn hx
  · intro i j hij
    exact (hUdisj hij).mono (hGU i) (hGU j)
  · intro i
    change range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      (F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) = {F i (a i, 0), F i (b i, 0)}
    rw [hcentralImage i, hcentral i, hcentral i]
    exact hends i
  · intro i
    exact ⟨q i, (q i).property, hcentralImage i⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
