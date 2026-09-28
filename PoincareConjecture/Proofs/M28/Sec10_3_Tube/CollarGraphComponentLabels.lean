import PoincareConjecture.Proofs.M28.Mathlib.ComponentLabels
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalGraphRegions
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckGraphSides










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M28

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
  {Y : Type v} [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] [IsManifold (𝓡 3) ∞ Y]
  {g : RiemannianMetric 3 X} {h : RiemannianMetric 3 Y}





theorem neck_collar_opposite_graph_component_labels
    (L : EpsilonNeck g) (N : EpsilonNeck h) (e : OpenPartialHomeomorph X Y)
    (he : L.carrier ⊆ e.source) {T : Set Y} (hmap : MapsTo e L.carrier T)
    (f : UnitTwoSphere → ℝ)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hsphere : e '' L.central_sphere = range (fun q => N.coordinate_map (q, f q)))
    (hcomponent : ∀ z ∈ N.belowGraph_m28 f,
      connectedComponentIn (T \ range (fun q => N.coordinate_map (q, f q))) z =
        N.belowGraph_m28 f)
    {x₀ x₁ : X} (hx₀ : x₀ ∈ L.belowGraph_m28 (fun _ => 0))
    (hx₁ : x₁ ∈ L.aboveGraph_m28 (fun _ => 0)) :
    e x₀ ∈ N.belowGraph_m28 f ↔ e x₁ ∉ N.belowGraph_m28 f := by
  have hzero (q : UnitTwoSphere) : (0 : ℝ) ∈ Ioo (-L.epsilon⁻¹) L.epsilon⁻¹ :=
    ⟨neg_lt_zero.mpr (inv_pos.mpr L.epsilon_pos), inv_pos.mpr L.epsilon_pos⟩
  have havoid₀ {x : X} (hx : x ∈ L.belowGraph_m28 (fun _ => 0)) :
      x ∉ L.central_sphere := by
    intro hS
    exact (ne_of_lt hx.2) ((L.mem_central_sphere_iff_of_mem_carrier hx.1).mp hS)
  have havoid₁ {x : X} (hx : x ∈ L.aboveGraph_m28 (fun _ => 0)) :
      x ∉ L.central_sphere := by
    intro hS
    exact (ne_of_gt hx.2) ((L.mem_central_sphere_iff_of_mem_carrier hx.1).mp hS)
  have himage {B : Set X} (hB : B ⊆ L.carrier)
      (havoid : ∀ x ∈ B, x ∉ L.central_sphere) :
      e '' B ⊆ T \ range (fun q => N.coordinate_map (q, f q)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hmap (hB hx), ?_⟩
    rw [← hsphere]
    rintro ⟨z, hz, heq⟩
    exact havoid x hx (e.injOn (he (L.central_sphere_subset hz)) (he (hB hx)) heq ▸ hz)
  have himage₀ := himage (B := L.belowGraph_m28 (fun _ => 0))
    (fun _ hx => hx.1) (fun _ hx => havoid₀ hx)
  have himage₁ := himage (B := L.aboveGraph_m28 (fun _ => 0))
    (fun _ hx => hx.1) (fun _ hx => havoid₁ hx)
  have hconn₀ : IsPreconnected (e '' L.belowGraph_m28 (fun _ => 0)) :=
    (L.isConnected_belowGraph_m28 _ continuous_const hzero).isPreconnected.image e
      (e.continuousOn.mono (fun _ hx => he hx.1))
  have hconn₁ : IsPreconnected (e '' L.aboveGraph_m28 (fun _ => 0)) :=
    (L.isConnected_aboveGraph_m28 _ continuous_const hzero).isPreconnected.image e
      (e.continuousOn.mono (fun _ hx => he hx.1))
  have hlabel₀ {y : Y} (hy : y ∈ e '' L.belowGraph_m28 (fun _ => 0)) :
      e x₀ ∈ N.belowGraph_m28 f ↔ y ∈ N.belowGraph_m28 f :=
    hconn₀.mem_iff_of_connectedComponentIn_eq himage₀ hcomponent
      (mem_image_of_mem e hx₀) hy
  have hlabel₁ {y : Y} (hy : y ∈ e '' L.aboveGraph_m28 (fun _ => 0)) :
      e x₁ ∈ N.belowGraph_m28 f ↔ y ∈ N.belowGraph_m28 f :=
    hconn₁.mem_iff_of_connectedComponentIn_eq himage₁ hcomponent
      (mem_image_of_mem e hx₁) hy
  have hsplit {y : Y} (hy : y ∈ e '' L.carrier)
      (hgraph : y ∉ range (fun q => N.coordinate_map (q, f q))) :
      y ∈ e '' L.belowGraph_m28 (fun _ => 0) ∨ y ∈ e '' L.aboveGraph_m28 (fun _ => 0) := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hne : (L.coordinate_inverse x).2 ≠ 0 := by
      intro hz
      apply hgraph
      rw [← hsphere]
      exact mem_image_of_mem e ((L.mem_central_sphere_iff_of_mem_carrier hx).mpr hz)
    rcases lt_or_gt_of_ne hne with hn | hp
    · exact Or.inl ⟨x, ⟨hx, hn⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hx, hp⟩, rfl⟩
  have hopen := e.isOpen_image_of_subset_source L.carrier_open he
  have hbase : e L.center ∈ range (fun q => N.coordinate_map (q, f q)) := by
    rw [← hsphere]
    exact mem_image_of_mem e L.center_on_central_sphere
  obtain ⟨q, hq⟩ := hbase
  change N.coordinate_map (q, f q) = e L.center at hq
  have hqopen : N.coordinate_map (q, f q) ∈ e '' L.carrier := by
    rw [hq]
    exact mem_image_of_mem e (L.central_sphere_subset L.center_on_central_sphere)
  obtain ⟨y₀, hy₀, hy₀N, hy₀sign⟩ := exists_neckGraphHeight_negative_in_open
    N f hopen q hqopen (hdom q) (kappa := 1) (Or.inl rfl)
  obtain ⟨y₁, hy₁, hy₁N, hy₁sign⟩ := exists_neckGraphHeight_negative_in_open
    N f hopen q hqopen (hdom q) (kappa := -1) (Or.inr rfl)
  have hy₀neg : neckGraphHeight N f y₀ < 0 := by simpa only [one_mul] using hy₀sign
  have hy₁pos : 0 < neckGraphHeight N f y₁ := by linarith
  have hy₀F : y₀ ∈ N.belowGraph_m28 f := ⟨hy₀N, sub_neg.mp hy₀neg⟩
  have hy₁F : y₁ ∉ N.belowGraph_m28 f := by
    intro hF
    exact (not_lt_of_ge (sub_nonpos.mpr hF.2.le)) hy₁pos
  have hy₀split := hsplit hy₀ (fun hS => (ne_of_lt hy₀neg)
    ((neckGraphHeight_eq_zero_iff N hdom hy₀N).mpr hS))
  have hy₁split := hsplit hy₁ (fun hS => (ne_of_gt hy₁pos)
    ((neckGraphHeight_eq_zero_iff N hdom hy₁N).mpr hS))
  constructor
  · intro h₀ h₁
    rcases hy₁split with hy | hy
    · exact hy₁F ((hlabel₀ hy).mp h₀)
    · exact hy₁F ((hlabel₁ hy).mp h₁)
  · intro h₁
    by_contra h₀
    rcases hy₀split with hy | hy
    · exact h₀ ((hlabel₀ hy).mpr hy₀F)
    · exact h₁ ((hlabel₁ hy).mpr hy₀F)

end PoincareConjecture.M28
