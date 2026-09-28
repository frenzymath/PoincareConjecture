import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Levels.Graph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.GraphCollar







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

private theorem range_eq_component_of_compact_local_image
    {P M : Type*} [TopologicalSpace P] [ConnectedSpace P] [CompactSpace P]
    [TopologicalSpace M] [T2Space M]
    {A V : Set M} (hV : IsOpen V) (F : P → M) (hF : Continuous F)
    (hrange : range F = A ∩ V) (p : P) :
    range F = connectedComponentIn A (F p) := by
  have hmem (q : P) : F q ∈ A := by
    have hm : F q ∈ range F := mem_range_self q
    rw [hrange] at hm
    exact hm.1
  let G : P → A := fun q => ⟨F q, hmem q⟩
  have hG : Continuous G := hF.subtype_mk _
  have hrG : range G = Subtype.val ⁻¹' V := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ((Set.ext_iff.mp hrange) _).mp (mem_range_self q) |>.2
    · intro hx
      obtain ⟨q, hq⟩ := ((Set.ext_iff.mp hrange) _).mpr ⟨x.property, hx⟩
      exact ⟨q, Subtype.ext hq⟩
  have hopen : IsOpen (range G) := by
    rw [hrG]
    exact hV.preimage continuous_subtype_val
  have hcomponent : range G = connectedComponent (G p) := by
    apply Subset.antisymm
    · exact (isConnected_range hG).isPreconnected.subset_connectedComponent (mem_range_self p)
    · exact (show IsClopen (range G) from
        ⟨(isCompact_range hG).isClosed, hopen⟩).connectedComponent_subset (mem_range_self p)
  rw [connectedComponentIn_eq_image (hmem p)]
  change range F = Subtype.val '' connectedComponent (G p)
  rw [← hcomponent, ← range_comp]
  rfl

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]



theorem exists_projective_level_component_parametrization
    (Φ : RoundCylinderSpace → M) {s : ℝ}
    (hΦ : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-s) s))
    (hfiber : ∀ z ∈ univ ×ˢ Ioo (-s) s, ∀ w ∈ univ ×ˢ Ioo (-s) s,
      Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2))
    {f : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (U : Set M) {W m c : ℝ} (hW : 0 < W) (hWs : W < s) (hm : 0 < m)
    (hU : Φ '' (univ ×ˢ Ioo (-W) W) ⊆ U)
    (hd : ∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (-W) W →
      m ≤ |deriv (fun a : ℝ => f (Φ (q, a))) t|)
    (hcenter : ∀ q : UnitTwoSphere, |f (Φ (q, 0)) - c| < m * W) :
    ∃ h : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ q, h q ∈ Ioo (-W) W) ∧ (∀ q, h (-q) = h q) ∧
      (∀ q, f (Φ (q, h q)) = c) ∧
      ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q => Φ (q, h q)) ∧
      ∀ q, range (fun p => Φ (p, h p)) =
        connectedComponentIn {x | x ∈ U ∧ f x = c} (Φ (q, h q)) := by
  obtain ⟨h, hh, hdom, hlevel, hgraph, hrange, hunique⟩ :=
    exists_smooth_cylinderCover_level_graph Φ hΦ.contMDiffOn hf hW hWs hm hd hcenter
  have hsub : (univ : Set UnitTwoSphere) ×ˢ Ioo (-W) W ⊆ univ ×ˢ Ioo (-s) s := by
    intro z hz
    exact ⟨mem_univ _, (neg_lt_neg hWs).trans hz.2.1, hz.2.2.trans hWs⟩
  have heven := cylinderCover_level_height_even Φ hdom hlevel hunique
    (fun q t ht => ((hfiber (q, t) (hsub ⟨mem_univ _, ht⟩)
      (-q, t) (hsub ⟨mem_univ _, ht⟩)).mpr (Or.inr rfl)).symm)
  have hopen : IsOpen (Φ '' (univ ×ˢ Ioo (-W) W)) :=
    (exists_projectiveCylinderSlab_homeomorph Φ
      (hΦ.isLocalHomeomorphOn.mono hsub)
      (fun z hz w hw => hfiber z (hsub hz) w (hsub hw))).1
  refine ⟨h, hh, hdom, heven, hlevel, hgraph, ?_⟩
  intro q
  apply range_eq_component_of_compact_local_image hopen _ hgraph.continuous _ q
  rw [← hrange]
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨⟨hU hx, hc⟩, hx⟩
  · rintro ⟨⟨_, hc⟩, hx⟩
    exact ⟨hx, hc⟩

end PoincareConjecture
