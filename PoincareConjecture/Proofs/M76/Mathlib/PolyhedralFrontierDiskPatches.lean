import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralFrontierGraph
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGraphs












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace CoordinateHalfBoxes



theorem base_eq_closedBall (r : ℝ) : base r = Metric.closedBall 0 r := by
  ext p
  simp only [base, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right,
    Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]

end CoordinateHalfBoxes

namespace Geometry.SimplicialComplex








theorem exists_halfspace_frontier_disk_patch
    (H : Finset (((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ))
    (hp : ∀ A ∈ H, A ((0 : ℝ × ℝ), (1 : ℝ)) ≤ 1)
    (hactive : ∃ A ∈ H, A ((0 : ℝ × ℝ), (1 : ℝ)) = 1)
    {U : Set ((ℝ × ℝ) × ℝ)} (hU : IsOpen U)
    (hpU : ((0 : ℝ × ℝ), (1 : ℝ)) ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : (ℝ × ℝ) → ℝ) (V : Set ((ℝ × ℝ) × ℝ)) (r : ℝ),
      Continuous f ∧ f 0 = 1 ∧ IsOpen V ∧ ((0 : ℝ × ℝ), (1 : ℝ)) ∈ V ∧
      V ⊆ U ∧ r ∈ Ioo 0 ε ∧
      FinitePiecewiseAffineOn f (base r) ∧
      (fun x => (x, f x)) '' base r ⊆ V ∧
      IsFinitePLBallPair (ℝ × ℝ)
        ((fun x => (x, f x)) '' base r)
        ((fun x => (x, f x)) '' baseBoundary r) ∧
      (∀ T ⊆ base r,
        (frontier {p | ∀ A ∈ H, A p ≤ 1} ∩ V) ∩ Prod.fst ⁻¹' T =
          (fun x => (x, f x)) '' T) ∧
      (∃ O : Set ((ℝ × ℝ) × ℝ), IsOpen O ∧ ((0 : ℝ × ℝ), (1 : ℝ)) ∈ O ∧
        frontier {p | ∀ A ∈ H, A p ≤ 1} ∩ O ⊆ (fun x => (x, f x)) '' base r) ∧
      ∀ a b d e : ℝ, a < b → d < e → (Icc a b ×ˢ Icc d e) ⊆ base r →
        IsFinitePLBallPair (ℝ × ℝ)
          ((fun x => (x, f x)) '' (Icc a b ×ˢ Icc d e))
          ((fun x => (x, f x)) '' (({a, b} ×ˢ Icc d e) ∪ (Icc a b ×ˢ {d, e}))) := by
  obtain ⟨f, V, hf, hf0, hV, hpV, hVU, _, hfront, hfPL⟩ :=
    exists_halfspace_frontier_graph_germ H hp hactive hU hpU
  have hpre : IsOpen ((fun x => (x, f x)) ⁻¹' V) :=
    hV.preimage (continuous_id.prodMk hf)
  have hzero : (0 : ℝ × ℝ) ∈ (fun x => (x, f x)) ⁻¹' V := by
    change (0, f 0) ∈ V
    rw [hf0]
    exact hpV
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hpre 0 hzero
  let r := min (ε / 2) (δ / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hgraphV : (fun x => (x, f x)) '' base r ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    apply hδV
    rw [base_eq_closedBall] at hx
    exact Metric.closedBall_subset_ball hrδ hx
  have hbase := base_ballPair hr
  have hcopy := hbase
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hfbase : FinitePiecewiseAffineOn f (base r) := by
    rw [← hKs]
    exact hfPL K hK
  have hactual (T : Set (ℝ × ℝ)) (hT : T ⊆ base r) :
      (frontier {p | ∀ A ∈ H, A p ≤ 1} ∩ V) ∩ Prod.fst ⁻¹' T =
        (fun x => (x, f x)) '' T := by
    ext p
    constructor
    · rintro ⟨hpF, hpT⟩
      have hpgraph := hfront.subset hpF
      exact ⟨p.1, hpT, Prod.ext rfl hpgraph.1.symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hxV := hgraphV ⟨x, hT hx, rfl⟩
      exact ⟨hfront.symm.subset ⟨rfl, hxV⟩, hx⟩
  refine ⟨f, V, r, hf, hf0, hV, hpV, hVU, ⟨hr, hrε⟩, hfbase, hgraphV,
    hbase.graph hfbase, hactual, ?_, ?_⟩
  · let O := V ∩ Prod.fst ⁻¹' interior (base r)
    have h0interior : (0 : ℝ × ℝ) ∈ interior (base r) := by
      rw [base_eq_closedBall]
      exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr)
    refine ⟨O, hV.inter (isOpen_interior.preimage continuous_fst),
      ⟨hpV, h0interior⟩, ?_⟩
    intro x hx
    exact (hactual (base r) Subset.rfl).subset
      ⟨⟨hx.1, hx.2.1⟩, (show x.1 ∈ base r from interior_subset hx.2.2)⟩
  · intro a b d e hab hde hsub
    have hrect := (isFinitePLBallPair_Icc hab).prod (isFinitePLBallPair_Icc hde)
    exact hrect.image_of_subset hfbase.graph hsub
      (fun _ _ _ _ h => congrArg Prod.fst h)

end Geometry.SimplicialComplex
