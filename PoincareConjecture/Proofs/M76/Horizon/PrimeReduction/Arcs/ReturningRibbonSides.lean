import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningArcNesting
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Collars.PolygonLocalJordanSide










set_option autoImplicit false
open Set Geometry
open scoped Topology

namespace Polygon

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))



theorem returning_axis_segment {u v : V} (hu : u.2 = 0) (hv : v.2 = 0)
    (huv : u.1 ≤ v.1) :
    segment ℝ u v = Icc u.1 v.1 ×ˢ ({0} : Set ℝ) := by
  let f : ℝ →ᵃ[ℝ] V := (AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ (0 : ℝ))
  have hfu : f u.1 = u := Prod.ext rfl hu.symm
  have hfv : f v.1 = v := Prod.ext rfl hv.symm
  have h := image_segment ℝ f u.1 v.1
  rw [hfu, hfv, segment_eq_Icc huv] at h
  rw [← h]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hz, hz0⟩
    exact ⟨z.1, hz, Prod.ext rfl hz0.symm⟩



theorem exists_returning_base_upper_rectangle {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hup : ∀ i, 0 ≤ (P i).2) {A : Set V} {u v q : V}
    (hboundary : P.boundary ℝ = A ∪ segment ℝ u v)
    (hA : IsClosed A) (hu : u.2 = 0) (hv : v.2 = 0)
    (hq0 : q.2 = 0) (hq : q.1 ∈ Ioo u.1 v.1) (hqA : q ∉ A) :
    ∃ δ : ℝ, 0 < δ ∧
      Ioo (q.1 - δ) (q.1 + δ) ×ˢ Ioo 0 δ ⊆ P.inside := by
  have huv : u.1 ≤ v.1 := (hq.1.trans hq.2).le
  have hseg := returning_axis_segment hu hv huv
  have hqP : q ∈ P.boundary ℝ := by
    rw [hboundary, hseg]
    exact Or.inr ⟨⟨hq.1.le, hq.2.le⟩, hq0⟩
  have hopen : IsOpen (Aᶜ ∩ Prod.fst ⁻¹' Ioo u.1 v.1) :=
    hA.isOpen_compl.inter (isOpen_Ioo.preimage continuous_fst)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen q ⟨hqA, hq⟩
  let J := Ioo (q.1 - δ) (q.1 + δ)
  let U := J ×ˢ Ioo (-δ) δ
  let L := J ×ˢ Ioo (-δ) 0
  let R := J ×ˢ Ioo 0 δ
  have hUball : U = Metric.ball q δ := by
    rw [← Prod.eta q, ← ball_prod_same, Real.ball_eq_Ioo, Real.ball_eq_Ioo, hq0]
    simp only [zero_sub, zero_add]
    rfl
  have hmodel (z : V) (hz : z ∈ U) : z ∈ P.boundary ℝ ↔ z.2 = 0 := by
    have hz' := hball (hUball ▸ hz)
    rw [hboundary, hseg]
    constructor
    · rintro (h | h)
      · exact (hz'.1 h).elim
      · exact h.2
    · intro h
      exact Or.inr ⟨⟨hz'.2.1.le, hz'.2.2.le⟩, h⟩
  have hcover : U \ P.boundary ℝ = L ∪ R := by
    ext z
    constructor
    · rintro ⟨hz, hn⟩
      rcases lt_or_gt_of_ne (fun h => hn ((hmodel z hz).mpr h)) with hl | hr
      · exact Or.inl ⟨hz.1, hz.2.1, hl⟩
      · exact Or.inr ⟨hz.1, hr, hz.2.2⟩
    · rintro (hl | hr)
      · have hz : z ∈ U := ⟨hl.1, hl.2.1, hl.2.2.trans hδ⟩
        exact ⟨hz, fun h => hl.2.2.ne ((hmodel z hz).mp h)⟩
      · have hz : z ∈ U := ⟨hr.1, (neg_lt_zero.mpr hδ).trans hr.2.1, hr.2.2⟩
        exact ⟨hz, fun h => hr.2.1.ne' ((hmodel z hz).mp h)⟩
  have hqU : q ∈ U := by
    exact ⟨⟨by linarith, by linarith⟩,
      by rw [hq0]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩⟩
  have hsides := P.local_jordan_side_labels hP hi hqP
    (isOpen_Ioo.prod isOpen_Ioo) hqU
    (isPreconnected_Ioo.prod isPreconnected_Ioo)
    (isPreconnected_Ioo.prod isPreconnected_Ioo) hcover
  have hclosedupper : closure P.inside ⊆ (univ : Set ℝ) ×ˢ Ici (0 : ℝ) := by
    apply P.closure_inside_subset_convex hP hi
      ((convex_univ : Convex ℝ (univ : Set ℝ)).prod (convex_Ici (0 : ℝ)))
    rintro _ ⟨i, rfl⟩
    exact ⟨mem_univ _, hup i⟩
  refine ⟨δ, hδ, ?_⟩
  rcases hsides with ⟨hL, _⟩ | ⟨hR, _⟩
  · have hneg : (q.1, -δ / 2) ∈ L := by
      exact ⟨⟨by dsimp [J]; linarith, by dsimp [J]; linarith⟩,
        by constructor <;> linarith⟩
    have := (hclosedupper (subset_closure (hL hneg))).2
    change 0 ≤ -δ / 2 at this
    linarith
  · exact hR





theorem returning_arc_outer_endpoint_order {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hup : ∀ i, 0 ≤ (P i).2) {A B : Set V} {u v a b : V}
    (hboundary : P.boundary ℝ = A ∪ segment ℝ u v)
    (hA : IsClosed A) (hAz : A ∩ Z = {u, v})
    (hB : IsFinitePLBallPair ℝ B {a, b}) (hBz : B ∩ Z = {a, b})
    (hBup : ∀ z ∈ B, 0 ≤ z.2) (hAB : Disjoint A B)
    (huv : u.1 < v.1) (hau : a.1 < u.1) (hub : u.1 < b.1) :
    v.1 < b.1 := by
  have hu : u ∈ A ∩ Z := hAz.symm.subset (by simp)
  have hv : v ∈ A ∩ Z := hAz.symm.subset (by simp)
  have ha : a ∈ B ∩ Z := hBz.symm.subset (by simp)
  have hb : b ∈ B ∩ Z := hBz.symm.subset (by simp)
  have hbA : b ∉ A := fun h => disjoint_left.mp hAB h hb.1
  have hbne : b.1 ≠ v.1 := by
    intro h
    have heq : b = v := Prod.ext h (hb.2.trans hv.2.symm)
    exact hbA (heq.symm ▸ hv.1)
  by_contra hn
  have hbv : b.1 < v.1 := lt_of_le_of_ne (not_lt.mp hn) hbne
  obtain ⟨δ, hδ, hrect⟩ := P.exists_returning_base_upper_rectangle hP hi hup
    hboundary hA hu.2 hv.2 hb.2 ⟨hub, hbv⟩ hbA
  let U : Set V := Ioo (b.1 - δ) (b.1 + δ) ×ˢ Ioo (-δ) δ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hbU : b ∈ U := by
    exact ⟨⟨by linarith, by linarith⟩,
      by rw [show b.2 = 0 from hb.2]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩⟩
  have hbcl : b ∈ closure (B \ {a, b}) := by
    rw [hB.closure_sdiff]
    exact hb.1
  obtain ⟨z, hzU, hzB⟩ := mem_closure_iff.mp hbcl U hU hbU
  have hzpos : 0 < z.2 := lt_of_le_of_ne (hBup z hzB.1) (by
    intro heq
    exact hzB.2 (hBz.subset ⟨hzB.1, heq.symm⟩))
  have hzI : z ∈ P.inside := hrect ⟨hzU.1, hzpos, hzU.2.2⟩
  have havoid : Disjoint (frontier P.inside) (B \ {a, b}) := by
    rw [P.frontier_inside hP hi]
    apply disjoint_left.mpr
    intro x hxP hxB
    rcases hboundary ▸ hxP with hxA | hxseg
    · exact disjoint_left.mp hAB hxA hxB.1
    · exact hxB.2 (hBz.subset ⟨hxB.1,
        segment_subset_returning_axis hu.2 hv.2 hxseg⟩)
  have hinside : B \ {a, b} ⊆ P.inside :=
    hB.isConnected_sdiff.isPreconnected.m76_subset_of_disjoint_frontier
      (P.isOpen_inside hP hi) havoid ⟨z, hzB, hzI⟩
  have hBcl : B ⊆ closure P.inside := by
    rw [← hB.closure_sdiff]
    exact closure_mono hinside
  have haseg : a ∈ segment ℝ u v :=
    (P.returning_closed_inside_axis hP hi hup hboundary hAz).subset ⟨hBcl ha.1, ha.2⟩
  rw [returning_axis_segment hu.2 hv.2 huv.le] at haseg
  exact hau.not_ge haseg.1.1





theorem exists_returning_ribbon_side_parameter {η : ℝ} (hη : 0 < η)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc (-η) η))
    (hfi : InjOn f (Icc (-η) η)) (hg : ContinuousOn g (Icc (-η) η))
    (hfg : f 0 < g 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, c ∈ Ioo (-η) η ∧ |c| < ε ∧ c ≠ 0 ∧ f c < f 0 ∧ f 0 < g c := by
  have hg0 : ContinuousAt g 0 :=
    hg.continuousAt (Icc_mem_nhds (neg_lt_zero.mpr hη) hη)
  have hnear : ∀ᶠ c in 𝓝 (0 : ℝ), f 0 < g c :=
    hg0.eventually (lt_mem_nhds hfg)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let ρ := min (min η δ) ε / 2
  have hρ : 0 < ρ := div_pos (lt_min (lt_min hη hδ) hε) (by norm_num)
  have hρη : ρ < η := by
    dsimp [ρ]
    linarith [min_le_left (min η δ) ε, min_le_left η δ]
  have hρδ : ρ < δ := by
    dsimp [ρ]
    linarith [min_le_left (min η δ) ε, min_le_right η δ]
  have hρε : ρ < ε := by dsimp [ρ]; linarith [min_le_right (min η δ) ε]
  have h0 : (0 : ℝ) ∈ Icc (-η) η := ⟨(neg_lt_zero.mpr hη).le, hη.le⟩
  have hp : ρ ∈ Icc (-η) η := ⟨by linarith, hρη.le⟩
  have hn : -ρ ∈ Icc (-η) η := ⟨by linarith, by linarith⟩
  rcases hf.strictMonoOn_of_injOn_Icc' (by linarith) hfi with hmono | hanti
  · refine ⟨-ρ, ⟨by linarith, by linarith⟩,
      by simpa [abs_of_pos hρ] using hρε, (neg_lt_zero.mpr hρ).ne,
      hmono hn h0 (neg_lt_zero.mpr hρ), ?_⟩
    apply hnear
    simpa [Real.dist_eq, abs_of_pos hρ] using hρδ
  · refine ⟨ρ, ⟨by linarith, hρη⟩,
      by simpa [abs_of_pos hρ] using hρε, hρ.ne', hanti h0 hp hρ, ?_⟩
    apply hnear
    simpa [Real.dist_eq, abs_of_pos hρ] using hρδ





theorem exists_outer_returning_ribbon_side {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hup : ∀ i, 0 ≤ (P i).2) {A : Set V} {u v : V}
    (hboundary : P.boundary ℝ = A ∪ segment ℝ u v)
    (hA : IsClosed A) (hAz : A ∩ Z = {u, v})
    {η : ℝ} (hη : 0 < η) (B : ℝ → Set V) (a b : ℝ → V)
    (ha : ContinuousOn (fun c => (a c).1) (Icc (-η) η))
    (hai : InjOn (fun c => (a c).1) (Icc (-η) η))
    (hb : ContinuousOn (fun c => (b c).1) (Icc (-η) η))
    (ha0 : a 0 = u) (hb0 : b 0 = v) (huv : u.1 < v.1)
    (hfamily : ∀ c ∈ Ioo (-η) η, c ≠ 0 →
      IsFinitePLBallPair ℝ (B c) {a c, b c} ∧
      B c ∩ Z = {a c, b c} ∧ (∀ z ∈ B c, 0 ≤ z.2) ∧ Disjoint A (B c))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, c ∈ Ioo (-η) η ∧ |c| < ε ∧ c ≠ 0 ∧
      (a c).1 < u.1 ∧ u.1 < v.1 ∧ v.1 < (b c).1 ∧
      IsFinitePLBallPair ℝ (B c) {a c, b c} ∧ Disjoint A (B c) := by
  obtain ⟨c, hc, hcε, hc0, hac, hbc⟩ :=
    exists_returning_ribbon_side_parameter hη ha hai hb (by simpa [ha0, hb0] using huv) hε
  rw [ha0] at hac hbc
  obtain ⟨hball, haxis, hupper, hdis⟩ := hfamily c hc hc0
  have horder := P.returning_arc_outer_endpoint_order hP hi hup hboundary hA hAz
    hball haxis hupper hdis huv hac hbc
  exact ⟨c, hc, hcε, hc0, hac, huv, horder, hball, hdis⟩

end Polygon
