import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.Sequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.Finite.Extension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.Extension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.ZeroSphere

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

universe u

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem forward_prefix_charts_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (N : ℕ → EpsilonNeck g),
        (∀ n, (N n).epsilon ≤ (1 / 200)) →
        (∀ n, (N (n + 1)).region (-(N (n + 1)).epsilon⁻¹)
          (-(N (n + 1)).epsilon⁻¹ / 2) ⊆ (N n).carrier) →
        (∀ n, (N n).carrier ∩ (N (n + 1)).carrier ⊆
          (N n).region (-(N n).epsilon⁻¹ / 2) (N n).epsilon⁻¹ ∩
            (N (n + 1)).region (-(N (n + 1)).epsilon⁻¹)
              ((N (n + 1)).epsilon⁻¹ / 2)) →
        (∀ n, Disjoint (N (n + 1)).carrier
          ((N 0).region (-(N 0).epsilon⁻¹) (-(7 / 8 : ℝ) * (N 0).epsilon⁻¹))) →
        ∃ (F : ∀ n, Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (neckPrefixUnion N n) ∞)
          (T : ∀ n, Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (N n).carrierOpen ∞)
          (E : ℕ → Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞),
          (∀ n (p : RoundCylinderSpace), 0 < p.2 → (F n p : M) = T n p) ∧
          (∀ n (p : RoundCylinderSpace),
            -(3 / 4 : ℝ) * (N n).epsilon⁻¹ < ((N n).coordinate_inverse (T n p)).2 ↔
              0 < p.2) ∧
          (∀ n (p : RoundCylinderSpace), p.2 ≤ 0 →
            (F (n + 1) ((E n).symm p) : M) = F n p) ∧
          (∀ n (p : RoundCylinderSpace), p.2 ≤ 0 → ((E n).symm p).2 < 0) ∧
          (∀ n, Disjoint (neckPrefixUnion N n : Set M)
            ((N (n + 1)).region ((N (n + 1)).epsilon⁻¹ / 2) (N (n + 1)).epsilon⁻¹)) ∧
          (∀ p : RoundCylinderSpace, (F 0 p : M) = T 0 p) ∧
          range (fun q : UnitTwoSphere => (F 0 (q, 0) : M)) =
            range (fun q : UnitTwoSphere =>
              (N 0).coordinate_map (q, -(3 / 4 : ℝ) * (N 0).epsilon⁻¹)) ∧
          (∀ p : RoundCylinderSpace, ((N 0).coordinate_inverse (T 0 p)).1 = p.1) ∧
          ∃ r : ℝ, 0 < r ∧ ∀ p : RoundCylinderSpace, |p.2| < r →
            (N 0).coordinate_inverse (T 0 p) =
              (p.1, -(3 / 4 : ℝ) * (N 0).epsilon⁻¹ + p.2) := by
  classical
  intro M _ _ _ _ _ _ _ g N hε hneg hwithin havoid
  let b (n : ℕ) : ℝ := -(3 / 4 : ℝ) * (N n).epsilon⁻¹
  let a : ℝ := -(7 / 8 : ℝ) * (N 0).epsilon⁻¹
  have hb (n : ℕ) : b n ∈ Ioo (-(N n).epsilon⁻¹) (N n).epsilon⁻¹ := by
    have hi := inv_pos.mpr (N n).epsilon_pos
    dsimp [b]
    constructor <;> linarith
  have hbq (n : ℕ) : b n < -(N n).epsilon⁻¹ / 2 := by
    have hi := inv_pos.mpr (N n).epsilon_pos
    dsimp [b]
    linarith
  have ha : a ∈ Ioo (-(N 0).epsilon⁻¹) (N 0).epsilon⁻¹ := by
    have hi := inv_pos.mpr (N 0).epsilon_pos
    dsimp [a]
    constructor <;> linarith
  have hab : a < b 0 := by
    have hi := inv_pos.mpr (N 0).epsilon_pos
    dsimp [a, b]
    linarith
  let L := (N 0).region (-(N 0).epsilon⁻¹) a
  let S := range (fun q : UnitTwoSphere => (N 0).coordinate_map (q, a))
  let Data (n : ℕ) :=
    Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (neckPrefixUnion N n) ∞ ×
    Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (N n).carrierOpen ∞ × Set M × ℝ
  let Good (n : ℕ) (d : Data n) : Prop :=
    0 < d.2.2.2 ∧ IsCompact d.2.2.1 ∧
    frontier d.2.2.1 ⊆ S ∪ range (fun q : UnitTwoSphere => (N n).coordinate_map (q, b n)) ∧
    (neckPrefixUnion N n : Set M) = (L ∪ d.2.2.1) ∪ (N n).region (b n) (N n).epsilon⁻¹ ∧
    Disjoint ((N n).region (b n) (N n).epsilon⁻¹) d.2.2.1 ∧
    (∀ q t, t ∈ Ioo (-(N n).epsilon⁻¹) (N n).epsilon⁻¹ →
      b n - d.2.2.2 < t → t ≤ b n → (N n).coordinate_map (q, t) ∈ d.2.2.1) ∧
    (∀ p : RoundCylinderSpace, 0 < p.2 → (d.1 p : M) = d.2.1 p) ∧
    (∀ p : RoundCylinderSpace, b n < ((N n).coordinate_inverse (d.2.1 p)).2 ↔ 0 < p.2)
  let State (n : ℕ) := {d : Data n // Good n d}
  have havoidS (n : ℕ) : Disjoint (N (n + 1)).carrier S := by
    apply ((havoid n).closure_right (N (n + 1)).carrier_open).mono_right
    rintro x ⟨q, rfl⟩
    have h := (N 0).coordinate_graph_mem_closure_belowGraph (fun _ => a) (fun _ => ha) q
    have hEq : (N 0).belowGraph (fun _ => a) = L := by
      ext x
      exact ⟨fun hx => ⟨hx.1, ((N 0).coordinate_inverse_mem x hx.1).2.1, hx.2⟩,
        fun hx => ⟨hx.1, hx.2.2⟩⟩
    rwa [hEq] at h
  have hnext (n : ℕ) (d : State n) :
      ∃ d' : State (n + 1),
        ∃ E : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
          (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (d'.1.1 (E.symm p) : M) = d.1.1 p) ∧
          (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (E.symm p).2 < 0) ∧
          Disjoint (neckPrefixUnion N n : Set M)
            ((N (n + 1)).region ((N (n + 1)).epsilon⁻¹ / 2) (N (n + 1)).epsilon⁻¹) := by
    rcases d with ⟨⟨F, T, K, r⟩, hr, hK, hfront, hdecomp, hupper, hcollar, htail, hside⟩
    obtain ⟨F', T', K', r', E, hr', hK', hfront', hdecomp', hupper', hcollar', htail',
      hside', hretain', hE', havoidPrefix⟩ := prefix_neck_extension_with_transition_of_epsilon_le (N n) (N (n + 1)) (hε n) (hε (n + 1))
      (hneg n) (hwithin n) (b n) (b (n + 1)) (hb n) (hb (n + 1)) (hbq n) (hbq (n + 1))
      (neckPrefixUnion N n) L K S (carrier_subset_neckPrefixUnion N n) F T htail hside
      hK hfront hdecomp (havoidS n) (havoid n) hupper r hr hcollar
    exact ⟨⟨⟨F', T', K', r'⟩, hr', hK', hfront', hdecomp', hupper', hcollar', htail', hside'⟩,
      E, hretain', hE', havoidPrefix⟩
  let K₀ := (N 0).closedGraphSlab (fun _ => a) (fun _ => b 0)
  have hK₀ : IsCompact K₀ := (N 0).isCompact_closedGraphSlab (fun _ => a) (fun _ => b 0)
    continuous_const continuous_const (fun _ => ha) (fun _ => hb 0) (fun _ => hab)
  have hfront₀ : frontier K₀ ⊆ S ∪
      range (fun q : UnitTwoSphere => (N 0).coordinate_map (q, b 0)) :=
    (N 0).frontier_closedGraphSlab_subset (fun _ => a) (fun _ => b 0)
      continuous_const continuous_const (fun _ => ha) (fun _ => hb 0) (fun _ => hab)
  have hdecomp₀ : (N 0).carrier = (L ∪ K₀) ∪ (N 0).region (b 0) (N 0).epsilon⁻¹ := by
    ext x
    constructor
    · intro hx
      have ht := ((N 0).coordinate_inverse_mem x hx).2
      by_cases hlow : ((N 0).coordinate_inverse x).2 < a
      · exact Or.inl (Or.inl ⟨hx, ht.1, hlow⟩)
      by_cases hhigh : b 0 < ((N 0).coordinate_inverse x).2
      · exact Or.inr ⟨hx, hhigh, ht.2⟩
      exact Or.inl (Or.inr ⟨hx, le_of_not_gt hlow, le_of_not_gt hhigh⟩)
    · rintro ((hx | hx) | hx) <;> exact hx.1
  have hupper₀ : Disjoint ((N 0).region (b 0) (N 0).epsilon⁻¹) K₀ := by
    apply disjoint_left.mpr
    exact fun x hx hk => not_lt_of_ge hk.2.2 hx.2.1
  have hcollar₀ (q : UnitTwoSphere) (t : ℝ)
      (ht : t ∈ Ioo (-(N 0).epsilon⁻¹) (N 0).epsilon⁻¹)
      (hlow : b 0 - (b 0 - a) < t) (hhigh : t ≤ b 0) : (N 0).coordinate_map (q, t) ∈ K₀ :=
    ((N 0).mem_closedGraphSlab_coordinate_map_iff (fun _ => a) (fun _ => b 0) ht).mpr
      ⟨by linarith, hhigh⟩
  obtain ⟨r₀, T₀, hr₀, hT₀fst, hT₀affine, hT₀side⟩ :=
    (N 0).exists_affine_neck_coordinates (fun _ => b 0)
    contMDiff_const (fun _ => hb 0)
  have hT₀pos (p : RoundCylinderSpace) : b 0 < ((N 0).coordinate_inverse (T₀ p)).2 ↔
      0 < p.2 := by simpa only [not_le] using not_congr (hT₀side p)
  let d₀ : State 0 := ⟨⟨T₀, T₀, K₀, b 0 - a⟩, sub_pos.mpr hab, hK₀, hfront₀,
    hdecomp₀, hupper₀, hcollar₀, fun _ _ => rfl, hT₀pos⟩
  let d : ∀ n, State n := Nat.rec d₀ (fun n d => (hnext n d).choose)
  let E (n : ℕ) := (hnext n (d n)).choose_spec.choose
  have hstep (n : ℕ) :
      (∀ p : RoundCylinderSpace, p.2 ≤ 0 → ((d (n + 1)).1.1 ((E n).symm p) : M) = (d n).1.1 p) ∧
      (∀ p : RoundCylinderSpace, p.2 ≤ 0 → ((E n).symm p).2 < 0) ∧
      Disjoint (neckPrefixUnion N n : Set M)
        ((N (n + 1)).region ((N (n + 1)).epsilon⁻¹ / 2) (N (n + 1)).epsilon⁻¹) :=
    (hnext n (d n)).choose_spec.choose_spec
  refine ⟨fun n => (d n).1.1, fun n => (d n).1.2.1, E, ?_, ?_,
    fun n => (hstep n).1, fun n => (hstep n).2.1, fun n => (hstep n).2.2,
    fun _ => rfl, ?_, hT₀fst, r₀, hr₀, hT₀affine⟩
  · intro n
    exact (d n).property.2.2.2.2.2.2.1
  · intro n
    exact (d n).property.2.2.2.2.2.2.2
  · exact (N 0).zeroSphere_eq_of_positive_tail _ (b 0) (hb 0) T₀ T₀
      (fun _ _ => rfl) hT₀pos

end PoincareConjecture.EpsilonNeck
