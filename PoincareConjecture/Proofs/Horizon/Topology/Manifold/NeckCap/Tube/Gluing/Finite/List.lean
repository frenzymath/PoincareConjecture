import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.Extension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.ZeroSphere
import Mathlib.Data.List.Chain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

def finiteNeckUnion : List (EpsilonNeck g) → Opens M
  | [] => ⊥
  | N :: xs => N.carrierOpen ⊔ finiteNeckUnion xs

@[simp] theorem finiteNeckUnion_nil : finiteNeckUnion ([] : List (EpsilonNeck g)) = ⊥ := rfl

@[simp] theorem finiteNeckUnion_cons (N : EpsilonNeck g) (xs : List (EpsilonNeck g)) :
    finiteNeckUnion (N :: xs) = N.carrierOpen ⊔ finiteNeckUnion xs := rfl

theorem finiteNeckUnion_carrier (xs : List (EpsilonNeck g)) :
    (finiteNeckUnion xs : Set M) = ⋃ N ∈ xs, N.carrier := by
  induction xs with
  | nil => simp
  | cons N xs ih =>
    rw [finiteNeckUnion_cons]
    ext x
    simp only [Opens.coe_sup, mem_union, ih, mem_iUnion, List.mem_cons]
    aesop

theorem exists_cylinder_extension_over_list_with_tail :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A : EpsilonNeck g) (xs : List (EpsilonNeck g)),
        (∀ N ∈ A :: xs, N.epsilon ≤ ε₀) →
        ∀ b ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹, b < -A.epsilon⁻¹ / 2 →
        ∀ (U : Opens M) (L K S : Set M), A.carrier ⊆ U →
        ∀ (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrierOpen ∞),
        (∀ p : RoundCylinderSpace, 0 < p.2 → (F p : M) = T p) →
        (∀ p : RoundCylinderSpace, b < (A.coordinate_inverse (T p)).2 ↔ 0 < p.2) →
        IsCompact K →
        frontier K ⊆ S ∪ range (fun q : UnitTwoSphere => A.coordinate_map (q, b)) →
        (U : Set M) = (L ∪ K) ∪ A.region b A.epsilon⁻¹ →
        Disjoint (A.region b A.epsilon⁻¹) K →
        ∀ r : ℝ, 0 < r →
        (∀ q t, t ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
          b - r < t → t ≤ b → A.coordinate_map (q, t) ∈ K) →
        List.IsChain (fun A B : EpsilonNeck g =>
          (B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier) ∧
          A.carrier ∩ B.carrier ⊆
            A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
              B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2)) (A :: xs) →
        (∀ B ∈ xs, Disjoint B.carrier S ∧ Disjoint B.carrier L) →
        ∃ (N : EpsilonNeck g) (c : ℝ)
          (D : Diffeomorph CylModel (𝓡 3)
            RoundCylinderSpace ↥(U ⊔ finiteNeckUnion xs) ∞)
          (T' : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace N.carrierOpen ∞),
          N ∈ A :: xs ∧ c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
          (∀ p : RoundCylinderSpace, 0 < p.2 → (D p : M) = T' p) ∧
          (∀ p : RoundCylinderSpace, c < (N.coordinate_inverse (T' p)).2 ↔ 0 < p.2) ∧
          N = (A :: xs).getLast (by simp) ∧
          (xs ≠ [] → Disjoint (U : Set M) (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) := by
  obtain ⟨ε₀, hε₀, hε₀small, hstep⟩ := exists_prefix_neck_extension_with_transition.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g A xs hsmall b hb hbq U L K S hAU F T hFtail hTside
    hK hfront hdecomp hupper r hr hcollar hchain havoid
  induction xs generalizing A b U K r with
  | nil =>
    have hU : U = U ⊔ finiteNeckUnion (g := g) [] := by rw [finiteNeckUnion_nil, sup_bot_eq]
    have hout : ∃ (N : EpsilonNeck g) (c : ℝ)
        (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
        (T' : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace N.carrierOpen ∞),
        N ∈ [A] ∧ c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
        (∀ p : RoundCylinderSpace, 0 < p.2 → (D p : M) = T' p) ∧
        (∀ p : RoundCylinderSpace, c < (N.coordinate_inverse (T' p)).2 ↔ 0 < p.2) ∧
        N = [A].getLast (by simp) ∧
        (([] : List (EpsilonNeck g)) ≠ [] →
          Disjoint (U : Set M) (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) :=
      ⟨A, b, F, T, by simp, hb, hFtail, hTside, rfl, by simp⟩
    exact hU ▸ hout
  | cons B xs ih =>
    obtain ⟨hAB, hrest⟩ := List.isChain_cons_cons.mp hchain
    let s := -(3 / 4 : ℝ) * B.epsilon⁻¹
    have hi := inv_pos.mpr B.epsilon_pos
    have hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
      dsimp [s]
      constructor <;> linarith
    have hsq : s < -B.epsilon⁻¹ / 2 := by dsimp [s]; linarith
    obtain ⟨D, T', K', r', _, hr', hK', hfront', hdecomp', hupper', hcollar',
      hDtail, hTside', _, _, havoidPrefix⟩ :=
      hstep A B (hsmall A (by simp)) (hsmall B (by simp)) hAB.1 hAB.2 b s hb hs hbq hsq
        U L K S hAU F T hFtail hTside hK hfront hdecomp
        (havoid B (by simp)).1 (havoid B (by simp)).2 hupper r hr hcollar
    obtain ⟨N, c, D', T'', hN, hc, hD'tail, hT''side, hlast, hexclude⟩ :=
      ih B (fun N hN => hsmall N (List.mem_cons_of_mem A hN))
      s hs hsq (U ⊔ B.carrierOpen) K' subset_union_right D T' hDtail hTside'
      hK' hfront' hdecomp' hupper' r' hr' hcollar' hrest
      (fun N hN => havoid N (List.mem_cons_of_mem B hN))
    rw [finiteNeckUnion_cons, ← sup_assoc]
    refine ⟨N, c, D', T'', List.mem_cons_of_mem A hN, hc, hD'tail, hT''side,
      by simpa only [List.getLast_cons_cons] using hlast, ?_⟩
    intro _
    by_cases hxs : xs = []
    · subst xs
      have hNB : N = B := by simpa using hlast
      rw [hNB]
      exact havoidPrefix
    · exact (hexclude hxs).mono_left subset_union_left

theorem exists_cylinder_extension_over_list :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A : EpsilonNeck g) (xs : List (EpsilonNeck g)),
        (∀ N ∈ A :: xs, N.epsilon ≤ ε₀) →
        ∀ b ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹, b < -A.epsilon⁻¹ / 2 →
        ∀ (U : Opens M) (L K S : Set M), A.carrier ⊆ U →
        ∀ (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrierOpen ∞),
        (∀ p : RoundCylinderSpace, 0 < p.2 → (F p : M) = T p) →
        (∀ p : RoundCylinderSpace, b < (A.coordinate_inverse (T p)).2 ↔ 0 < p.2) →
        IsCompact K →
        frontier K ⊆ S ∪ range (fun q : UnitTwoSphere => A.coordinate_map (q, b)) →
        (U : Set M) = (L ∪ K) ∪ A.region b A.epsilon⁻¹ →
        Disjoint (A.region b A.epsilon⁻¹) K →
        ∀ r : ℝ, 0 < r →
        (∀ q t, t ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
          b - r < t → t ≤ b → A.coordinate_map (q, t) ∈ K) →
        List.IsChain (fun A B : EpsilonNeck g =>
          (B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier) ∧
          A.carrier ∩ B.carrier ⊆
            A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
              B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2)) (A :: xs) →
        (∀ B ∈ xs, Disjoint B.carrier S ∧ Disjoint B.carrier L) →
        Nonempty (Diffeomorph CylModel (𝓡 3)
          RoundCylinderSpace ↥(U ⊔ finiteNeckUnion xs) ∞) := by
  obtain ⟨ε₀, hε₀, hsmall, h⟩ := exists_cylinder_extension_over_list_with_tail.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g A xs hsmall b hb hbq U L K S hAU F T hFtail hTside
    hK hfront hdecomp hupper r hr hcollar hchain havoid
  obtain ⟨_, _, D, _⟩ := h A xs hsmall b hb hbq U L K S hAU F T hFtail hTside
    hK hfront hdecomp hupper r hr hcollar hchain havoid
  exact ⟨D⟩

theorem exists_finite_neck_cylinder_with_middle :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A : EpsilonNeck g) (xs : List (EpsilonNeck g)),
        (∀ N ∈ A :: xs, N.epsilon ≤ ε₀) →
        ∀ a b : ℝ, a ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
        b ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ → a < b → b < -A.epsilon⁻¹ / 2 →
        List.IsChain (fun A B : EpsilonNeck g =>
          (B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier) ∧
          A.carrier ∩ B.carrier ⊆
            A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
              B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2)) (A :: xs) →
        (∀ B ∈ xs, Disjoint B.carrier (A.region (-A.epsilon⁻¹) a)) →
        ∃ (D : Diffeomorph CylModel (𝓡 3)
          RoundCylinderSpace (finiteNeckUnion (A :: xs)) ∞)
          (N : EpsilonNeck g) (c : ℝ), N ∈ A :: xs ∧
          c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
            range (fun q : UnitTwoSphere => N.coordinate_map (q, c)) ∧
          N = (A :: xs).getLast (by simp) ∧
          (xs ≠ [] → Disjoint A.carrier (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) := by
  obtain ⟨ε₀, hε₀, hε₀small, hextend⟩ := exists_cylinder_extension_over_list_with_tail.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g A xs hsmall a b ha hb hab hbq hchain havoid
  let K := A.closedGraphSlab (fun _ => a) (fun _ => b)
  let L := A.region (-A.epsilon⁻¹) a
  let S := range (fun q : UnitTwoSphere => A.coordinate_map (q, a))
  have hK : IsCompact K := A.isCompact_closedGraphSlab (fun _ => a) (fun _ => b)
    continuous_const continuous_const (fun _ => ha) (fun _ => hb) (fun _ => hab)
  have hfront : frontier K ⊆ S ∪ range (fun q : UnitTwoSphere => A.coordinate_map (q, b)) :=
    A.frontier_closedGraphSlab_subset (fun _ => a) (fun _ => b)
      continuous_const continuous_const (fun _ => ha) (fun _ => hb) (fun _ => hab)
  have hdecomp : A.carrier = (L ∪ K) ∪ A.region b A.epsilon⁻¹ := by
    ext x
    constructor
    · intro hx
      have ht := (A.coordinate_inverse_mem x hx).2
      by_cases hlow : (A.coordinate_inverse x).2 < a
      · exact Or.inl (Or.inl ⟨hx, ht.1, hlow⟩)
      by_cases hhigh : b < (A.coordinate_inverse x).2
      · exact Or.inr ⟨hx, hhigh, ht.2⟩
      exact Or.inl (Or.inr ⟨hx, le_of_not_gt hlow, le_of_not_gt hhigh⟩)
    · rintro ((hx | hx) | hx) <;> exact hx.1
  have hupper : Disjoint (A.region b A.epsilon⁻¹) K := by
    apply disjoint_left.mpr
    exact fun x hx hk => not_lt_of_ge hk.2.2 hx.2.1
  have hcollar (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
      (hlow : b - (b - a) < t) (hhigh : t ≤ b) : A.coordinate_map (q, t) ∈ K :=
    (A.mem_closedGraphSlab_coordinate_map_iff (fun _ => a) (fun _ => b) ht).mpr
      ⟨by linarith, hhigh⟩
  obtain ⟨_, T, _, _, _, hTside⟩ := A.exists_affine_neck_coordinates (fun _ => b)
    contMDiff_const (fun _ => hb)
  have hTpos (p : RoundCylinderSpace) : b < (A.coordinate_inverse (T p)).2 ↔ 0 < p.2 := by
    simpa only [not_le] using not_congr (hTside p)
  have havoids : ∀ B ∈ xs, Disjoint B.carrier S ∧ Disjoint B.carrier L := by
    intro B hB
    refine ⟨((havoid B hB).closure_right B.carrier_open).mono_right ?_, havoid B hB⟩
    rintro x ⟨q, rfl⟩
    have h := A.coordinate_graph_mem_closure_belowGraph (fun _ => a) (fun _ => ha) q
    have hEq : A.belowGraph (fun _ => a) = A.region (-A.epsilon⁻¹) a := by
      ext x
      exact ⟨fun hx => ⟨hx.1, (A.coordinate_inverse_mem x hx.1).2.1, hx.2⟩,
        fun hx => ⟨hx.1, hx.2.2⟩⟩
    rwa [hEq] at h
  obtain ⟨N, c, D, T', hN, hc, hDtail, hT'side, hlast, hexclude⟩ :=
    hextend A xs hsmall b hb hbq A.carrierOpen L K S subset_rfl T T
    (fun _ _ => rfl) hTpos hK hfront hdecomp hupper (b - a) (sub_pos.mpr hab)
      hcollar hchain havoids
  exact ⟨D, N, c, hN, hc, N.zeroSphere_eq_of_positive_tail _ c hc D T' hDtail hT'side,
    hlast, hexclude⟩

theorem exists_finite_neck_cylinder :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A : EpsilonNeck g) (xs : List (EpsilonNeck g)),
        (∀ N ∈ A :: xs, N.epsilon ≤ ε₀) →
        ∀ a b : ℝ, a ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
        b ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ → a < b → b < -A.epsilon⁻¹ / 2 →
        List.IsChain (fun A B : EpsilonNeck g =>
          (B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier) ∧
          A.carrier ∩ B.carrier ⊆ A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
            B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2)) (A :: xs) →
        (∀ B ∈ xs, Disjoint B.carrier (A.region (-A.epsilon⁻¹) a)) →
        Nonempty (Diffeomorph CylModel (𝓡 3)
          RoundCylinderSpace (finiteNeckUnion (A :: xs)) ∞) := by
  obtain ⟨ε₀, hε₀, hsmall, h⟩ := exists_finite_neck_cylinder_with_middle.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g A xs hsmall a b ha hb hab hbq hchain havoid
  obtain ⟨D, _⟩ := h A xs hsmall a b ha hb hab hbq hchain havoid
  exact ⟨D⟩

end PoincareConjecture.EpsilonNeck
