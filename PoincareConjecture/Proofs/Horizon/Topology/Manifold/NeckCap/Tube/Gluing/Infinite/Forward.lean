import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.Sequence
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.LowerExhaustion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.Prepend
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_forward_cylinder_with_affine_tail_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∀ a : ℤ, C.shape = .forward a →
        ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (C.neck a).carrierOpen ∞),
          (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D p : M) = T p) ∧
          (∀ p : RoundCylinderSpace,
            -(3 / 4 : ℝ) * ε⁻¹ < ((C.neck a).coordinate_inverse (T p)).2 ↔ 0 < p.2) ∧
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
            range (fun q : UnitTwoSphere => (C.neck a).coordinate_map (q, -(3 / 4 : ℝ) * ε⁻¹)) ∧
          (∀ p : RoundCylinderSpace, ((C.neck a).coordinate_inverse (T p)).1 = p.1) ∧
          ∃ r : ℝ, 0 < r ∧ ∀ p : RoundCylinderSpace, |p.2| < r →
            (C.neck a).coordinate_inverse (T p) =
              (p.1, -(3 / 4 : ℝ) * ε⁻¹ + p.2) := by
  obtain ⟨ε₁, hε₁, hsmall, hsequence⟩ := EpsilonNeck.exists_forward_prefix_charts.{u}
  obtain ⟨ε₂, hε₂, _, hnegative⟩ := exists_uniform_negative_end_exclusion_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε hsep a hshape
  let N : ℕ → EpsilonNeck g := fun n => C.neck (a + (n : ℤ))
  have hN0 : N 0 = C.neck a := by simp only [N, Int.natCast_zero, add_zero]
  have hactive (n : ℕ) : a + (n : ℤ) ∈ C.shape.active := by
    rw [hshape]
    change a ≤ a + (n : ℤ)
    omega
  have ha : a ∈ C.shape.active := by simpa only [Int.natCast_zero, add_zero] using hactive 0
  have heN (n : ℕ) : (N n).epsilon = ε := C.epsilon_eq _ (hactive n)
  have hepos : 0 < ε := heN 0 ▸ (N 0).epsilon_pos
  have hi := inv_pos.mpr hepos
  have hNsmall (n : ℕ) : (N n).epsilon ≤ ε₁ := by
    rw [heN]
    exact hε.trans (min_le_left _ _)
  have hNneg (n : ℕ) : (N (n + 1)).region (-(N (n + 1)).epsilon⁻¹)
      (-(N (n + 1)).epsilon⁻¹ / 2) ⊆ (N n).carrier := by
    rw [heN]
    have hnext : a + (n : ℤ) + 1 ∈ C.shape.active := by
      simpa only [Int.natCast_add, Int.natCast_one, ← add_assoc] using hactive (n + 1)
    simpa only [N, Int.natCast_add, Int.natCast_one, ← add_assoc] using
      (C.overlap_contains_quarters _ (hactive n) hnext).2
  have hNwithin (n : ℕ) : (N n).carrier ∩ (N (n + 1)).carrier ⊆
      (N n).region (-(N n).epsilon⁻¹ / 2) (N n).epsilon⁻¹ ∩
        (N (n + 1)).region (-(N (n + 1)).epsilon⁻¹) ((N (n + 1)).epsilon⁻¹ / 2) := by
    rw [heN n, heN (n + 1)]
    have hnext : a + (n : ℤ) + 1 ∈ C.shape.active := by
      simpa only [Int.natCast_add, Int.natCast_one, ← add_assoc] using hactive (n + 1)
    simpa only [N, Int.natCast_add, Int.natCast_one, ← add_assoc] using
      C.overlap_within_three_quarters _ (hactive n) hnext
  have hNavoid (n : ℕ) : Disjoint (N (n + 1)).carrier
      ((N 0).region (-(N 0).epsilon⁻¹) (-(7 / 8 : ℝ) * (N 0).epsilon⁻¹)) := by
    have h := hnegative C (hε.trans (min_le_right _ _)) hsep a ha
      (a + ((n + 1 : ℕ) : ℤ)) (hactive (n + 1)) (by omega)
    have h' : Disjoint (N (n + 1)).carrier ((N 0).region (-ε⁻¹) (-ε⁻¹ / 2)) := by
      simpa only [N, Int.natCast_zero, add_zero] using h
    rw [heN 0]
    apply h'.mono_right
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans (by linarith)⟩
  obtain ⟨F, T, E, htail, hside, hretain, hE, _, hF0, hzero, hTfst, r, hr, hTaffine⟩ :=
    hsequence N hNsmall hNneg hNwithin hNavoid
  have hNunion : (⨆ n, (N n).carrierOpen) = C.unionOpen := by
    apply SetLike.coe_injective
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Opens.mem_iSup.mp hx
      exact mem_iUnion.mpr ⟨⟨a + (n : ℤ), hactive n⟩, hn⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hia : a ≤ i.1 := by simpa only [hshape, ChainShape.active, mem_Ici] using i.2
      have hieq : a + ((i.1 - a).toNat : ℤ) = i.1 := by omega
      apply Opens.mem_iSup.mpr
      refine ⟨(i.1 - a).toNat, ?_⟩
      change x ∈ (C.neck (a + ((i.1 - a).toNat : ℤ))).carrier
      rwa [hieq]
  have hUnion : (⨆ n, EpsilonNeck.neckPrefixUnion N n) = C.unionOpen :=
    (EpsilonNeck.iSup_neckPrefixUnion N).trans hNunion
  have hconnected : IsConnected (⋃ n, (EpsilonNeck.neckPrefixUnion N n : Set M)) := by
    rw [← Opens.coe_iSup, hUnion]
    exact C.isConnected_union
  obtain ⟨D, hDfirst⟩ := EpsilonNeck.exists_cylinder_of_neck_tails N heN
    (EpsilonNeck.neckPrefixUnion N) (EpsilonNeck.neckPrefixUnion_mono N) hconnected
    F T E htail (fun n p => by simpa only [heN n] using hside n p)
    (fun n => by simpa only [heN n, heN (n + 1)] using hNwithin n) hretain hE
  have hDzero : range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
      range (fun q : UnitTwoSphere => (C.neck a).coordinate_map (q, -(3 / 4 : ℝ) * ε⁻¹)) := by
    rw [show (fun q : UnitTwoSphere => (D (q, 0) : M)) =
      (fun q => (F 0 (q, 0) : M)) from funext (fun q => hDfirst (q, 0) le_rfl), hzero]
    rw [heN 0, hN0]
  have hout : ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace
      ↥(⨆ n, EpsilonNeck.neckPrefixUnion N n) ∞)
      (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (N 0).carrierOpen ∞),
      (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D p : M) = T p) ∧
      (∀ p : RoundCylinderSpace,
        -(3 / 4 : ℝ) * ε⁻¹ < ((N 0).coordinate_inverse (T p)).2 ↔ 0 < p.2) ∧
      range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
        range (fun q : UnitTwoSphere => (C.neck a).coordinate_map (q, -(3 / 4 : ℝ) * ε⁻¹)) ∧
      (∀ p : RoundCylinderSpace, ((N 0).coordinate_inverse (T p)).1 = p.1) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ p : RoundCylinderSpace, |p.2| < r →
        (N 0).coordinate_inverse (T p) = (p.1, -(3 / 4 : ℝ) * ε⁻¹ + p.2) := by
    refine ⟨D, T 0, fun p hp => (hDfirst p hp).trans (hF0 p), ?_, hDzero,
      hTfst, r, hr, ?_⟩
    · intro p
      simpa only [heN 0] using hside 0 p
    · intro p hp
      simpa only [heN 0] using hTaffine p hp
  rw [hN0] at hout
  exact hUnion ▸ hout

theorem exists_forward_cylinder_with_tail_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∀ a : ℤ, C.shape = .forward a →
        ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (C.neck a).carrierOpen ∞),
          (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D p : M) = T p) ∧
          (∀ p : RoundCylinderSpace,
            -(3 / 4 : ℝ) * ε⁻¹ < ((C.neck a).coordinate_inverse (T p)).2 ↔ 0 < p.2) ∧
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
            range (fun q : UnitTwoSphere => (C.neck a).coordinate_map (q, -(3 / 4 : ℝ) * ε⁻¹)) := by
  obtain ⟨ε₀, hε₀, hsmall, hforward⟩ := exists_forward_cylinder_with_affine_tail_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε hsep a hshape
  obtain ⟨D, T, hretain, hside, hzero, _⟩ := hforward C hε hsep a hshape
  exact ⟨D, T, hretain, hside, hzero⟩

end PoincareConjecture.BalancedNeckChain
