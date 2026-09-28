import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.Infinite.Sequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.NoReturn.PositiveEnd
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.Sequence
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.LowerExhaustion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.PositiveEnd
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem backward_cylinder_with_affine_tail_of_epsilon_le :
    ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ 1 / 200 → ∀ b : ℤ, C.shape = .backward b →
        ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (C.neck b).carrierOpen ∞),
          (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D p : M) = T p) ∧
          (∀ p : RoundCylinderSpace,
            ((C.neck b).coordinate_inverse (T p)).2 < (3 / 4 : ℝ) * ε⁻¹ ↔ 0 < p.2) ∧
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
            range (fun q : UnitTwoSphere => (C.neck b).coordinate_map (q, (3 / 4 : ℝ) * ε⁻¹)) ∧
          (∀ p : RoundCylinderSpace, ((C.neck b).coordinate_inverse (T p)).1 = p.1) ∧
          ∃ r : ℝ, 0 < r ∧ ∀ p : RoundCylinderSpace, |p.2| < r →
            (C.neck b).coordinate_inverse (T p) =
              (p.1, (3 / 4 : ℝ) * ε⁻¹ - p.2) := by
  intro M _ _ _ _ _ _ _ g ε C hε b hshape
  let N : ℕ → EpsilonNeck g := fun n => (C.neck (b - (n : ℤ))).reversed
  have hN0 : N 0 = (C.neck b).reversed := by simp only [N, Int.natCast_zero, sub_zero]
  have hactive (n : ℕ) : b - (n : ℤ) ∈ C.shape.active := by
    rw [hshape]
    change b - (n : ℤ) ≤ b
    omega
  have hb : b ∈ C.shape.active := by simpa only [Int.natCast_zero, sub_zero] using hactive 0
  have heN (n : ℕ) : (N n).epsilon = ε := C.epsilon_eq _ (hactive n)
  have hepos : 0 < ε := heN 0 ▸ (N 0).epsilon_pos
  have hi := inv_pos.mpr hepos
  have hNsmall (n : ℕ) : (N n).epsilon ≤ 1 / 200 := by
    rw [heN]
    exact hε
  have hnext (n : ℕ) : b - ((n + 1 : ℕ) : ℤ) + 1 = b - (n : ℤ) := by omega
  have hNneg (n : ℕ) : (N (n + 1)).region (-(N (n + 1)).epsilon⁻¹)
      (-(N (n + 1)).epsilon⁻¹ / 2) ⊆ (N n).carrier := by
    rw [heN]
    have h := (C.overlap_contains_quarters _ (hactive (n + 1))
      ((hnext n).symm ▸ hactive n)).1
    rw [hnext n] at h
    simpa only [N, EpsilonNeck.reversed_region, EpsilonNeck.reversed_carrier,
      neg_div, neg_neg] using h
  have hNwithin (n : ℕ) : (N n).carrier ∩ (N (n + 1)).carrier ⊆
      (N n).region (-(N n).epsilon⁻¹ / 2) (N n).epsilon⁻¹ ∩
        (N (n + 1)).region (-(N (n + 1)).epsilon⁻¹) ((N (n + 1)).epsilon⁻¹ / 2) := by
    rw [heN n, heN (n + 1)]
    simp only [N, EpsilonNeck.reversed_region, EpsilonNeck.reversed_carrier, neg_div, neg_neg]
    intro x hx
    have h := C.overlap_within_three_quarters _ (hactive (n + 1))
      ((hnext n).symm ▸ hactive n)
    rw [hnext n] at h
    simpa only [neg_div, mem_inter_iff] using (h ⟨hx.2, hx.1⟩).symm
  have hNavoid (n : ℕ) : Disjoint (N (n + 1)).carrier
      ((N 0).region (-(N 0).epsilon⁻¹) (-(7 / 8 : ℝ) * (N 0).epsilon⁻¹)) := by
    have h := positive_end_exclusion_of_epsilon_le C hε
      (b - ((n + 1 : ℕ) : ℤ)) (hactive (n + 1)) b hb (by omega)
    rw [heN 0, hN0]
    simp only [N, EpsilonNeck.reversed_region, EpsilonNeck.reversed_carrier, neg_neg, neg_mul]
    apply h.mono_right
    intro x hx
    exact ⟨hx.1, (show ε⁻¹ / 2 < (7 / 8 : ℝ) * ε⁻¹ by linarith).trans hx.2.1, hx.2.2⟩
  obtain ⟨F, T, E, htail, hside, hretain, hE, _, hF0, hzero, hTfst, r, hr, hTaffine⟩ :=
    EpsilonNeck.forward_prefix_charts_of_epsilon_le N hNsmall hNneg hNwithin hNavoid
  have hNunion : (⨆ n, (N n).carrierOpen) = C.unionOpen := by
    apply SetLike.coe_injective
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Opens.mem_iSup.mp hx
      exact mem_iUnion.mpr ⟨⟨b - (n : ℤ), hactive n⟩, hn⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hib : i.1 ≤ b := by simpa only [hshape, ChainShape.active, mem_Iic] using i.2
      have hieq : b - ((b - i.1).toNat : ℤ) = i.1 := by omega
      apply Opens.mem_iSup.mpr
      refine ⟨(b - i.1).toNat, ?_⟩
      change x ∈ (C.neck (b - ((b - i.1).toNat : ℤ))).carrier
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
      range (fun q : UnitTwoSphere => (C.neck b).coordinate_map (q, (3 / 4 : ℝ) * ε⁻¹)) := by
    rw [show (fun q : UnitTwoSphere => (D (q, 0) : M)) =
      (fun q => (F 0 (q, 0) : M)) from funext (fun q => hDfirst (q, 0) le_rfl), hzero]
    rw [heN 0, hN0]
    simp only [EpsilonNeck.reversed_coordinate_map, neg_mul, neg_neg]
  have hout : ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace
      ↥(⨆ n, EpsilonNeck.neckPrefixUnion N n) ∞)
      (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace (N 0).carrierOpen ∞),
      (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D p : M) = T p) ∧
      (∀ p : RoundCylinderSpace,
        ((C.neck b).coordinate_inverse (T p)).2 < (3 / 4 : ℝ) * ε⁻¹ ↔ 0 < p.2) ∧
      range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
        range (fun q : UnitTwoSphere => (C.neck b).coordinate_map (q, (3 / 4 : ℝ) * ε⁻¹)) ∧
      (∀ p : RoundCylinderSpace, ((C.neck b).coordinate_inverse (T p)).1 = p.1) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ p : RoundCylinderSpace, |p.2| < r →
        (C.neck b).coordinate_inverse (T p) = (p.1, (3 / 4 : ℝ) * ε⁻¹ - p.2) := by
    refine ⟨D, T 0, fun p hp => (hDfirst p hp).trans (hF0 p), ?_, hDzero, ?_, r, hr, ?_⟩
    · intro p
      have h := hside 0 p
      rw [heN 0] at h
      have hinverse (x : M) : ((N 0).coordinate_inverse x).2 =
          -((C.neck b).coordinate_inverse x).2 := by
        rw [hN0, EpsilonNeck.reversed_coordinate_inverse]
      rw [hinverse] at h
      have hequiv : ((C.neck b).coordinate_inverse (T 0 p)).2 < (3 / 4 : ℝ) * ε⁻¹ ↔
          -(3 / 4 : ℝ) * ε⁻¹ < -((C.neck b).coordinate_inverse (T 0 p)).2 := by
        constructor <;> intro ht <;> linarith
      exact hequiv.trans h
    · intro p
      have h := hTfst p
      simpa only [hN0, EpsilonNeck.reversed_coordinate_inverse] using h
    · intro p hp
      have h := hTaffine p hp
      rw [heN 0] at h
      simp only [hN0, EpsilonNeck.reversed_coordinate_inverse] at h
      apply Prod.ext
      · simpa only using congrArg Prod.fst h
      · have hs := congrArg Prod.snd h
        change -((C.neck b).coordinate_inverse (T 0 p)).2 =
          -(3 / 4 : ℝ) * ε⁻¹ + p.2 at hs
        change ((C.neck b).coordinate_inverse (T 0 p)).2 = (3 / 4 : ℝ) * ε⁻¹ - p.2
        linarith
  have hcarrier : (N 0).carrierOpen = (C.neck b).carrierOpen := by rw [hN0]; rfl
  rw [hcarrier] at hout
  exact hUnion ▸ hout

end PoincareConjecture.BalancedNeckChain
