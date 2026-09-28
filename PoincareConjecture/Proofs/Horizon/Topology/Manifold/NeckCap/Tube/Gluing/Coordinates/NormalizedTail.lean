import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.SliceShift
import Mathlib.Topology.Order.IntermediateValue










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

omit [T2Space M] in


theorem strictMono_height_of_affine_neck_coordinates
    (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace N.carrierOpen ∞)
    (hfst : ∀ p : RoundCylinderSpace, (N.coordinate_inverse (T p)).1 = p.1)
    (b : ℝ) {r : ℝ} (hr : 0 < r)
    (haffine : ∀ p : RoundCylinderSpace, |p.2| < r →
      N.coordinate_inverse (T p) = (p.1, b + p.2)) :
    ∀ q : UnitTwoSphere, StrictMono (fun t : ℝ => (N.coordinate_inverse (T (q, t))).2) := by
  intro q
  have hcont : Continuous (fun t : ℝ => (N.coordinate_inverse (T (q, t))).2) :=
    continuous_snd.comp ((contMDiff_subtype_val.comp
      (N.coordinateDiffeomorph.symm.contMDiff.comp T.contMDiff)).continuous.comp
        (continuous_const.prodMk continuous_id))
  have hinj : Function.Injective (fun t : ℝ => (N.coordinate_inverse (T (q, t))).2) := by
    intro s t hst
    have hcoord : N.coordinate_inverse (T (q, s)) = N.coordinate_inverse (T (q, t)) :=
      Prod.ext ((hfst (q, s)).trans (hfst (q, t)).symm) hst
    have heq := T.injective (N.coordinateDiffeomorph.symm.injective (Subtype.ext hcoord))
    exact congrArg Prod.snd heq
  rcases hcont.strictMono_of_inj hinj with hmono | hanti
  · exact hmono
  · have hzero : (N.coordinate_inverse (T (q, 0))).2 = b := by
      simpa only [add_zero] using congrArg Prod.snd (haffine (q, 0) (by simpa using hr))
    have hhalf : (N.coordinate_inverse (T (q, r / 2))).2 = b + r / 2 :=
      congrArg Prod.snd (haffine (q, r / 2) (by rw [abs_of_pos (half_pos hr)]; linarith))
    have h := hanti (half_pos hr)
    dsimp only at h
    rw [hzero, hhalf] at h
    linarith



theorem exists_normalized_retained_neck_tail (U : Opens M) (hNU : N.carrier ⊆ U)
    (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
    (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace N.carrierOpen ∞)
    (b : ℝ) (hb : b ∈ Ioo (-N.epsilon⁻¹) 0)
    (hretain : ∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D p : M) = T p)
    (hfst : ∀ p : RoundCylinderSpace, (N.coordinate_inverse (T p)).1 = p.1)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (haffine : ∀ p : RoundCylinderSpace, |p.2| < r₀ →
      N.coordinate_inverse (T p) = (p.1, b + p.2)) :
    ∃ (D' : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞) (r : ℝ),
      0 < r ∧
      (∀ p : RoundCylinderSpace, |p.2| < r → (D' p : M) = N.coordinate_map p) ∧
      (fun p : RoundCylinderSpace => (D' p : M)) '' {p | p.2 ≤ 0} =
        {x : M | x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ 0} := by
  have hmono := N.strictMono_height_of_affine_neck_coordinates T hfst b hr₀ haffine
  let η := min (r₀ / 4) ((b + N.epsilon⁻¹) / 4)
  have hη : 0 < η := lt_min (by positivity) (by linarith [hb.1])
  have hηr : η < r₀ := (min_le_left _ _).trans_lt (by linarith)
  have hηb : η ≤ (b + N.epsilon⁻¹) / 4 := min_le_right _ _
  let c := b - η
  have hc : c ∈ Ioo (-N.epsilon⁻¹) 0 := by
    dsimp [c]
    constructor <;> linarith [hb.1, hb.2]
  have hcut (q : UnitTwoSphere) : N.coordinate_inverse (T (q, -η)) = (q, c) := by
    simpa only [c, sub_eq_add_neg] using haffine (q, -η)
      (by simpa only [abs_neg, abs_of_pos hη] using hηr)
  let τ : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
    toFun := fun p => (p.1, p.2 - η)
    invFun := fun p => (p.1, p.2 + η)
    left_inv := fun p => by simp only [sub_add_cancel, Prod.eta]
    right_inv := fun p => by simp only [add_sub_cancel_right, Prod.eta]
    contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
    contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const) }
  let D₀ := τ.trans D
  have hD₀half : (fun p : RoundCylinderSpace => (D₀ p : M)) '' {p | p.2 ≤ 0} =
      {x : M | x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ c} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      change p.2 ≤ 0 at hp
      have hpt : (τ p).2 ≤ 0 := by change p.2 - η ≤ 0; linarith
      change (D (τ p) : M) ∈ _
      rw [hretain (τ p) hpt]
      refine ⟨(T (τ p)).property, ?_⟩
      have h := (hmono p.1).monotone (show p.2 - η ≤ -η by linarith)
      rw [hcut] at h
      exact h
    · intro hx
      let z := T.symm ⟨x, hx.1⟩
      have hTz : (T z : M) = x := congrArg Subtype.val (T.apply_symm_apply _)
      have hz : z.2 ≤ -η := by
        apply (hmono z.1).le_iff_le.mp
        rw [hcut]
        simpa only [Prod.eta, hTz] using hx.2
      let p : RoundCylinderSpace := (z.1, z.2 + η)
      have hτp : τ p = z := by
        change (z.1, z.2 + η - η) = z
        simp only [add_sub_cancel_right, Prod.eta]
      refine ⟨p, (show z.2 + η ≤ 0 by linarith), ?_⟩
      change (D (τ p) : M) = x
      rw [hτp, hretain z (by linarith)]
      exact hTz
  have hi := inv_pos.mpr N.epsilon_pos
  obtain ⟨ρ, A, hρ, hAfixed, hAlocal, hAhalf⟩ := N.exists_smooth_slice_shift
    (show c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨hc.1, hc.2.trans hi⟩)
    (show (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨neg_neg_of_pos hi, hi⟩) hc.2
  let AU := A.restrictOpensOfFixedCompl U hNU hAfixed
  let D' := D₀.trans AU
  let r := min (η / 2) (min ((r₀ - η) / 2) ρ)
  have hr : 0 < r := lt_min (half_pos hη) (lt_min (by linarith) hρ)
  refine ⟨D', r, hr, ?_, ?_⟩
  · intro p hp
    have hpη : |p.2| < η / 2 := hp.trans_le (min_le_left _ _)
    have hpr : |p.2| < (r₀ - η) / 2 :=
      hp.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hpρ : |p.2| < ρ := hp.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hpt : (τ p).2 ≤ 0 := by
      change p.2 - η ≤ 0
      linarith [le_abs_self p.2]
    have htnear : |(τ p).2| < r₀ := by
      change |p.2 - η| < r₀
      have hbound := abs_sub_le p.2 0 η
      simp only [sub_zero, zero_sub, abs_neg, abs_of_pos hη] at hbound
      linarith
    have hTcoord : N.coordinate_inverse (T (τ p)) = (p.1, c + p.2) := by
      rw [haffine (τ p) htnear]
      refine Prod.ext ?_ ?_
      · rfl
      · change b + (p.2 - η) = c + p.2
        dsimp [c]
        ring
    have hz : (p.1, c + p.2) ∈ N.cylinderDomain :=
      hTcoord ▸ N.coordinate_inverse_mem (T (τ p)) (T (τ p)).property
    have hTmap : (T (τ p) : M) = N.coordinate_map (p.1, c + p.2) := by
      rw [← hTcoord]
      exact (N.coordinate_map_coordinate_inverse (T (τ p)).property).symm
    change A (D (τ p)) = N.coordinate_map p
    rw [hretain (τ p) hpt, hTmap, hAlocal _ hz (by simpa only [add_sub_cancel_left] using hpρ)]
    congr 1
    refine Prod.ext ?_ ?_
    · rfl
    · dsimp
      ring
  · change (A ∘ (fun p : RoundCylinderSpace => (D₀ p : M))) '' {p | p.2 ≤ 0} = _
    rw [image_comp, hD₀half, hAhalf]

end PoincareConjecture.EpsilonNeck
