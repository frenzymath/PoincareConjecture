import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.SlopeRegularity
import PoincareConjecture.Definitions.M63Polygon

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {Z : Type v} [TopologicalSpace Z] [CompactSpace Z]

theorem initial_family_speed_bounds (F : RicciFlow n M (Icc a b))
    (gamma : Z → ℝ → M) (t : ℝ)
    (hjet : Continuous (fun p : Z × ℝ => m63AngularFirstJet (n := n) (gamma p.1) p.2))
    (hper : ∀ z, Function.Periodic (gamma z) curvePeriod)
    (hreg : ∀ z, MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (gamma z))
    (himm : ∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0) :
    ∃ m B : ℝ, 0 < m ∧ 0 < B ∧ ∀ z x,
      m ≤ curveSpeed F (fun y _ => gamma z y) t x ∧
        curveSpeed F (fun y _ => gamma z y) t x ≤ B := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · let := hZ
    exact ⟨1, 1, zero_lt_one, zero_lt_one, fun z => isEmptyElim z⟩
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨(F.metric t).inner, (F.metric t).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let v : Z × ℝ → ℝ := fun p => curveSpeed F (fun y _ => gamma p.1 y) t p.2
  have hX : Continuous (fun p : Z × ℝ =>
      (⟨gamma p.1 p.2, curveVelocity (gamma p.1) p.2⟩ : TangentBundle (𝓡 n) M)) := hjet
  have hcont : Continuous v := (hX.inner_bundle hX).sqrt
  have hpos (p : Z × ℝ) : 0 < v p :=
    Real.sqrt_pos.mpr ((F.metric t).pos _ _ (himm p.1 p.2))
  have hperiod (z : Z) : Function.Periodic (fun x => v (z, x)) curvePeriod := by
    have hv := m63CurveVelocity_periodic (hreg z) (hper z)
    intro x
    have hvx : curveVelocity (gamma z) (x + curvePeriod) = curveVelocity (gamma z) x := hv x
    have hbase : gamma z (x + curvePeriod) = gamma z x := hper z x
    change (F.metric t).tangentNorm (gamma z (x + curvePeriod))
        (curveVelocity (gamma z) (x + curvePeriod)) =
      (F.metric t).tangentNorm (gamma z x) (curveVelocity (gamma z) x)
    erw [hvx, hbase]
  have hp : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hK : IsCompact ((univ : Set Z) ×ˢ Icc (0 : ℝ) curvePeriod) :=
    isCompact_univ.prod isCompact_Icc
  have hne : ((univ : Set Z) ×ˢ Icc (0 : ℝ) curvePeriod).Nonempty :=
    ⟨(Classical.choice hZ, 0), mem_univ _, le_rfl, hp.le⟩
  obtain ⟨pmin, _, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  obtain ⟨pmax, _, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  refine ⟨v pmin, v pmax, hpos pmin, hpos pmax, ?_⟩
  intro z x
  obtain ⟨y, hy, hxy⟩ := (hperiod z).exists_mem_Ico₀ hp x
  change v pmin ≤ v (z, x) ∧ v (z, x) ≤ v pmax
  rw [hxy]
  exact ⟨hmin ⟨mem_univ _, Ico_subset_Icc_self hy⟩,
    hmax ⟨mem_univ _, Ico_subset_Icc_self hy⟩⟩

theorem initial_family_principal_bounds (F : RicciFlow n M (Icc a b))
    (gamma : Z → ℝ → M) (t : ℝ)
    (hjet : Continuous (fun p : Z × ℝ => m63AngularFirstJet (n := n) (gamma p.1) p.2))
    (hper : ∀ z, Function.Periodic (gamma z) curvePeriod)
    (hreg : ∀ z, MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (gamma z))
    (himm : ∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0) :
    ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧ ∀ z x,
      mu ≤ (curveSpeed F (fun y _ => gamma z y) t x ^ 2)⁻¹ ∧
        (curveSpeed F (fun y _ => gamma z y) t x ^ 2)⁻¹ ≤ Lambda := by
  obtain ⟨m, B, hm, hB, hbound⟩ := initial_family_speed_bounds F gamma t hjet hper hreg himm
  refine ⟨(B ^ 2)⁻¹, (m ^ 2)⁻¹, inv_pos.mpr (pow_pos hB _),
    inv_pos.mpr (pow_pos hm _), ?_⟩
  intro z x
  have hv : 0 < curveSpeed F (fun y _ => gamma z y) t x := hm.trans_le (hbound z x).1
  exact ⟨inv_anti₀ (pow_pos hv 2) (pow_le_pow_left₀ hv.le (hbound z x).2 2),
    inv_anti₀ (pow_pos hm 2) (pow_le_pow_left₀ hm.le (hbound z x).1 2)⟩

end PoincareConjecture.M63
