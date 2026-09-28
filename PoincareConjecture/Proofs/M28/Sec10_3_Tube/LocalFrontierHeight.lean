import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalAxialOrientation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalSliceOscillation











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem mem_closure_positive_tail_m28 (N : EpsilonNeck g) {x : M}
    (hx : x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹))
    (hout : x ∉ N.carrier) {b : ℝ}
    (hb : b < N.epsilon⁻¹) : x ∈ closure (N.region b N.epsilon⁻¹) := by
  by_cases hhalf : b ≤ N.epsilon⁻¹ / 2
  · have hsub : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N.region b N.epsilon⁻¹ :=
      fun _ hy => ⟨hy.1, hhalf.trans_lt hy.2.1, hy.2.2⟩
    exact closure_mono hsub hx
  have hlow : -N.epsilon⁻¹ < N.epsilon⁻¹ / 2 := by
    linarith [inv_pos.mpr N.epsilon_pos]
  let K := N.coordinate_map '' (univ ×ˢ Icc (N.epsilon⁻¹ / 2) b)
  have hK : IsCompact K := N.isCompact_coordinate_slab hlow hb
  have hKsub : K ⊆ N.carrier := by
    rintro _ ⟨z, hz, rfl⟩
    exact N.coordinate_map_mem ⟨mem_univ _, hlow.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
  have hcover : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
      K ∪ N.region b N.epsilon⁻¹ := by
    intro y hy
    by_cases hby : b < (N.coordinate_inverse y).2
    · exact Or.inr ⟨hy.1, hby, hy.2.2⟩
    · exact Or.inl ⟨N.coordinate_inverse y,
        ⟨mem_univ _, hy.2.1.le, le_of_not_gt hby⟩,
        N.coordinate_map_coordinate_inverse hy.1⟩
  have h := closure_mono hcover hx
  rw [closure_union, hK.isClosed.closure_eq] at h
  exact h.resolve_left (fun hy => hout (hKsub hy))

private theorem frontier_height_bounds_of_signed_displacement
    (N P : EpsilonNeck g) {x : M} {σ : ℝ} (hσ : |σ| = 1)
    (hx : x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹))
    (hout : x ∉ N.carrier) (hxP : x ∈ P.central_sphere)
    (hdisp : ∀ (q : UnitTwoSphere) (a b : ℝ),
      a ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ →
      b ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ → a ≤ b →
      (0.9 : ℝ) * (b - a) ≤ σ * ((P.coordinate_inverse (N.coordinate_map (q, b))).2 -
        (P.coordinate_inverse (N.coordinate_map (q, a))).2) ∧
      σ * ((P.coordinate_inverse (N.coordinate_map (q, b))).2 -
        (P.coordinate_inverse (N.coordinate_map (q, a))).2) ≤ (1.1 : ℝ) * (b - a))
    (hosc : ∀ (q p : UnitTwoSphere) (a : ℝ),
      a ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ →
      |(P.coordinate_inverse (N.coordinate_map (q, a))).2 -
        (P.coordinate_inverse (N.coordinate_map (p, a))).2| ≤ 5 * Real.pi)
    (q : UnitTwoSphere) {a : ℝ} (ha : a ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹) :
    -(1.1 : ℝ) * (N.epsilon⁻¹ - a) - 5 * Real.pi ≤
        σ * (P.coordinate_inverse (N.coordinate_map (q, a))).2 ∧
      σ * (P.coordinate_inverse (N.coordinate_map (q, a))).2 ≤
        -(0.9 : ℝ) * (N.epsilon⁻¹ - a) + 5 * Real.pi := by
  let f : M → ℝ := fun y => σ * (P.coordinate_inverse y).2
  let c := f (N.coordinate_map (q, a))
  have hcont : ContinuousAt f x := continuousAt_const.mul
    (P.coordinate_inverse_smooth.continuousOn.continuousAt
      (P.carrier_open.mem_nhds (P.central_sphere_subset hxP))).snd
  have hzero : f x = 0 := by
    obtain ⟨p, hp⟩ := P.centralSphere_range ▸ hxP
    have hpdom : (p, (0 : ℝ)) ∈ P.cylinderDomain :=
      ⟨mem_univ _, neg_neg_of_pos (inv_pos.mpr P.epsilon_pos), inv_pos.mpr P.epsilon_pos⟩
    simp only [f, ← hp, P.coordinate_inverse_coordinate_map hpdom, mul_zero]
  have hbounds (b : ℝ) (hab : a < b) (hb : b < N.epsilon⁻¹) :
      c + (0.9 : ℝ) * (b - a) - 5 * Real.pi ≤ 0 ∧
        0 ≤ c + (1.1 : ℝ) * (N.epsilon⁻¹ - a) + 5 * Real.pi := by
    have hxTail := N.mem_closure_positive_tail_m28 hx hout hb
    have hpoint (y : M) (hy : y ∈ N.region b N.epsilon⁻¹) :
        c + (0.9 : ℝ) * (b - a) - 5 * Real.pi ≤ f y ∧
          f y ≤ c + (1.1 : ℝ) * (N.epsilon⁻¹ - a) + 5 * Real.pi := by
      let z := N.coordinate_inverse y
      have hz : z.2 ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ :=
        ⟨ha.1.trans (hab.trans hy.2.1), hy.2.2⟩
      have hd := hdisp z.1 a z.2 ha hz (hab.trans hy.2.1).le
      have ho : |σ * ((P.coordinate_inverse (N.coordinate_map (z.1, a))).2 -
          (P.coordinate_inverse (N.coordinate_map (q, a))).2)| ≤ 5 * Real.pi := by
        rw [abs_mul, hσ, one_mul]
        exact hosc z.1 q a ha
      have hmap : N.coordinate_map (z.1, z.2) = y := N.coordinate_map_coordinate_inverse hy.1
      rw [hmap] at hd
      obtain ⟨hol, hou⟩ := abs_le.mp ho
      dsimp [c, f]
      constructor <;> nlinarith [hy.2.1, hy.2.2]
    have hlo := ContinuousWithinAt.closure_le hxTail continuousWithinAt_const
      hcont.continuousWithinAt (fun y hy => (hpoint y hy).1)
    have hhi := ContinuousWithinAt.closure_le hxTail hcont.continuousWithinAt
      continuousWithinAt_const (fun y hy => (hpoint y hy).2)
    rw [hzero] at hlo hhi
    exact ⟨hlo, hhi⟩
  obtain ⟨b, hab, hb⟩ := exists_between ha.2
  have hlo := (hbounds b hab hb).2
  have hupper : c + (0.9 : ℝ) * (N.epsilon⁻¹ - a) - 5 * Real.pi ≤ 0 := by
    apply le_on_closure (s := Ioo a N.epsilon⁻¹)
      (f := fun b => c + (0.9 : ℝ) * (b - a) - 5 * Real.pi) (g := fun _ => (0 : ℝ))
      (fun b hb => (hbounds b hb.1 hb.2).1)
      (by fun_prop) continuousOn_const
    rw [closure_Ioo ha.2.ne]
    exact ⟨ha.2.le, le_rfl⟩
  change -(1.1 : ℝ) * (N.epsilon⁻¹ - a) - 5 * Real.pi ≤ c ∧
    c ≤ -(0.9 : ℝ) * (N.epsilon⁻¹ - a) + 5 * Real.pi
  constructor <;> linarith




theorem exists_frontier_transition_height_bounds_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
        ∀ x : M, x ∈ frontier N.carrier →
        x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        x ∈ P.central_sphere →
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          ∀ (q : UnitTwoSphere) (a : ℝ), a ∈ Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹ →
            -(1.1 : ℝ) * (N.epsilon⁻¹ - a) - 5 * Real.pi ≤
                σ * (P.coordinate_inverse (N.coordinate_map (q, a))).2 ∧
              σ * (P.coordinate_inverse (N.coordinate_map (q, a))).2 ≤
                -(0.9 : ℝ) * (N.epsilon⁻¹ - a) + 5 * Real.pi := by
  obtain ⟨ε₁, hε₁, hsmall, hcontain⟩ :=
    exists_closure_positive_quarter_subset_of_central_sphere_contact_m28.{u}
  obtain ⟨ε₂, hε₂, _, horient⟩ := exists_transition_band_orientation_m28.{u}
  obtain ⟨ε₃, hε₃, _, haxis⟩ := exists_transition_axis_monotonicity_m28.{u}
  obtain ⟨ε₄, hε₄, _, hoscillation⟩ := exists_transition_slice_oscillation_m28.{u}
  refine ⟨min ε₁ (min ε₂ (min ε₃ ε₄)), lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq x hxfront hx hxP
  have hN₁ := hε.trans (min_le_left _ _)
  have hN₂ := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hN₃ := hε.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hN₄ := hε.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hr : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let S := Ioo (N.epsilon⁻¹ / 2) N.epsilon⁻¹
  have hdom : S ⊆ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro a ha
    exact ⟨by dsimp [S] at ha; linarith [ha.1], ha.2⟩
  have hquarter := hcontain N P hN₁ heq ⟨x, hx, hxP⟩
  have hmem (q : UnitTwoSphere) (a : ℝ) (ha : a ∈ S) :
      N.coordinate_map (q, a) ∈ P.carrier := by
    apply hquarter
    apply subset_closure
    have hqa : (q, a) ∈ N.cylinderDomain := ⟨mem_univ _, hdom ha⟩
    refine ⟨N.coordinate_map_mem hqa, ?_⟩
    simpa only [N.coordinate_inverse_coordinate_map hqa, S, mem_Ioo] using ha
  have hdisp (q : UnitTwoSphere) (a b : ℝ) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≤ b) :=
    (haxis P N (heq ▸ hN₃) hN₃ q S isPreconnected_Ioo hdom (hmem q)).2 a ha b hb hab
  have hosc (q p : UnitTwoSphere) (a : ℝ) (ha : a ∈ S) :=
    hoscillation P N (heq ▸ hN₄) hN₄ (hdom ha) (fun q => hmem q a ha) q p
  have hnontrivial : ∃ a ∈ S, ∃ b ∈ S, a < b := by
    refine ⟨3 * N.epsilon⁻¹ / 4, ?_, 7 * N.epsilon⁻¹ / 8, ?_, ?_⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · linarith
  have hout : x ∉ N.carrier := (N.carrier_open.frontier_eq ▸ hxfront).2
  rcases horient P N (heq ▸ hN₂) hN₂ S isPreconnected_Ioo hdom hmem hnontrivial with
    hmono | hanti
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro q a ha
    refine frontier_height_bounds_of_signed_displacement N P (σ := 1)
      (by norm_num) hx hout hxP ?_ hosc q ha
    intro p a b ha hb hab
    have hd := hdisp p a b ha hb hab
    have hnonneg := sub_nonneg.mpr ((hmono p).monotoneOn ha hb hab)
    simpa only [abs_of_nonneg hnonneg, one_mul] using hd
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro q a ha
    refine frontier_height_bounds_of_signed_displacement N P (σ := -1)
      (by norm_num) hx hout hxP ?_ hosc q ha
    intro p a b ha hb hab
    have hd := hdisp p a b ha hb hab
    have hnonpos := sub_nonpos.mpr ((hanti p).antitoneOn ha hb hab)
    simpa only [abs_of_nonpos hnonpos, neg_one_mul] using hd

end PoincareConjecture.EpsilonNeck
