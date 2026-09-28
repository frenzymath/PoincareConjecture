import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Compatible
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Partition.GraphRegions
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CylinderPasting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_prefix_cylinder_with_retained_half :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ ε₀ → B.epsilon ≤ ε₀ →
        ∀ s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹,
        (∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ A.carrier) →
        ∀ f : UnitTwoSphere → ℝ,
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f →
        (∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹) →
        range (fun q => A.coordinate_map (q, f q)) =
          range (fun q => B.coordinate_map (q, s)) →
        (∀ x ∈ A.carrier ∩ B.carrier,
          s < (B.coordinate_inverse x).2 ↔
            f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2) →
        ∀ (U : Opens M)
          (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
          (T₀ : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrierOpen ∞)
          (b : ℝ),
        (∀ q, b < f q) →
        (∀ p : RoundCylinderSpace, 0 < p.2 → (F p : M) = T₀ p) →
        (∀ p : RoundCylinderSpace, b < (A.coordinate_inverse (T₀ p)).2 ↔ 0 < p.2) →
        (U : Set M) ∪ B.carrier =
          ((U : Set M) \ A.aboveGraph f) ∪ B.region s B.epsilon⁻¹ →
        Disjoint ((U : Set M) \ A.aboveGraph f) (B.region s B.epsilon⁻¹) →
        ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace ↥(U ⊔ B.carrierOpen) ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace B.carrierOpen ∞)
          (E : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞),
          (∀ p : RoundCylinderSpace, 0 < p.2 → (D p : M) = T p) ∧
          (∀ p : RoundCylinderSpace, s < (B.coordinate_inverse (T p)).2 ↔ 0 < p.2) ∧
          (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D (E.symm p) : M) = F p) ∧
          (∀ p : RoundCylinderSpace, (F p : M) ∉ A.aboveGraph f →
            (D (E.symm p) : M) = F p) ∧
          (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (E.symm p).2 < 0) ∧
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
            range (fun q : UnitTwoSphere => B.coordinate_map (q, s)) := by
  obtain ⟨ε₀, hε₀, hε₀small, hcharts⟩ := exists_compatible_neck_cut_charts.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g A B hA hB s hs hc f hf hfd hrange hside
    U F T₀ b hbf hFtail hT₀side hcut hseparate
  obtain ⟨r, DA, T, hr, hDAangle, hDAzero, hDAside, hTside, hagree⟩ :=
    hcharts A B hA hB s hs hc f hf hfd hrange hside
  let E₀ := DA.trans T₀.symm
  let D₀ := E₀.trans F
  have hEchart (p : RoundCylinderSpace) : T₀ (E₀ p) = DA p := T₀.apply_symm_apply _
  have hEpos (p : RoundCylinderSpace) (hp : 0 < p.2) : 0 < (E₀ p).2 := by
    apply (hT₀side (E₀ p)).mp
    rw [hEchart]
    have hgt : f p.1 < (A.coordinate_inverse (DA p)).2 :=
      lt_of_not_ge (fun h => (not_le_of_gt hp) ((hDAside p).mp h))
    exact (hbf _).trans hgt
  have hEzero (q : UnitTwoSphere) : 0 < (E₀ (q, 0)).2 := by
    apply (hT₀side (E₀ (q, 0))).mp
    rw [hEchart, hDAzero]
    exact hbf q
  let V : Opens RoundCylinderSpace := ⟨{p | 0 < (E₀ p).2},
    isOpen_lt continuous_const (continuous_snd.comp E₀.continuous)⟩
  obtain ⟨δ, hδ, hδV⟩ := CylinderGluing.exists_cylinder_collar V hEzero
  have hD₀agree (p : RoundCylinderSpace) (hp : 0 < (E₀ p).2) :
      (D₀ p : M) = DA p := by
    change (F (E₀ p) : M) = DA p
    exact (hFtail (E₀ p) hp).trans (congrArg Subtype.val (hEchart p))
  have hcommon (p : RoundCylinderSpace) (hp : |p.2| < min r δ) :
      (D₀ p : M) = T p :=
    (hD₀agree p (hδV p (hp.trans_le (min_le_right _ _)))).trans
      (hagree p (hp.trans_le (min_le_left _ _)))
  have hpositive : (fun p : RoundCylinderSpace => (D₀ p : M)) '' {p | 0 < p.2} =
      A.aboveGraph f := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      change (D₀ p : M) ∈ A.aboveGraph f
      rw [hD₀agree p (hEpos p hp)]
      refine ⟨(DA p).property, ?_⟩
      rw [hDAangle]
      exact lt_of_not_ge (fun h => (not_le_of_gt hp) ((hDAside p).mp h))
    · intro hx
      obtain ⟨p, hp⟩ := DA.surjective ⟨x, hx.1⟩
      have hpx : (DA p : M) = x := congrArg Subtype.val hp
      have hlt := hx.2
      rw [← hpx, hDAangle] at hlt
      have hpos : 0 < p.2 := lt_of_not_ge fun hn => hlt.not_ge ((hDAside p).mpr hn)
      exact ⟨p, hpos, (hD₀agree p (hEpos p hpos)).trans hpx⟩
  have hleft : (fun p : RoundCylinderSpace => (D₀ p : M)) '' {p | p.2 ≤ 0} =
      (U : Set M) \ A.aboveGraph f := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(D₀ p).property, ?_⟩
      rw [← hpositive]
      rintro ⟨q, hq, heq⟩
      have hqp : q = p := D₀.injective (Subtype.ext heq)
      change p.2 ≤ 0 at hp
      change 0 < q.2 at hq
      exact (not_lt.mpr hp) (hqp ▸ hq)
    · rintro ⟨hxU, hxAH⟩
      obtain ⟨p, hp⟩ := D₀.surjective ⟨x, hxU⟩
      refine ⟨p, ?_, congrArg Subtype.val hp⟩
      change p.2 ≤ 0
      apply le_of_not_gt
      intro hgt
      apply hxAH
      rw [← hpositive]
      exact ⟨p, hgt, congrArg Subtype.val hp⟩
  have hright : (fun p : RoundCylinderSpace => (T p : M)) '' {p | 0 < p.2} =
      B.region s B.epsilon⁻¹ := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(T p).property, (hTside p).mpr hp,
        (B.coordinate_inverse_mem (T p) (T p).property).2.2⟩
    · intro hx
      obtain ⟨p, hp⟩ := T.surjective ⟨x, hx.1⟩
      have hpx : (T p : M) = x := congrArg Subtype.val hp
      exact ⟨p, (hTside p).mp (hpx.symm ▸ hx.2.1), hpx⟩
  have hsep (p q : RoundCylinderSpace) (hp : p.2 ≤ 0) (hq : 0 < q.2) :
      (D₀ p : M) ≠ T q := by
    intro heq
    apply Set.disjoint_left.mp hseparate
    · rw [← hleft]
      exact ⟨p, hp, rfl⟩
    · rw [← hright]
      exact ⟨q, hq, heq.symm⟩
  obtain ⟨W, D, hD, hW⟩ := Poincare.exists_pasted_cylinder U B.carrierOpen D₀ T
    (min r δ) (lt_min hr hδ) hcommon hsep
  rw [hleft, hright, ← hcut] at hW
  have hW' : W = U ⊔ B.carrierOpen := SetLike.coe_injective hW
  subst W
  have hretain (p : RoundCylinderSpace) (hp : (E₀.symm p).2 ≤ 0) :
      (D (E₀.symm p) : M) = F p := by
    calc
      (D (E₀.symm p) : M) = D₀ (E₀.symm p) := (hD _).trans (if_pos hp)
      _ = F p := by
        change (F (E₀ (E₀.symm p)) : M) = F p
        rw [E₀.apply_symm_apply]
  have hEstrict (p : RoundCylinderSpace) (hp : p.2 ≤ 0) : (E₀.symm p).2 < 0 := by
    have hlow : (A.coordinate_inverse (T₀ p)).2 ≤ b := by
      apply le_of_not_gt
      intro hgt
      exact (not_lt.mpr hp) ((hT₀side p).mp hgt)
    have hle : (E₀.symm p).2 ≤ 0 := by
      apply (hDAside (E₀.symm p)).mp
      rw [← hEchart, E₀.apply_symm_apply]
      exact hlow.trans (hbf _).le
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hpair : E₀.symm p = ((E₀.symm p).1, 0) := Prod.ext rfl heq
    have hpos := hEzero (E₀.symm p).1
    rw [← hpair, E₀.apply_symm_apply] at hpos
    exact (not_lt.mpr hp) hpos
  refine ⟨D, T, E₀, fun p hp => (hD p).trans (if_neg (not_le_of_gt hp)), hTside,
    fun p hp => hretain p (hEstrict p hp).le, ?_, hEstrict, ?_⟩
  · intro p hp
    apply hretain
    apply le_of_not_gt
    intro hgt
    apply hp
    rw [← hpositive]
    refine ⟨E₀.symm p, hgt, ?_⟩
    change (F (E₀ (E₀.symm p)) : M) = F p
    rw [E₀.apply_symm_apply]
  · have hzero (q : UnitTwoSphere) : (D (q, 0) : M) = A.coordinate_map (q, f q) := by
      calc
        (D (q, 0) : M) = D₀ (q, 0) := (hD _).trans (if_pos (le_refl 0))
        _ = DA (q, 0) := hD₀agree _ (hEzero q)
        _ = A.coordinate_map (q, f q) := by
          have hcoord := A.coordinate_map_coordinate_inverse (DA (q, 0)).property
          rw [hDAzero] at hcoord
          exact hcoord.symm
    rw [show (fun q : UnitTwoSphere => (D (q, 0) : M)) =
      (fun q => A.coordinate_map (q, f q)) from funext hzero]
    exact hrange

theorem exists_prefix_cylinder_of_partition :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ ε₀ → B.epsilon ≤ ε₀ →
        ∀ s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹,
        (∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ A.carrier) →
        ∀ f : UnitTwoSphere → ℝ,
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f →
        (∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹) →
        range (fun q => A.coordinate_map (q, f q)) =
          range (fun q => B.coordinate_map (q, s)) →
        (∀ x ∈ A.carrier ∩ B.carrier,
          s < (B.coordinate_inverse x).2 ↔
            f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2) →
        ∀ (U : Opens M)
          (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
          (T₀ : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrierOpen ∞)
          (b : ℝ),
        (∀ q, b < f q) →
        (∀ p : RoundCylinderSpace, 0 < p.2 → (F p : M) = T₀ p) →
        (∀ p : RoundCylinderSpace, b < (A.coordinate_inverse (T₀ p)).2 ↔ 0 < p.2) →
        (U : Set M) ∪ B.carrier =
          ((U : Set M) \ A.aboveGraph f) ∪ B.region s B.epsilon⁻¹ →
        Disjoint ((U : Set M) \ A.aboveGraph f) (B.region s B.epsilon⁻¹) →
        ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace ↥(U ⊔ B.carrierOpen) ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace B.carrierOpen ∞),
          (∀ p : RoundCylinderSpace, 0 < p.2 → (D p : M) = T p) ∧
          (∀ p : RoundCylinderSpace, s < (B.coordinate_inverse (T p)).2 ↔ 0 < p.2) := by
  obtain ⟨ε₀, hε₀, hε₀small, hextend⟩ := exists_prefix_cylinder_with_retained_half.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g A B hA hB s hs hc f hf hfd hrange hside
    U F T₀ b hbf hFtail hT₀side hcut hseparate
  obtain ⟨D, T, _, htail, hside, _⟩ :=
    hextend A B hA hB s hs hc f hf hfd hrange hside U F T₀ b hbf hFtail hT₀side hcut hseparate
  exact ⟨D, T, htail, hside⟩

end PoincareConjecture.EpsilonNeck
