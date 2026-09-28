import PoincareConjecture.Proofs.M25.AppA_1_Necks.TubeSphereCoordinates
import PoincareConjecture.Proofs.M25.AppA_1_Necks.PositiveTransitionBand
import PoincareConjecture.Proofs.M25.Mathlib.SmoothRetainedClamp
import PoincareConjecture.Proofs.M25.Mathlib.RelativeFiberwiseExtension

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_extended_chain_band_atlas :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      let L := epsilon⁻¹
      ∃ (e : ℤ → OpenPartialHomeomorph RoundCylinderSpace M)
        (A : ℤ → Diffeomorph (𝓡 2) (𝓡 2)
          UnitTwoSphere UnitTwoSphere ∞)
        (D : ℤ → Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
          ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞)
        (m p : ℤ → UnitTwoSphere → ℝ),
        (∀ i ∈ C.shape.active,
          (e i).source = univ ×ˢ Ioo (-L) L ∧
          (e i).target = (C.neck i).carrier ∧
          ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (e i)
            (univ ×ˢ Ioo (-L) L) ∧
          ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (e i).symm
            (C.neck i).carrier ∧
          (∀ z ∈ univ ×ˢ Ioo (-L) L,
            ((C.neck i).coordinate_inverse (e i z)).2 = z.2) ∧
          (∀ x ∈ (C.neck i).carrier,
            ((e i).symm x).2 = ((C.neck i).coordinate_inverse x).2) ∧
          (∀ z ∈ univ ×ˢ Ioo (-L) L, z.2 ≤ 5 * L / 8 →
            e i z = (C.neck i).coordinate_map z) ∧
          (∀ x ∈ (C.neck i).carrier,
            ((C.neck i).coordinate_inverse x).2 ≤ 5 * L / 8 →
              (e i).symm x = (C.neck i).coordinate_inverse x)) ∧
        (∀ i : ℤ, ∀ z : RoundCylinderSpace, (D i z).1 = A i z.1) ∧
        (∀ i : ℤ, ∀ q : UnitTwoSphere,
          StrictMono (fun s : ℝ => (D i (q, s)).2)) ∧
        (∀ i : ℤ, ∀ q : UnitTwoSphere,
          m i q < -(3 * L / 16) ∧ p i q < -(9 * L / 32)) ∧
        (∀ i : ℤ, ∀ q : UnitTwoSphere, ∀ s : ℝ,
          s ≤ 11 * L / 16 → D i (q, s) = (A i q, s + m i q)) ∧
        (∀ i : ℤ, ∀ q : UnitTwoSphere, ∀ s : ℝ,
          13 * L / 16 ≤ s → D i (q, s) = (A i q, s + p i q)) ∧
        (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
          ∀ z : RoundCylinderSpace,
            z.2 ∈ Icc (23 * L / 32) (25 * L / 32) →
              D i z ∈ univ ×ˢ Ioo (-L) (L / 2) ∧
              D i z = (e (i + 1)).symm (e i z) ∧
              e (i + 1) (D i z) = e i z) := by
  classical
  obtain ⟨epsilon0, hepos, hecap, hadjust⟩ :=
    EpsilonNeck.exists_positive_quarter_sphere_coordinate_adjustment.{u}
  refine ⟨epsilon0, hepos, hecap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C hepsilon hsep
  let L : ℝ := epsilon⁻¹
  have hepspos : 0 < epsilon := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    rw [← C.epsilon_eq i hi]
    exact (C.neck i).epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepspos
  let P : ℤ → OpenPartialHomeomorph RoundCylinderSpace M → Prop := fun i e =>
    e.source = (C.neck i).cylinderDomain ∧ e.target = (C.neck i).carrier ∧
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e (C.neck i).cylinderDomain ∧
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm (C.neck i).carrier ∧
    (∀ z ∈ (C.neck i).cylinderDomain,
      ((C.neck i).coordinate_inverse (e z)).2 = z.2) ∧
    (∀ x ∈ (C.neck i).carrier,
      (e.symm x).2 = ((C.neck i).coordinate_inverse x).2) ∧
    (∀ z ∈ (C.neck i).cylinderDomain, z.2 ≤ 5 * (C.neck i).epsilon⁻¹ / 8 →
      e z = (C.neck i).coordinate_map z) ∧
    (∀ x ∈ (C.neck i).carrier,
      ((C.neck i).coordinate_inverse x).2 ≤ 5 * (C.neck i).epsilon⁻¹ / 8 →
        e.symm x = (C.neck i).coordinate_inverse x)
  have hcharts (i : ℤ) :
      ∃ (A : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
        (e : OpenPartialHomeomorph RoundCylinderSpace M), P i e ∧
        (i ∈ C.shape.active → i + 1 ∈ C.shape.active →
          ∀ z : RoundCylinderSpace, z.2 ∈ Icc (11 * L / 16) (13 * L / 16) →
            e z ∈ (C.neck (i + 1)).carrier ∧
              ((C.neck (i + 1)).coordinate_inverse (e z)).1 = A z.1) := by
    by_cases hi : i ∈ C.shape.active ∧ i + 1 ∈ C.shape.active
    · have hsmall : (C.neck i).epsilon ≤ epsilon0 := by
        simpa only [C.epsilon_eq i hi.1] using hepsilon
      have hsmall' : (C.neck (i + 1)).epsilon ≤ epsilon0 := by
        simpa only [C.epsilon_eq (i + 1) hi.2] using hepsilon
      have hquarter : (C.neck i).region ((C.neck i).epsilon⁻¹ / 2)
          (C.neck i).epsilon⁻¹ ⊆ (C.neck (i + 1)).carrier := by
        simpa only [C.epsilon_eq i hi.1] using (C.overlap_contains_quarters i hi.1 hi.2).1
      obtain ⟨A, e, hes, het, he, hei, hh, hhi, hlo, hli, _, hband, _⟩ :=
        hadjust (C.neck i) (C.neck (i + 1)) hsmall hsmall' hquarter
      refine ⟨A, e, ⟨hes, het, he, hei, hh, hhi, hlo, hli⟩, ?_⟩
      intro _ _ z hz
      exact hband z (by simpa only [C.epsilon_eq i hi.1] using hz)
    · refine ⟨Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞,
        (C.neck i).coordinatePartialHomeomorph, ?_, ?_⟩
      · refine ⟨rfl, rfl, (C.neck i).coordinate_map_smooth,
          (C.neck i).coordinate_inverse_smooth, ?_, ?_, ?_, ?_⟩
        · intro z hz
          exact congrArg Prod.snd ((C.neck i).coordinate_inverse_coordinate_map hz)
        · intro x _
          rfl
        · intro z _ _
          rfl
        · intro x _ _
          rfl
      · intro hi0 hi1
        exact (hi ⟨hi0, hi1⟩).elim
  choose A e he hband using hcharts
  have hleft : 11 * L / 16 < 23 * L / 32 := by linarith
  have hab : 23 * L / 32 < 25 * L / 32 := by linarith
  have hright : 25 * L / 32 < 13 * L / 16 := by linarith
  obtain ⟨rho, hrho, hrhomono, hrange, hagree, hrhoderiv, hrholeft, hrhoright⟩ :=
    Real.exists_smooth_retained_clamp hleft hab hright
  have htransitions (i : ℤ) :
      ∃ (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
          RoundCylinderSpace RoundCylinderSpace ∞)
        (m p : UnitTwoSphere → ℝ),
        (∀ z : RoundCylinderSpace, (D z).1 = A i z.1) ∧
        (∀ q : UnitTwoSphere, StrictMono (fun s : ℝ => (D (q, s)).2)) ∧
        (∀ q : UnitTwoSphere, m q < -(3 * L / 16) ∧ p q < -(9 * L / 32)) ∧
        (∀ q : UnitTwoSphere, ∀ s : ℝ,
          s ≤ 11 * L / 16 → D (q, s) = (A i q, s + m q)) ∧
        (∀ q : UnitTwoSphere, ∀ s : ℝ,
          13 * L / 16 ≤ s → D (q, s) = (A i q, s + p q)) ∧
        (i ∈ C.shape.active → i + 1 ∈ C.shape.active →
          ∀ z : RoundCylinderSpace, z.2 ∈ Icc (23 * L / 32) (25 * L / 32) →
            D z ∈ univ ×ˢ Ioo (-L) (L / 2) ∧
            D z = (e (i + 1)).symm (e i z) ∧ e (i + 1) (D z) = e i z) := by
    by_cases hi : i ∈ C.shape.active ∧ i + 1 ∈ C.shape.active
    · have hqi := he i
      have hqj := he (i + 1)
      dsimp only [P] at hqi hqj
      obtain ⟨hes, het, hesm, heism, heh, _, _, _⟩ := hqi
      obtain ⟨he's, he't, he'sm, he'ism, he'h, _, _, he'low⟩ := hqj
      have hclosed (z : RoundCylinderSpace)
          (hz : z.2 ∈ Icc (11 * L / 16) (13 * L / 16)) :
          z ∈ (C.neck i).cylinderDomain := by
        change z ∈ univ ×ˢ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹
        rw [C.epsilon_eq i hi.1]
        exact ⟨mem_univ _, by linarith [hz.1], by linarith [hz.2]⟩
      have hfirst (z : RoundCylinderSpace)
          (hz : z.2 ∈ Icc (11 * L / 16) (13 * L / 16)) :
          ((e (i + 1)).symm (e i z)).1 = A i z.1 := by
        have hb := hband i hi.1 hi.2 z hz
        have hold : e i z ∈ (C.neck i).carrier :=
          het ▸ (e i).map_source (hes.symm ▸ hclosed z hz)
        have hheight := (C.overlap_within_three_quarters i hi.1 hi.2 ⟨hold, hb.1⟩).2.2.2
        have hlow : ((C.neck (i + 1)).coordinate_inverse (e i z)).2 ≤
            5 * (C.neck (i + 1)).epsilon⁻¹ / 8 := by
          rw [C.epsilon_eq (i + 1) hi.2]
          change ((C.neck (i + 1)).coordinate_inverse (e i z)).2 ≤ 5 * L / 8
          linarith
        rw [he'low _ hb.1 hlow]
        exact hb.2
      have hquarter : (C.neck i).region ((C.neck i).epsilon⁻¹ / 2)
          (C.neck i).epsilon⁻¹ ⊆ (C.neck (i + 1)).carrier := by
        simpa only [C.epsilon_eq i hi.1] using (C.overlap_contains_quarters i hi.1 hi.2).1
      have hoverlap : (C.neck i).carrier ∩ (C.neck (i + 1)).carrier ⊆
          (C.neck i).region (-(C.neck i).epsilon⁻¹ / 2) (C.neck i).epsilon⁻¹ ∩
            (C.neck (i + 1)).region (-(C.neck (i + 1)).epsilon⁻¹)
              ((C.neck (i + 1)).epsilon⁻¹ / 2) := by
        simpa only [C.epsilon_eq i hi.1, C.epsilon_eq (i + 1) hi.2] using
          C.overlap_within_three_quarters i hi.1 hi.2
      have ha0 : (C.neck i).epsilon⁻¹ / 2 < 11 * L / 16 := by
        rw [C.epsilon_eq i hi.1]
        change L / 2 < 11 * L / 16
        linarith
      have hb0 : 13 * L / 16 < (C.neck i).epsilon⁻¹ := by
        rw [C.epsilon_eq i hi.1]
        change 13 * L / 16 < L
        linarith
      obtain ⟨hgraph, _, hh, hhpos, _⟩ :=
        (C.neck i).positive_fiberwise_transition_band (C.neck (i + 1)) (hsep i hi.1)
          hquarter hoverlap (e i) (e (i + 1)) (A i) hes het he's he't
          hesm heism he'sm he'ism heh he'h ha0 (by linarith : 11 * L / 16 < 13 * L / 16)
          hb0 hfirst
      let h : RoundCylinderSpace → ℝ := fun z => ((e (i + 1)).symm (e i z)).2
      have hbound (q : UnitTwoSphere) (s : ℝ)
          (hs : s ∈ Icc (11 * L / 16) (13 * L / 16)) : h (q, s) ∈ Ioo (-L) (L / 2) := by
        have hq := (hgraph s hs).2.1 (A i q)
        simpa only [Diffeomorph.symm_apply_apply, C.epsilon_eq (i + 1) hi.2] using hq
      obtain ⟨D, hD, _, hDpos, hret, hminus, hplus, _⟩ :=
        Diffeomorph.exists_relative_fiberwise_extension (A i) h hleft hab hright
          hh hhpos rho hrho hrange hagree hrhoderiv hrholeft hrhoright
      let m : UnitTwoSphere → ℝ := fun q => h (q, rho (11 * L / 16)) - rho (11 * L / 16)
      let p : UnitTwoSphere → ℝ := fun q => h (q, rho (13 * L / 16)) - rho (13 * L / 16)
      refine ⟨D, m, p, ?_, ?_, ?_, hminus, hplus, ?_⟩
      · intro z
        exact congrArg Prod.fst (hD z)
      · intro q
        have hm := strictMono_of_deriv_pos (hDpos q)
        simpa only [hD] using hm
      · intro q
        have hm := (hbound q (rho (11 * L / 16))
          ⟨(hrange _).1.le, (hrange _).2.le⟩).2
        have hp := (hbound q (rho (13 * L / 16))
          ⟨(hrange _).1.le, (hrange _).2.le⟩).2
        have hrleft := (hrange (11 * L / 16)).1
        have hrright : 25 * L / 32 ≤ rho (13 * L / 16) := by
          have hmono := hrhomono hright.le
          rw [hagree ⟨hab.le, le_rfl⟩] at hmono
          exact hmono
        dsimp only [m, p]
        constructor <;> linarith
      · intro _ _ z hz
        have hz0 : z.2 ∈ Icc (11 * L / 16) (13 * L / 16) :=
          ⟨hleft.le.trans hz.1, hz.2.trans hright.le⟩
        have hpair : (e (i + 1)).symm (e i z) = (A i z.1, h z) :=
          Prod.ext (hfirst z hz0) rfl
        have ht : D z = (e (i + 1)).symm (e i z) :=
          (hret z hz).1.trans hpair.symm
        refine ⟨?_, ht, ?_⟩
        · rw [ht]
          exact ⟨mem_univ _, hbound z.1 z.2 hz0⟩
        · rw [ht]
          exact (e (i + 1)).right_inv (he't.symm ▸ (hband i hi.1 hi.2 z hz0).1)
    · let f : RoundCylinderSpace → ℝ := fun z => z.2 - L / 2
      have hf : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f :=
        (contDiff_id.sub contDiff_const).comp_contMDiff contMDiff_snd
      have hpos (q : UnitTwoSphere) (s : ℝ) :
          0 < deriv (fun r : ℝ => f (q, r)) s := by
        change 0 < deriv (fun r : ℝ => r - L / 2) s
        have hd : deriv (fun r : ℝ => r - L / 2) s = 1 :=
          ((hasDerivAt_id s).sub_const (L / 2)).deriv
        rw [hd]
        norm_num
      have hsurj (q : UnitTwoSphere) : Function.Surjective (fun s : ℝ => f (q, s)) := by
        intro s
        exact ⟨s + L / 2, by dsimp [f]; ring⟩
      obtain ⟨D, hD, _⟩ := Diffeomorph.exists_fiberwise_of_deriv_pos (A i) f hf hpos hsurj
      refine ⟨D, fun _ => -(L / 2), fun _ => -(L / 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro z
        exact congrArg Prod.fst (hD z)
      · intro q s t hst
        simpa only [hD, f] using sub_lt_sub_right hst (L / 2)
      · intro q
        constructor <;> linarith
      · intro q s _
        simpa only [f, sub_eq_add_neg] using hD (q, s)
      · intro q s _
        simpa only [f, sub_eq_add_neg] using hD (q, s)
      · intro hi0 hi1
        exact (hi ⟨hi0, hi1⟩).elim
  choose D m p hD using htransitions
  refine ⟨e, A, D, m, p, ?_, fun i => (hD i).1, fun i => (hD i).2.1,
    fun i => (hD i).2.2.1, fun i => (hD i).2.2.2.1,
    fun i => (hD i).2.2.2.2.1, fun i => (hD i).2.2.2.2.2⟩
  intro i hi
  simpa only [P, EpsilonNeck.cylinderDomain, C.epsilon_eq i hi] using he i

end PoincareConjecture.BalancedNeckChain
