import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicFiniteChain
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.RetainedFiniteChainCore
import PoincareConjecture.Proofs.M25.AppA_1_Necks.PositiveFrontier
import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionHeight
import PoincareConjecture.Proofs.M25.Mathlib.PlateauMeanValue
import PoincareConjecture.Proofs.M25.Mathlib.ClosedPrefixTrap










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

open Classical in



theorem BalancedNeckChain.exists_oriented_frontier_initial_height_control :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      ∀ a b : ℤ, C.shape = ChainShape.finite a b →
        let L := epsilon⁻¹
        let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
        let F : M → ℝ := fun x =>
          if x ∈ (C.neck a).carrier then
            ((C.neck a).coordinate_inverse x).2 else L
        ∀ (R : EpsilonNeck g), R.epsilon = epsilon →
          R.center ∈ closure ((C.neck b).region 0 L) →
          R.center ∉ U →
          ∀ f : UnitTwoSphere → ℝ,
            (∀ q, -(3 * L / 10) < f q ∧ f q < -(L / 5)) →
            Set.range (fun q : UnitTwoSphere =>
              (C.neck b).coordinate_map (q, 3 * L / 4)) =
              Set.range (fun q : UnitTwoSphere =>
                R.coordinate_map (q, f q)) →
            (∀ q : UnitTwoSphere,
              7 * L / 10 < F ((C.neck b).coordinate_map (q, 3 * L / 4))) ∧
            (∀ (q : UnitTwoSphere) (s : ℝ),
              -L < s → s ≤ -(L / 20) →
              R.coordinate_map (q, s) ∈ U ∧
                -(L / 5) < F (R.coordinate_map (q, s))) := by
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hden : 0 < 10000 * (B0 + Real.pi + 1) := by positivity
  obtain ⟨es, hspos, hscap, hscale⟩ :=
    EpsilonNeck.exists_intersecting_scale_control.{u} (α := (1 / 1000 : ℝ))
      (by norm_num)
  obtain ⟨ea, hapos, _, haxis⟩ :=
    EpsilonNeck.exists_intersecting_axial_derivative_control.{u}
      (η := (1 / 1000 : ℝ)) (by norm_num)
  obtain ⟨ek, hkpos, _, hcore⟩ :=
    BalancedNeckChain.exists_finite_retained_core_cover.{u}
  refine ⟨min es (min ea (min ek (min (1 / 10000)
    (1 / (10000 * (B0 + Real.pi + 1)))))),
    lt_min hspos (lt_min hapos (lt_min hkpos
      (lt_min (by norm_num) (div_pos zero_lt_one hden)))),
    (min_le_left _ _).trans hscap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C hepsilon a b hshape
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let L : ℝ := epsilon⁻¹
  let N := C.neck a
  let B := C.neck b
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let F : M → ℝ := fun x => if x ∈ N.carrier then (N.coordinate_inverse x).2 else L
  dsimp only
  intro R heR hy hout f hf hgraph
  change R.center ∈ closure (B.region 0 L) at hy
  change R.center ∉ U at hout
  change range (fun q : UnitTwoSphere => B.coordinate_map (q, 3 * L / 4)) =
    range (fun q : UnitTwoSphere => R.coordinate_map (q, f q)) at hgraph
  change (∀ q : UnitTwoSphere, 7 * L / 10 < F (B.coordinate_map (q, 3 * L / 4))) ∧
    (∀ (q : UnitTwoSphere) (s : ℝ), -L < s → s ≤ -(L / 20) →
      R.coordinate_map (q, s) ∈ U ∧ -(L / 5) < F (R.coordinate_map (q, s)))
  rcases le_min_iff.mp hepsilon with ⟨hes, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hea, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hek, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hesmall, henumeric⟩
  have hactive (i : ℤ) : i ∈ C.shape.active ↔ i ∈ Icc a b := by
    rw [hshape]
    rfl
  have hab : a ≤ b := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ((hactive i).mp hi).1.trans ((hactive i).mp hi).2
  have ha : a ∈ C.shape.active := (hactive a).mpr ⟨le_rfl, hab⟩
  have hb : b ∈ C.shape.active := (hactive b).mpr ⟨hab, le_rfl⟩
  have heN : N.epsilon = epsilon := C.epsilon_eq a ha
  have heB : B.epsilon = epsilon := C.epsilon_eq b hb
  have hepos : 0 < epsilon := heN ▸ N.epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have hNU : N.carrier ⊆ U := fun _ hx => mem_iUnion₂.mpr ⟨a, ha, hx⟩
  have hBU : B.carrier ⊆ U := fun _ hx => mem_iUnion₂.mpr ⟨b, hb, hx⟩
  have hyN : R.center ∉ N.carrier := fun hx => hout (hNU hx)
  have hyB : R.center ∉ B.carrier := fun hx => hout (hBU hx)
  have hyBcl : R.center ∈ closure (B.region 0 B.epsilon⁻¹) := by
    simpa only [heB] using hy
  have hFin (x : M) (hx : x ∈ N.carrier) : F x = (N.coordinate_inverse x).2 := by
    simp only [F, if_pos hx]
  have hFout (x : M) (hx : x ∉ N.carrier) : F x = L := by
    simp only [F, if_neg hx]
  have hI1 := C.continuousOn_initial_height_of_finite hshape
  change ContinuousOn F U ∧ (∀ x ∈ U, F x ∈ Ioc (-L) L) ∧ _ at hI1
  obtain ⟨hFcont, hFbounds, _⟩ := hI1
  obtain ⟨lo, hlo, hloa, hKcompact, hcover⟩ := hcore C hek a b hshape
  let K : Set M := ⋃ i ∈ C.shape.active,
    (C.neck i).coordinate_map '' (univ ×ˢ Icc (lo i) (3 * L / 4))
  change IsCompact K at hKcompact
  change U = (K ∪ N.region (-L) (lo a)) ∪ B.region (3 * L / 4) L at hcover
  rw [hloa] at hcover
  have hKsub : K ⊆ U := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    rcases hxi with ⟨z, hz, rfl⟩
    refine mem_iUnion₂.mpr ⟨i, hi, (C.neck i).coordinate_map_mem ?_⟩
    refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [C.epsilon_eq i hi]
    · exact (hlo i hi).1.trans_le hz.2.1
    · change z.2 < L
      linarith [hz.2.2]
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hopenU : IsOpen U :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  have hbudget : (B0 + Real.pi + 1) * epsilon ≤ 1 / 10000 := by
    have h := (le_div_iff₀ hden).mp henumeric
    nlinarith only [h]
  have hB0budget : B0 * epsilon ≤ 1 / 10000 := by
    nlinarith only [hbudget, hepos, mul_pos Real.pi_pos hepos]
  have hB0L : B0 ≤ L / 10000 := by
    calc
      B0 ≤ (1 / 10000) / epsilon := (le_div_iff₀ hepos).mpr hB0budget
      _ = L / 10000 := by dsimp only [L]; ring
  have hsqlo : (999 : ℝ) / 1000 ≤ Real.sqrt (1 - epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hesmall])
  have hsqhi : Real.sqrt (1 + epsilon) ≤ (1001 : ℝ) / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hesmall]⟩
  have hsqpos : 0 < Real.sqrt (1 - epsilon) := by linarith
  have hsqplus : 0 < Real.sqrt (1 + epsilon) := Real.sqrt_pos.mpr (by linarith)

  have htransfer (A D : EpsilonNeck g) (heA : A.epsilon = epsilon)
      (heD : D.epsilon = epsilon) (hAD : (A.carrier ∩ D.carrier).Nonempty)
      (x y : M) (t : ℝ) (ht : 0 ≤ t)
      (hdist : g.edist x y ≤
        ENNReal.ofReal (A.scale * Real.sqrt (1 + epsilon) * t)) :
      |D.axialDepth x - D.axialDepth y| ≤ (101 / 100 : ℝ) * t := by
    obtain ⟨z, hzA, hzD⟩ := hAD
    have hratio := (hscale D A (by rw [heD]; exact hes)
      (by rw [heA]; exact hes) ⟨z, hzD, hzA⟩).2
    have hscaleAD : A.scale ≤ (1001 / 1000 : ℝ) * D.scale := by
      apply (div_le_iff₀ D.scale_pos).mp
      linarith only [(abs_lt.mp hratio).2]
    have hcoeff : A.scale * Real.sqrt (1 + epsilon) ≤
        (101 / 100 : ℝ) * (D.scale * Real.sqrt (1 - epsilon)) := by
      calc
        _ ≤ ((1001 / 1000 : ℝ) * D.scale) * (1001 / 1000) :=
          mul_le_mul hscaleAD hsqhi (Real.sqrt_nonneg _)
            (mul_nonneg (by norm_num) D.scale_pos.le)
        _ ≤ _ := by
          have h := mul_le_mul_of_nonneg_left hsqlo D.scale_pos.le
          linarith only [h, D.scale_pos]
    have hdepth := D.axialDepth_edist_le x y
    rw [heD] at hdepth
    have hreal := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg A.scale_pos.le hsqplus.le) ht)).mp (hdepth.trans hdist)
    have hscaled : D.scale * Real.sqrt (1 - epsilon) *
        |D.axialDepth x - D.axialDepth y| ≤
        (D.scale * Real.sqrt (1 - epsilon)) * ((101 / 100 : ℝ) * t) := by
      calc
        _ ≤ A.scale * Real.sqrt (1 + epsilon) * t := hreal
        _ ≤ ((101 / 100 : ℝ) * (D.scale * Real.sqrt (1 - epsilon))) * t :=
          mul_le_mul_of_nonneg_right hcoeff ht
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ (mul_pos D.scale_pos hsqpos)).mp hscaled
  have hNdepth (x : M) (hx : x ∈ N.carrier) : N.axialDepth x = L - |F x| := by
    rw [hFin x hx]
    simp only [EpsilonNeck.axialDepth, if_pos hx, heN, L]
  have hNdepth0 : N.axialDepth R.center = 0 := by
    simp only [EpsilonNeck.axialDepth, if_neg hyN]
  have hFabs (x : M) (hx : x ∈ N.carrier) : |F x| < L := by
    rw [hFin x hx]
    apply abs_lt.mpr
    simpa only [heN, L, mem_Ioo] using (N.coordinate_inverse_mem x hx).2
  have hBdistance (x : M) (hx : x ∈ B.carrier) :
      g.edist x R.center ≤ ENNReal.ofReal
        (B.scale * Real.sqrt (1 + epsilon) *
          (L - (B.coordinate_inverse x).2 + B0)) := by
    simpa only [heB, L, B0] using B.edist_le_positive_frontier hx hyBcl hyB
  let Q : Set M := B.region (L / 2) L
  have hQsub : Q ⊆ U := fun _ hx => hBU hx.1
  have hQabs (x : M) (hx : x ∈ Q) : 2 * L / 5 < |F x| := by
    by_cases hxN : x ∈ N.carrier
    · have hup := hBdistance x hx.1
      have ht : 0 ≤ L - (B.coordinate_inverse x).2 + B0 := by
        linarith [hx.2.2]
      have hd := htransfer B N heB heN ⟨x, hx.1, hxN⟩ x R.center
        (L - (B.coordinate_inverse x).2 + B0) ht hup
      rw [hNdepth x hxN, hNdepth0, sub_zero,
        abs_of_nonneg (sub_nonneg.mpr (hFabs x hxN).le)] at hd
      linarith only [hd, hB0L, hL, hx.2.1]
    · rw [hFout x hxN, abs_of_pos hL]
      linarith
  have hQimage : Q = B.coordinate_map '' (univ ×ˢ Ioo (L / 2) L) := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨B.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, B.coordinate_map_inverse hx.1⟩
    · rintro x ⟨z, hz, rfl⟩
      have hzs : z.2 ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
        rw [heB]
        change -L < z.2 ∧ z.2 < L
        exact ⟨by linarith [hz.2.1], hz.2.2⟩
      refine ⟨B.coordinate_map_mem ⟨mem_univ _, hzs⟩, ?_⟩
      rw [B.coordinate_inverse_map z hzs]
      exact hz.2
  have hQconnected : IsConnected Q := by
    rw [hQimage]
    apply (isConnected_univ.prod (isConnected_Ioo (by linarith : L / 2 < L))).image
    apply B.coordinate_map_smooth.continuousOn.mono
    intro z hz
    refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [heB]
    · change -L < z.2
      linarith [hz.2.1]
    · exact hz.2.2
  have hQzero (x : M) (hx : x ∈ Q) : F x ≠ 0 := by
    intro hz
    have h := hQabs x hx
    rw [hz, abs_zero] at h
    linarith
  have hQpositive (x : M) (hx : x ∈ Q) : 0 < F x := by
    rcases hQconnected.2.mapsTo_Ioi_or_Iio (hFcont.mono hQsub) hQzero with hp | hn
    · exact hp hx
    · exfalso
      by_cases heqab : a = b
      · have hxN : x ∈ N.carrier := by simpa only [N, B, heqab] using hx.1
        have hh : F x = (B.coordinate_inverse x).2 := by
          rw [hFin x hxN]
          simp only [N, B, heqab]
        have hnegative : F x < 0 := hn hx
        rw [hh] at hnegative
        linarith [hx.2.1]
      have hablt : a < b := lt_of_le_of_ne hab heqab
      obtain ⟨c, hc, hdisjoint⟩ := C.later_disjoint_negative_end a ha b hb hablt
      change c ∈ Ioo (-L) 0 at hc
      change Disjoint B.carrier (N.region (-L) c) at hdisjoint
      let S : Set M := N.coordinate_map '' (univ ×ˢ Icc c (-(2 * L / 5)))
      have hloS : -N.epsilon⁻¹ < c := by simpa only [heN] using hc.1
      have hhiS : -(2 * L / 5) < N.epsilon⁻¹ := by rw [heN]; change _ < L; linarith
      have hSclosed : IsClosed S := (N.isCompact_coordinate_slab hloS hhiS).isClosed
      have hSsub : S ⊆ N.carrier := by
        rintro z ⟨w, hw, rfl⟩
        exact N.coordinate_map_mem
          ⟨mem_univ _, hloS.trans_le hw.2.1, hw.2.2.trans_lt hhiS⟩
      have hQS : Q ⊆ S := by
        intro z hz
        have hzneg : F z < 0 := hn hz
        have hzN : z ∈ N.carrier := by
          by_contra hzout
          rw [hFout z hzout] at hzneg
          linarith
        have hlow : c ≤ (N.coordinate_inverse z).2 := by
          by_contra hnot
          apply (Set.disjoint_left.mp hdisjoint) hz.1
          refine ⟨hzN, ?_, lt_of_not_ge hnot⟩
          simpa only [heN] using (N.coordinate_inverse_mem z hzN).2.1
        have hhigh : (N.coordinate_inverse z).2 ≤ -(2 * L / 5) := by
          have h := hQabs z hz
          rw [abs_of_neg hzneg, hFin z hzN] at h
          linarith
        exact ⟨N.coordinate_inverse z, ⟨mem_univ _, hlow, hhigh⟩,
          N.coordinate_map_inverse hzN⟩
      have hyQ : R.center ∈ closure Q := by
        have h := B.mem_closure_final_tail_of_mem_positive_closure hyBcl hyB
          (a := L / 2) (by rw [heB]; change _ < L; linarith)
        simpa only [heB] using h
      exact hyN (hSsub (closure_minimal hQS hSclosed hyQ))
  have hslice : 3 * L / 4 ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
    rw [heB]
    change -L < 3 * L / 4 ∧ 3 * L / 4 < L
    constructor <;> linarith
  have hfirst (q : UnitTwoSphere) : 7 * L / 10 < F (B.coordinate_map (q, 3 * L / 4)) := by
    let x := B.coordinate_map (q, 3 * L / 4)
    have hxB : x ∈ B.carrier := B.coordinate_map_mem ⟨mem_univ _, hslice⟩
    have hh : (B.coordinate_inverse x).2 = 3 * L / 4 := by
      dsimp only [x]
      rw [B.coordinate_inverse_map (q, 3 * L / 4) hslice]
    have hxQ : x ∈ Q := ⟨hxB, by rw [hh]; constructor <;> linarith⟩
    have hpositive : 0 < F x := hQpositive x hxQ
    by_cases hxN : x ∈ N.carrier
    · have hup := hBdistance x hxB
      rw [hh] at hup
      have hd := htransfer B N heB heN ⟨x, hxB, hxN⟩ x R.center
        (L - 3 * L / 4 + B0) (by linarith) hup
      rw [hNdepth x hxN, hNdepth0, sub_zero,
        abs_of_nonneg (sub_nonneg.mpr (hFabs x hxN).le), abs_of_pos hpositive] at hd
      change 7 * L / 10 < F x
      linarith only [hd, hB0L, hL]
    · change 7 * L / 10 < F x
      rw [hFout x hxN]
      linarith
  have hcR := (R.mem_central_sphere_iff R.center).mp R.center_on_central_sphere
  have hinterBR : (B.carrier ∩ R.carrier).Nonempty := by
    obtain ⟨z, hzR, hzB⟩ := mem_closure_iff.mp hy R.carrier R.carrier_open hcR.1
    exact ⟨z, hzB.1, hzR⟩
  have hRdepthCenter : R.axialDepth R.center = L := by
    simp only [EpsilonNeck.axialDepth, if_pos hcR.1, hcR.2, abs_zero, sub_zero, heR, L]
  have hfrontierDistance (x : M) (hx : x ∈ closure (B.region 0 L))
      (hxout : x ∉ B.carrier) :
      g.edist x R.center ≤ ENNReal.ofReal (B.scale * Real.sqrt (1 + epsilon) * B0) := by
    let cB := B.scale * Real.sqrt (1 + epsilon)
    have hcB : 0 < cB := mul_pos B.scale_pos hsqplus
    have hbound (d : ℝ) (hd : 0 < d) :
        g.edist x R.center ≤ ENNReal.ofReal (cB * (d + B0)) := by
      have hxB : x ∈ closure (B.region 0 B.epsilon⁻¹) := by
        simpa only [heB] using hx
      have htail := B.mem_closure_final_tail_of_mem_positive_closure hxB hxout
        (a := L - d) (by rw [heB]; change _ < L; linarith)
      have hsub : B.region (L - d) B.epsilon⁻¹ ⊆
          {z | g.edist z R.center ≤ ENNReal.ofReal (cB * (d + B0))} := by
        intro z hz
        have h := hBdistance z hz.1
        exact h.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (by linarith [hz.2.1]) hcB.le))
      have hclosed : IsClosed
          {z | g.edist z R.center ≤ ENNReal.ofReal (cB * (d + B0))} :=
        isClosed_le (continuous_id.edist continuous_const) continuous_const
      exact closure_minimal hsub hclosed htail
    have hfinite : g.edist x R.center ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound 1 zero_lt_one)
    have hreal (d : ℝ) (hd : 0 < d) :
        (g.edist x R.center).toReal ≤ cB * (d + B0) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound d hd)
      rwa [ENNReal.toReal_ofReal (mul_nonneg hcB.le (by positivity))] at h
    have hlimit : (g.edist x R.center).toReal ≤ cB * B0 := by
      apply le_of_forall_pos_le_add
      intro d hd
      calc
        _ ≤ cB * (d / cB + B0) := hreal (d / cB) (div_pos hd hcB)
        _ = cB * B0 + d := by field_simp [hcB.ne']; ring
    apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (mul_nonneg hcB.le hB0.le)]
    exact hlimit
  have hfrontierSmall (x : M) (hx : x ∈ closure (B.region 0 L)) (hxout : x ∉ U) :
      x ∈ R.carrier ∧ |(R.coordinate_inverse x).2| < L / 100 := by
    have hup := hfrontierDistance x hx (fun hxB => hxout (hBU hxB))
    have hd := htransfer B R heB heR hinterBR x R.center B0 hB0.le hup
    rw [hRdepthCenter] at hd
    have hxR : x ∈ R.carrier := by
      by_contra houtR
      rw [show R.axialDepth x = 0 by
        simp only [EpsilonNeck.axialDepth, if_neg houtR], zero_sub,
        abs_neg, abs_of_pos hL] at hd
      linarith only [hd, hB0L, hL]
    refine ⟨hxR, ?_⟩
    have hdx : R.axialDepth x = L - |(R.coordinate_inverse x).2| := by
      simp only [EpsilonNeck.axialDepth, if_pos hxR, heR, L]
    rw [hdx, show (L - |(R.coordinate_inverse x).2|) - L =
      -|(R.coordinate_inverse x).2| by ring, abs_neg, abs_abs] at hd
    linarith only [hd, hB0L, hL]
  have hheight (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ioo (-L) L)
      (hxN : R.coordinate_map (q, t) ∈ N.carrier) :
      DifferentiableAt ℝ
          (fun r => (N.coordinate_inverse (R.coordinate_map (q, r))).2) t ∧
        |deriv (fun r => (N.coordinate_inverse (R.coordinate_map (q, r))).2) t| ≤
          (101 / 100 : ℝ) := by
    have hz : (q, t) ∈ R.cylinderDomain := by
      refine ⟨mem_univ _, ?_⟩
      simpa only [heR] using ht
    have hm := R.coordinate_map_smooth.contMDiffAt (R.cylinderDomain_open.mem_nhds hz)
    have hi := N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hxN)
    have hp : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun r : ℝ => (q, r)) t := contMDiffAt_const.prodMk contMDiffAt_id
    refine ⟨mdifferentiableAt_iff_differentiableAt.mp
      ((contMDiffAt_snd.comp t (hi.comp t (hm.comp t hp))).mdifferentiableAt (by simp)), ?_⟩
    have hxR : R.coordinate_map (q, t) ∈ R.carrier := R.coordinate_map_mem hz
    have hratio := (hscale N R (by rw [heN]; exact hes)
      (by rw [heR]; exact hes) ⟨R.coordinate_map (q, t), hxN, hxR⟩).2
    have hr : R.scale / N.scale ≤ 2 := by linarith [(abs_lt.mp hratio).2]
    obtain ⟨sigma, hsigma, hcross⟩ := haxis R N
      (by rw [heR]; exact hea) (by rw [heN]; exact hea)
      (R.coordinate_map (q, t)) hxR hxN
    have he := R.transition_height_axial_error N hz hxN (τ := (1 / 1000 : ℝ))
      hsigma (by norm_num)
      hratio.le hr (by simpa only [mul_assoc] using hcross.le)
    have hsigmaAbs : |sigma| = 1 := by
      rcases hsigma with rfl | rfl <;> norm_num
    have htriangle := abs_add_le
      (deriv (fun r => (N.coordinate_inverse (R.coordinate_map (q, r))).2) t - sigma) sigma
    rw [sub_add_cancel, hsigmaAbs] at htriangle
    linarith only [he, htriangle]
  have hbase (q : UnitTwoSphere) :
      R.coordinate_map (q, f q) ∈ U ∧ 7 * L / 10 < F (R.coordinate_map (q, f q)) := by
    have hx : R.coordinate_map (q, f q) ∈
        range (fun p : UnitTwoSphere => B.coordinate_map (p, 3 * L / 4)) := by
      rw [hgraph]
      exact mem_range_self q
    obtain ⟨p, hp⟩ := hx
    rw [← hp]
    exact ⟨hBU (B.coordinate_map_mem ⟨mem_univ _, hslice⟩), hfirst p⟩
  refine ⟨hfirst, ?_⟩
  intro q s hslo hshi
  let I : Set ℝ := uIcc (f q) s
  let gamma : ℝ → M := fun t => R.coordinate_map (q, t)
  have hparam (t : ℝ) (ht : t ∈ I) : -L < t ∧ t ≤ -(L / 20) := by
    change t ∈ uIcc (f q) s at ht
    rcases le_total (f q) s with hfs | hsf
    · rw [uIcc_of_le hfs] at ht
      exact ⟨by linarith [(hf q).1, ht.1], ht.2.trans hshi⟩
    · rw [uIcc_of_ge hsf] at ht
      exact ⟨hslo.trans_le ht.1, by linarith [(hf q).2, ht.2]⟩
  have hstrip (t : ℝ) (ht : t ∈ I) : t ∈ Ioo (-L) L :=
    ⟨(hparam t ht).1, by linarith [(hparam t ht).2]⟩
  have hlength (t : ℝ) (ht : t ∈ I) : |t - f q| < 4 * L / 5 := by
    apply abs_lt.mpr
    constructor <;> linarith [(hparam t ht).1, (hparam t ht).2, (hf q).1, (hf q).2]
  have hgammaOpen : ContinuousOn gamma (Ioo (-L) L) := by
    apply R.coordinate_map_smooth.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro t ht
    exact ⟨mem_univ _, by simpa only [heR, L, id_eq] using ht⟩
  have hgamma : ContinuousOn gamma I := hgammaOpen.mono hstrip
  have hprefixHeight (t : ℝ) (ht : t ∈ I)
      (hprefix : MapsTo gamma (uIcc (f q) t) U) : -L / 5 < F (gamma t) := by
    have hsub : uIcc (f q) t ⊆ I := uIcc_subset_uIcc_left ht
    have hbound : |F (gamma t) - F (gamma (f q))| ≤
        (101 / 100 : ℝ) * |t - f q| := by
      apply Real.abs_sub_le_mul_abs_sub_of_deriv_le_below
        (f := fun r => F (gamma r))
        (c := L) (k := (101 / 100 : ℝ))
        (hFcont.comp (hgamma.mono hsub) hprefix) (by norm_num)
      · intro r hr
        exact (hFbounds _ (hprefix hr)).2
      · intro r hr hbelow
        have hrI : r ∈ I := hsub (uIoo_subset_uIcc_self hr)
        have hrstrip := hstrip r hrI
        have hrN : gamma r ∈ N.carrier := by
          by_contra hrout
          rw [hFout _ hrout] at hbelow
          exact lt_irrefl _ hbelow
        have hc := hgammaOpen.continuousAt (isOpen_Ioo.mem_nhds hrstrip)
        have hmem : ∀ᶠ v in 𝓝 r, gamma v ∈ N.carrier :=
          hc.eventually (N.carrier_open.mem_nhds hrN)
        have heq : (fun v => F (gamma v)) =ᶠ[𝓝 r]
            (fun v => (N.coordinate_inverse (R.coordinate_map (q, v))).2) := by
          filter_upwards [hmem] with v hv
          exact hFin _ hv
        have hd := hheight q r hrstrip hrN
        refine ⟨hd.1.congr_of_eventuallyEq heq, ?_⟩
        rw [heq.deriv_eq]
        exact hd.2
    have hstrict := hbound.trans_lt
      (mul_lt_mul_of_pos_left (hlength t ht) (by norm_num : (0 : ℝ) < 101 / 100))
    have hstart : 7 * L / 10 < F (gamma (f q)) := (hbase q).2
    linarith only [(abs_lt.mp hstrict).1, hstart, hL]
  let Z : Set M := K ∪ closure (B.region (3 * L / 4) L)
  have hZclosed : IsClosed Z := hKclosed.union isClosed_closure
  have hguard : Z ∩ gamma '' I ⊆ U := by
    rintro x ⟨hx, t, ht, rfl⟩
    rcases hx with hxK | hxtail
    · exact hKsub hxK
    · by_contra hxout
      have hxpos : gamma t ∈ closure (B.region 0 L) := by
        apply closure_mono (s := B.region (3 * L / 4) L) ?_ hxtail
        intro z hz
        exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
      have hsmall := (hfrontierSmall (gamma t) hxpos hxout).2
      have hinverse : (R.coordinate_inverse (gamma t)).2 = t := by
        dsimp only [gamma]
        rw [R.coordinate_inverse_map (q, t) (by simpa only [heR] using hstrip t ht)]
      rw [hinverse] at hsmall
      linarith [(abs_lt.mp hsmall).1, (hparam t ht).2]
  have htrap (t : ℝ) (ht : t ∈ I) (hp : MapsTo gamma (uIcc (f q) t) U) :
      gamma t ∈ Z := by
    have hhigh := hprefixHeight t ht hp
    have hx := hp right_mem_uIcc
    rw [hcover] at hx
    rcases hx with (hxK | hxneg) | hxpos
    · exact Or.inl hxK
    · have hlow : F (gamma t) < -L / 2 := by
        rw [hFin _ hxneg.1]
        exact hxneg.2.2
      linarith
    · exact Or.inr (subset_closure hxpos)
  have hpath : MapsTo gamma I U :=
    hgamma.mapsTo_uIcc_of_closed_prefix_trap hopenU hZclosed (hbase q).1 hguard htrap
  refine ⟨hpath right_mem_uIcc, ?_⟩
  simpa only [neg_div, gamma] using hprefixHeight s right_mem_uIcc hpath

end PoincareConjecture
