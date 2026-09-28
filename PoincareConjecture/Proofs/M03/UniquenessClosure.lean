import PoincareConjecture.Proofs.M03.GlobalDifferenceEnergy
import PoincareConjecture.Proofs.M03.ConnectionDifferenceCoordinateRate
import PoincareConjecture.Proofs.M03.CoordinateIntegration
import PoincareConjecture.Proofs.M03.CurvatureRateAbsorption
import PoincareConjecture.Proofs.M03.CoupledDifferenceEnergy
import PoincareConjecture.Proofs.M03.MetricDifferenceEnergyRate
import PoincareConjecture.Statements.Ch03.ShortTime









set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle MeasureTheory Set

universe u

namespace PoincareConjecture.Proofs.M03


theorem exists_connection_difference_integral_rate_bound
    {n dH dA dS : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    let FH := V →L[ℝ] V →L[ℝ] ℝ
    let FA := V →L[ℝ] V →L[ℝ] V
    let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
    let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ
    let BA := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
    let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x
    letI : MeasurableSpace V := borel _
    letI : BorelSpace V := ⟨rfl⟩
    ∀ (qH : FH ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
      (qA : FA ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
      (qS : FS ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
      (s : Finset M) (φ : M → V → ℝ),
      (∀ a ∈ s, ContDiff ℝ ∞ (φ a) ∧ HasCompactSupport (φ a) ∧
        tsupport (φ a) ⊆ (chartAt V a).target) →
      ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J'),
        F.metric 0 = F'.metric 0 →
        ∀ (R R' : (t : ℝ) → (x : M) → BS x),
          (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
          (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
          ∀ (K : Set ℝ), IsCompact K → K ⊆ J ∩ J' →
            let c := chartAt V
            let eH := trivializationAt FH BH
            let eA := trivializationAt FA BA
            let eS := trivializationAt FS BS
            let H : (t : ℝ) → (x : M) → BH x :=
              fun t x => (F.metric t).inner x - (F'.metric t).inner x
            let A : (t : ℝ) → (x : M) → BA x := fun t x =>
              CovariantDerivative.difference
                (F.connection t).connection (F'.connection t).connection x
            let S : (t : ℝ) → (x : M) → BS x := fun t x => R t x - R' t x
            let fH : M → Fin dH → ℝ × V → ℝ := fun a i p =>
              qH ((eH a) (TotalSpace.mk' FH
                ((c a).symm p.2) (H p.1 ((c a).symm p.2)))).2 i
            let fA : M → Fin dA → ℝ × V → ℝ := fun a i p =>
              qA ((eA a) (TotalSpace.mk' FA
                ((c a).symm p.2) (A p.1 ((c a).symm p.2)))).2 i
            let fS : M → Fin dS → ℝ × V → ℝ := fun a i p =>
              qS ((eS a) (TotalSpace.mk' FS
                ((c a).symm p.2) (S p.1 ((c a).symm p.2)))).2 i
            let density : M → ℝ × V → ℝ := fun a p =>
              (∑ i : Fin dH, (fH a i p) ^ 2) +
                (∑ i : Fin dA, (fA a i p) ^ 2) +
                (∑ i : Fin dS, (fS a i p) ^ 2)
            ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ t ∈ interior K,
              (∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * fA a i (t, z) *
                fderiv ℝ (fA a i) (t, z) (1, 0)) ≤
                  ε * (∑ a ∈ s, ∑ i, ∫ z, φ a z ^ 2 * ∑ j : Fin n,
                    (fderiv ℝ (fun y => fS a i (t, y)) z
                      (EuclideanSpace.single j 1)) ^ 2) +
                  (C / ε + C) * (∑ a ∈ s, ∫ z in tsupport (φ a), density a (t, z)) := by
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let FH := V →L[ℝ] V →L[ℝ] ℝ
  let FA := V →L[ℝ] V →L[ℝ] V
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] ℝ
  let BA := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
  let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x
  let : NormedAddCommGroup FH := inferInstance
  let : NormedSpace ℝ FH := inferInstance
  let : NormedAddCommGroup FA := inferInstance
  let : NormedSpace ℝ FA := inferInstance
  let : NormedAddCommGroup FS := inferInstance
  let : NormedSpace ℝ FS := inferInstance
  let : ∀ x, AddCommGroup (BH x) := inferInstance
  let : ∀ x, Module ℝ (BH x) := inferInstance
  let : ∀ x, AddCommGroup (BA x) := inferInstance
  let : ∀ x, Module ℝ (BA x) := inferInstance
  let : ∀ x, AddCommGroup (BS x) := inferInstance
  let : ∀ x, Module ℝ (BS x) := inferInstance
  let : MeasurableSpace V := borel _
  let : BorelSpace V := ⟨rfl⟩
  classical
  dsimp only
  intro qH qA qS s φ hφ J J' F F' hinit R R' hR hR' K hK hKsub
  let c := chartAt V (M := M)
  let eH := trivializationAt FH BH
  let eA := trivializationAt FA BA
  let eS := trivializationAt FS BS
  let H : (t : ℝ) → (x : M) → BH x :=
    fun t x => (F.metric t).inner x - (F'.metric t).inner x
  let A : (t : ℝ) → (x : M) → BA x := fun t x =>
    CovariantDerivative.difference (F.connection t).connection (F'.connection t).connection x
  let S : (t : ℝ) → (x : M) → BS x := fun t x => R t x - R' t x
  let fH : M → Fin dH → ℝ × V → ℝ := fun a i p =>
    qH ((eH a) (TotalSpace.mk' FH ((c a).symm p.2) (H p.1 ((c a).symm p.2)))).2 i
  let fA : M → Fin dA → ℝ × V → ℝ := fun a i p =>
    qA ((eA a) (TotalSpace.mk' FA ((c a).symm p.2) (A p.1 ((c a).symm p.2)))).2 i
  let fS : M → Fin dS → ℝ × V → ℝ := fun a i p =>
    qS ((eS a) (TotalSpace.mk' FS ((c a).symm p.2) (S p.1 ((c a).symm p.2)))).2 i
  let density := fun (a : M) (p : ℝ × V) =>
    (∑ i, fH a i p ^ 2) + (∑ i, fA a i p ^ 2) + (∑ i, fS a i p ^ 2)
  obtain ⟨C0, hC0, hpoint⟩ := exists_connection_difference_coordinate_rate_bound
    qH qA qS s (fun a => tsupport (φ a))
    (fun a ha => ⟨(hφ a ha).2.1, (hφ a ha).2.2⟩)
    J J' F F' hinit R R' hR hR' K hK hKsub
  have hbound (a : M) (ha : a ∈ s) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ tsupport (φ a), φ a z ^ 2 ≤ B := by
    obtain ⟨B, hB⟩ := (hφ a ha).2.1.exists_bound_of_continuousOn
      ((hφ a ha).1.continuous.pow 2).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun z hz =>
      (le_abs_self _).trans ((hB z hz).trans (le_max_left _ _))⟩
  let bound := fun a : M => if ha : a ∈ s then Classical.choose (hbound a ha) else 0
  have hb (a : M) (ha : a ∈ s) :
      0 ≤ bound a ∧ ∀ z ∈ tsupport (φ a), φ a z ^ 2 ≤ bound a := by
    dsimp only [bound]
    rw [dif_pos ha]
    exact Classical.choose_spec (hbound a ha)
  let B : ℝ := ∑ a ∈ s, bound a
  have hB : 0 ≤ B := Finset.sum_nonneg (fun a ha => (hb a ha).1)
  have hBbound (a : M) (ha : a ∈ s) (z : V) (hz : z ∈ tsupport (φ a)) :
      φ a z ^ 2 ≤ B := (hb a ha).2 z hz |>.trans
    (Finset.single_le_sum (fun a ha => (hb a ha).1) ha)
  refine ⟨C0 * B, mul_nonneg hC0 hB, ?_⟩
  intro ε hε t ht
  have htJ : t ∈ J ∩ J' := hKsub (interior_subset ht)
  have htI : t ∈ interior (J ∩ J') := interior_mono hKsub ht
  obtain ⟨R0, hR0, hRsm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F.smooth F.connection
  obtain ⟨R1, hR1, hR'sm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F'.smooth F'.connection
  have hReq : R0 = R := by
    funext r x
    ext u v w
    exact (hR0 r x u v w).trans (hR r x u v w).symm
  have hR'eq : R1 = R' := by
    funext r x
    ext u v w
    exact (hR1 r x u v w).trans (hR' r x u v w).symm
  rw [hReq] at hRsm
  rw [hR'eq] at hR'sm
  have hF := F.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J from Set.inter_subset_left) subset_rfl)
  have hF' := F'.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J' from Set.inter_subset_right) subset_rfl)
  have hAsm := contMDiffOn_connection_family_difference hF hF' F.connection F'.connection
  change (∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * fA a i (t, z) *
      fderiv ℝ (fA a i) (t, z) (1, 0)) ≤
    ε * (∑ a ∈ s, ∑ i, ∫ z, φ a z ^ 2 * ∑ j : Fin n,
      (fderiv ℝ (fun y => fS a i (t, y)) z (EuclideanSpace.single j 1)) ^ 2) +
    (C0 * B / ε + C0 * B) * (∑ a ∈ s, ∫ z in tsupport (φ a), density a (t, z))
  rw [Finset.mul_sum s _ ε, Finset.mul_sum s _ (C0 * B / ε + C0 * B),
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  have hbaseH : (c a).source ⊆ (eH a).baseSet := by
    simp only [c, eH, V, FH, BH, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, mem_univ x⟩
  have hbaseA : (c a).source ⊆ (eA a).baseSet := by
    simp only [c, eA, V, FA, BA, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, hx⟩
  have hbaseS : (c a).source ⊆ (eS a).baseSet := by
    simp only [c, eS, V, FS, BS, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, hx, hx⟩
  have hHcoord : ContDiffOn ℝ ∞
      (fun p : ℝ × V => qH ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
        (H p.1 ((c a).symm p.2)))).2) ((J ∩ J') ×ˢ (c a).target) := by
    have h1 := contDiffOn_family_bundle_coordinates (E := BH) qH
      (fun r x => (F.metric r).inner x) hF a hbaseH
    have h2 := contDiffOn_family_bundle_coordinates (E := BH) qH
      (fun r x => (F'.metric r).inner x) hF' a hbaseH
    apply (h1.sub h2).congr
    intro p hp
    have hx := hbaseH ((c a).map_target hp.2)
    change qH ((eH a) (TotalSpace.mk' FH _ (_ - _))).2 = _
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eH a) _ hx, map_sub, map_sub]
    rfl
  have hAcoord := contDiffOn_family_bundle_coordinates (E := BA) qA A hAsm a hbaseA
  have hScoord : ContDiffOn ℝ ∞
      (fun p : ℝ × V => qS ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
        (S p.1 ((c a).symm p.2)))).2) ((J ∩ J') ×ˢ (c a).target) := by
    have h1 := contDiffOn_family_bundle_coordinates (E := BS) (J := J ∩ J') qS R
      (hRsm.mono (Set.prod_mono inter_subset_left subset_rfl)) a hbaseS
    have h2 := contDiffOn_family_bundle_coordinates (E := BS) (J := J ∩ J') qS R'
      (hR'sm.mono (Set.prod_mono inter_subset_right subset_rfl)) a hbaseS
    apply (h1.sub h2).congr
    intro p hp
    have hx := hbaseS ((c a).map_target hp.2)
    change qS ((eS a) (TotalSpace.mk' FS _ (_ - _))).2 = _
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eS a) _ hx, map_sub, map_sub]
    rfl
  have hH (i : Fin dH) : ContDiffOn ℝ ∞ (fun z => fH a i (t, z)) (c a).target := by
    simpa only [fH, Function.comp_def, EuclideanSpace.coe_proj, id_eq] using
      ((EuclideanSpace.proj i).contDiff.comp_contDiffOn hHcoord).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun z hz => ⟨htJ, hz⟩)
  have hA (i : Fin dA) : ContDiffOn ℝ ∞ (fA a i)
      (interior (J ∩ J') ×ˢ (c a).target) := by
    simpa only [fA, eA, c, Function.comp_def, EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj i).contDiff.comp_contDiffOn hAcoord).mono
      (Set.prod_mono interior_subset subset_rfl)
  have hAs (i : Fin dA) : ContDiffOn ℝ ∞ (fun z => fA a i (t, z)) (c a).target :=
    (hA i).comp (contDiffOn_const.prodMk contDiffOn_id) (fun z hz => ⟨htI, hz⟩)
  have hS (i : Fin dS) : ContDiffOn ℝ ∞ (fun z => fS a i (t, z)) (c a).target := by
    simpa only [fS, Function.comp_def, EuclideanSpace.coe_proj, id_eq] using
      ((EuclideanSpace.proj i).contDiff.comp_contDiffOn hScoord).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun z hz => ⟨htJ, hz⟩)
  have hAt (i : Fin dA) : ContinuousOn
      (fun z => fderiv ℝ (fA a i) (t, z) (1, 0)) (c a).target :=
    (((hA i).continuousOn_fderiv_of_isOpen
      (isOpen_interior.prod (c a).open_target) (by simp)).clm_apply continuousOn_const).comp
      (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨htI, hz⟩)
  have hSd (i : Fin dS) (j : Fin n) : ContinuousOn
      (fun z => fderiv ℝ (fun y => fS a i (t, y)) z
        (EuclideanSpace.single j 1)) (c a).target :=
    ((hS i).continuousOn_fderiv_of_isOpen (c a).open_target (by simp)).clm_apply
      continuousOn_const
  have hdc : ContinuousOn (fun z => density a (t, z)) (c a).target :=
    ((continuousOn_finsetSum _ (fun i _ => (hH i).continuousOn.pow 2)).add
      (continuousOn_finsetSum _ (fun i _ => (hAs i).continuousOn.pow 2))).add
      (continuousOn_finsetSum _ (fun i _ => (hS i).continuousOn.pow 2))
  have hdi : IntegrableOn (fun z => density a (t, z)) (tsupport (φ a)) :=
    ContinuousOn.integrableOn_compact (hφ a ha).2.1 (hdc.mono (hφ a ha).2.2)
  have hpatch (Q : V → ℝ) (hQ : ContinuousOn Q (c a).target)
      (hzero : ∀ z ∉ tsupport (φ a), Q z = 0) : Integrable Q := by
    have hc : HasCompactSupport Q := by
      apply (hφ a ha).2.1.mono'
      intro z hz
      by_contra hzφ
      exact hz (hzero z hzφ)
    have hcont : Continuous Q := by
      apply continuous_iff_continuousAt.mpr
      intro z
      by_cases hz : z ∈ (c a).target
      · exact hQ.continuousAt ((c a).open_target.mem_nhds hz)
      · apply continuousAt_const.congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport (φ a)).isOpen_compl.mem_nhds
          (show z ∉ tsupport (φ a) from fun h => hz ((hφ a ha).2.2 h))] with y hy
        exact hzero y hy
    exact hcont.integrable_of_hasCompactSupport hc
  let Rate (i : Fin dA) (z : V) :=
    2 * φ a z ^ 2 * fA a i (t, z) * fderiv ℝ (fA a i) (t, z) (1, 0)
  let Grad (i : Fin dS) (z : V) := φ a z ^ 2 * ∑ j : Fin n,
    (fderiv ℝ (fun y => fS a i (t, y)) z (EuclideanSpace.single j 1)) ^ 2
  have hRi (i : Fin dA) : Integrable (Rate i) := hpatch _
    (((continuousOn_const.mul ((hφ a ha).1.continuous.continuousOn.pow 2)).mul
      (hAs i).continuousOn).mul (hAt i))
    (fun z hz => by simp [Rate, image_eq_zero_of_notMem_tsupport hz])
  have hGi (i : Fin dS) : Integrable (Grad i) := hpatch _
    (((hφ a ha).1.continuous.continuousOn.pow 2).mul
      (continuousOn_finsetSum _ (fun j _ => (hSd i j).pow 2)))
    (fun z hz => by simp [Grad, image_eq_zero_of_notMem_tsupport hz])
  have hpi (z : V) : (∑ i, Rate i z) ≤ ε * (∑ i, Grad i z) +
      (C0 * B / ε + C0 * B) * (tsupport (φ a)).indicator
        (fun y => density a (t, y)) z := by
    by_cases hz : z ∈ tsupport (φ a)
    · rw [indicator_of_mem hz]
      have hp := mul_le_mul_of_nonneg_left (hpoint ε hε t ht a ha z hz)
        (sq_nonneg (φ a z))
      have hd0 : 0 ≤ density a (t, z) := by dsimp [density]; positivity
      have hb' := mul_le_mul_of_nonneg_right (hBbound a ha z hz)
        (mul_nonneg (show 0 ≤ C0 / ε + C0 by positivity) hd0)
      have hcoeff : B * (C0 / ε + C0) = C0 * B / ε + C0 * B := by ring
      have hrate : (∑ i, Rate i z) = φ a z ^ 2 *
          (∑ i, 2 * fA a i (t, z) * fderiv ℝ (fA a i) (t, z) (1, 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [Rate]
        ring
      have hgrad : (∑ i, Grad i z) = φ a z ^ 2 *
          (∑ i, ∑ j : Fin n, (fderiv ℝ (fun y => fS a i (t, y)) z
            (EuclideanSpace.single j 1)) ^ 2) := by
        simp only [Grad, Finset.mul_sum]
      rw [hrate, hgrad, ← hcoeff]
      change φ a z ^ 2 * (∑ i, 2 * fA a i (t, z) *
          fderiv ℝ (fA a i) (t, z) (1, 0)) ≤ φ a z ^ 2 *
          (ε * (∑ i, ∑ j : Fin n, (fderiv ℝ (fun y => fS a i (t, y)) z
            (EuclideanSpace.single j 1)) ^ 2) + (C0 / ε + C0) * density a (t, z)) at hp
      nlinarith only [hp, hb']
    · simp [Rate, Grad, indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz]
  have hineq := integral_mono (integrable_finsetSum _ (fun i _ => hRi i))
    (((integrable_finsetSum _ (fun i _ => hGi i)).const_mul ε).add
      ((hdi.integrable_indicator (isClosed_tsupport (φ a)).measurableSet).const_mul
        (C0 * B / ε + C0 * B))) hpi
  simp only [Pi.add_apply, integral_finsetSum _ (fun i _ => hRi i),
    integral_add ((integrable_finsetSum _ (fun i _ => hGi i)).const_mul ε)
      ((hdi.integrable_indicator (isClosed_tsupport (φ a)).measurableSet).const_mul
        (C0 * B / ε + C0 * B)), integral_const_mul,
    integral_finsetSum _ (fun i _ => hGi i),
    Rate, Grad, Pi.smul_apply, smul_eq_mul] at hineq
  rw [integral_indicator (f := fun z : V => density a (t, z))
    (μ := volume) (isClosed_tsupport (φ a)).measurableSet] at hineq
  exact hineq


theorem exists_curvature_difference_integral_rate_bound
    {n dH dA dS : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    let FH := V →L[ℝ] V →L[ℝ] ℝ
    let FA := V →L[ℝ] V →L[ℝ] V
    let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
    let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ
    let BA := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
    let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x
    letI : MeasurableSpace V := borel _
    letI : BorelSpace V := ⟨rfl⟩
    ∀ (qH : FH ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
      (qA : FA ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
      (qS : FS ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
      (s : Finset M) (φ : M → V → ℝ),
      (∀ a ∈ s, ContDiff ℝ ∞ (φ a) ∧ HasCompactSupport (φ a) ∧
        tsupport (φ a) ⊆ (chartAt V a).target) →
      ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J')
        (R R' : (t : ℝ) → (x : M) → BS x),
        (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
        (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
        ∀ (K : Set ℝ), IsCompact K → K ⊆ J ∩ J' →
          let c := chartAt V
          let eH := trivializationAt FH BH
          let eA := trivializationAt FA BA
          let eS := trivializationAt FS BS
          let H : (t : ℝ) → (x : M) → BH x :=
            fun t x => (F.metric t).inner x - (F'.metric t).inner x
          let A : (t : ℝ) → (x : M) → BA x := fun t x =>
            CovariantDerivative.difference
              (F.connection t).connection (F'.connection t).connection x
          let S : (t : ℝ) → (x : M) → BS x := fun t x => R t x - R' t x
          let fH : M → Fin dH → ℝ × V → ℝ := fun a i p =>
            qH ((eH a) (TotalSpace.mk' FH
              ((c a).symm p.2) (H p.1 ((c a).symm p.2)))).2 i
          let fA : M → Fin dA → ℝ × V → ℝ := fun a i p =>
            qA ((eA a) (TotalSpace.mk' FA
              ((c a).symm p.2) (A p.1 ((c a).symm p.2)))).2 i
          let fS : M → Fin dS → ℝ × V → ℝ := fun a i p =>
            qS ((eS a) (TotalSpace.mk' FS
              ((c a).symm p.2) (S p.1 ((c a).symm p.2)))).2 i
          let density : M → ℝ × V → ℝ := fun a p =>
            (∑ i : Fin dH, (fH a i p) ^ 2) +
              (∑ i : Fin dA, (fA a i p) ^ 2) + (∑ i : Fin dS, (fS a i p) ^ 2)
          ∃ lambda C : ℝ, 0 < lambda ∧ 0 ≤ C ∧ ∀ t ∈ interior K,
            (∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * fS a i (t, z) *
              fderiv ℝ (fS a i) (t, z) (1, 0)) ≤
                C * (∑ a ∈ s, ∫ z in tsupport (φ a), density a (t, z)) -
                lambda / 4 * (∑ a ∈ s, ∑ i, ∫ z, φ a z ^ 2 * ∑ j : Fin n,
                  (fderiv ℝ (fun y => fS a i (t, y)) z
                    (EuclideanSpace.single j 1)) ^ 2) := by
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let FH := V →L[ℝ] V →L[ℝ] ℝ
  let FA := V →L[ℝ] V →L[ℝ] V
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] ℝ
  let BA := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
  let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x
  let : NormedAddCommGroup FH := inferInstance
  let : NormedSpace ℝ FH := inferInstance
  let : NormedAddCommGroup FA := inferInstance
  let : NormedSpace ℝ FA := inferInstance
  let : NormedAddCommGroup FS := inferInstance
  let : NormedSpace ℝ FS := inferInstance
  let : ∀ x, AddCommGroup (BH x) := inferInstance
  let : ∀ x, Module ℝ (BH x) := inferInstance
  let : ∀ x, AddCommGroup (BA x) := inferInstance
  let : ∀ x, Module ℝ (BA x) := inferInstance
  let : ∀ x, AddCommGroup (BS x) := inferInstance
  let : ∀ x, Module ℝ (BS x) := inferInstance
  let : MeasurableSpace V := borel _
  let : BorelSpace V := ⟨rfl⟩
  classical
  dsimp only
  intro qH qA qS s φ hφ J J' F F' R R' hR hR' K hK hKsub
  let c := chartAt V (M := M)
  let eT := fun a : M => trivializationAt V (TangentSpace (𝓡 n)) a
  let eH := trivializationAt FH BH
  let eA := trivializationAt FA BA
  let eS := trivializationAt FS BS
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  let frame := fun a i x => (eT a).symmL ℝ x (e i)
  let G := fun (g : ℝ → RiemannianMetric n M) a (p : ℝ × V) =>
    ((eH a) (TotalSpace.mk' FH ((c a).symm p.2) ((g p.1).inner ((c a).symm p.2)))).2
  let ai := fun g a p i d => ((G g a p).inverse (EuclideanSpace.proj d)) i
  let gamma := fun (g : ℝ → RiemannianMetric n M)
      (D : (t : ℝ) → LeviCivitaData (g t)) a (p : ℝ × V) i j l =>
    ((eT a).continuousLinearMapAt ℝ ((c a).symm p.2)
      ((D p.1).connection (frame a j) ((c a).symm p.2)
        (frame a i ((c a).symm p.2)))) l
  let Hbar := fun a (p : ℝ × V) => ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
    ((F.metric p.1).inner ((c a).symm p.2) - (F'.metric p.1).inner ((c a).symm p.2)))).2
  let Abar := fun a (p : ℝ × V) => ((eA a) (TotalSpace.mk' FA ((c a).symm p.2)
    (CovariantDerivative.difference (F.connection p.1).connection
      (F'.connection p.1).connection ((c a).symm p.2)))).2
  let Sbar := fun a (p : ℝ × V) => ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
    (R p.1 ((c a).symm p.2) - R' p.1 ((c a).symm p.2)))).2
  let Rbar := fun a (p : ℝ × V) => ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
    (R p.1 ((c a).symm p.2)))).2
  let Rbar' := fun a (p : ℝ × V) => ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
    (R' p.1 ((c a).symm p.2)))).2
  let raw := fun (T : FS) l j k m => (T (e j) (e k) (e m)) l
  let ag := fun (A : FA) i j l => (A (e j) (e i)) l
  let act := fun (g : Fin n → Fin n → Fin n → ℝ)
      (T : Fin n → Fin n → Fin n → Fin n → ℝ) d l j k m =>
    ∑ p : Fin n, (g d p l * T p j k m - g d j p * T l p k m -
      g d k p * T l j p m - g d m p * T l j k p)
  let div := fun (g : Fin n → Fin n → Fin n → ℝ)
      (T : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) l j k m =>
    ∑ i : Fin n, (act g (T i) i l j k m + ∑ p, g i p i * T p l j k m)
  let kp := fun a (p : ℝ × V) d l j k m =>
    fderiv ℝ (fun z => raw (Rbar' a (p.1, z)) l j k m) p.2 (e d) +
      act (gamma F'.metric F'.connection a p) (raw (Rbar' a p)) d l j k m
  let vp := fun a p i l j k m => ∑ d, ai F'.metric a p i d * kp a p d l j k m
  let w := fun a p i l j k m => ∑ d : Fin n,
    (ai F.metric a p i d * act (gamma F.metric F.connection a p)
        (raw (Sbar a p)) d l j k m +
      -((G F.metric a p).inverse
        (Hbar a p ((G F'.metric a p).inverse (EuclideanSpace.proj d)))) i *
          kp a p d l j k m +
      ai F.metric a p i d * act (ag (Abar a p)) (raw (Rbar' a p)) d l j k m)
  let fH := fun a i p => qH (Hbar a p) i
  let fA := fun a i p => qA (Abar a p) i
  let fS := fun a i p => qS (Sbar a p) i
  let principal := fun a (p : ℝ × V) i l j k m =>
    ∑ d, ai F.metric a p i d * ∑ β : Fin dS,
      raw (qS.symm (EuclideanSpace.single β 1)) l j k m *
        fderiv ℝ (fun z => fS a β (p.1, z)) p.2 (e d)
  let B : Fin n → Fin n → Fin n → Fin n → FS := fun l j k m => (EuclideanSpace.proj j).smulRight
    ((EuclideanSpace.proj k).smulRight ((EuclideanSpace.proj m).smulRight (e l)))
  let contract := fun (T : Fin n → Fin n → Fin n → Fin n → ℝ) α =>
    ∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) α * T l j k m
  let U := fun a p α i => contract (w a p i) α
  let W := fun a p α => contract
    (div (gamma F.metric F.connection a p) (principal a p + w a p) +
      div (ag (Abar a p)) (vp a p)) α
  let ric := fun (T : FS) u v => ∑ k, (T (e k) u v) k
  let reaction := fun (A : FH) (T : FS) u v w =>
    ∑ i : Fin n, ∑ j : Fin n, (A.inverse (EuclideanSpace.proj j)) i •
      (T (T u v (e i)) (e j) w - (2 : ℝ) • T v (e i) (T (e j) u w) +
        (2 : ℝ) • T (e i) u (T v (e j) w) + ric T (T u v w) (e i) • e j -
        ric T u (e i) • T (e j) v w - ric T v (e i) • T u (e j) w -
        ric T w (e i) • T u v (e j))
  let qQ := fun a α p => ∑ l, ∑ j, ∑ k, ∑ m, qS (B l j k m) α *
    ((reaction (G F.metric a p) (Rbar a p) (e j) (e k) (e m) -
      reaction (G F'.metric a p) (Rbar' a p) (e j) (e k) (e m)) l)
  let density := fun a p => (∑ i : Fin dH, (fH a i p) ^ 2) +
    (∑ i : Fin dA, (fA a i p) ^ 2) + (∑ i : Fin dS, (fS a i p) ^ 2)
  obtain ⟨CU, CR, hCU, hCR, hflux⟩ := exists_curvature_difference_flux_coordinate_bound
    qH qA qS s (fun a => tsupport (φ a))
    (fun a ha => ⟨(hφ a ha).2.1, (hφ a ha).2.2⟩)
    J J' F F' R R' hR hR' K hK hKsub
  obtain ⟨CQ, hCQ, hreaction⟩ := exists_curvature_reaction_coordinate_energy_bound
    qH qS s (fun a => tsupport (φ a))
    (fun a ha => ⟨(hφ a ha).2.1, (hφ a ha).2.2⟩)
    J J' F F' R R' hR hR' K hK hKsub
  have hell (a : M) (ha : a ∈ s) : ∃ lambda : ℝ, 0 < lambda ∧
      ∀ t ∈ K, ∀ z ∈ tsupport (φ a), ∀ v : Fin n → ℝ,
        lambda * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, ai F.metric a (t, z) i j * v i * v j :=
    exists_ricciFlow_coordinate_ellipticity F hK (fun t ht => (hKsub ht).1) a
      (hφ a ha).2.1 (hφ a ha).2.2
  let localLambda := fun a : M => if ha : a ∈ s then Classical.choose (hell a ha) else 1
  have hlocalLambda (a : M) (ha : a ∈ s) : 0 < localLambda a ∧
      ∀ t ∈ K, ∀ z ∈ tsupport (φ a), ∀ v : Fin n → ℝ,
        localLambda a * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, ai F.metric a (t, z) i j * v i * v j := by
    dsimp only [localLambda]
    rw [dif_pos ha]
    exact Classical.choose_spec (hell a ha)
  let lambdas := insert (1 : ℝ) (s.image localLambda)
  have hne : lambdas.Nonempty := Finset.insert_nonempty _ _
  let lambda := lambdas.min' hne
  have hlambda : 0 < lambda := by
    have hm : lambda ∈ lambdas := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]
      norm_num
    · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hm
      rw [← heq]
      exact (hlocalLambda a ha).1
  have haell (a : M) (ha : a ∈ s) (t : ℝ) (ht : t ∈ K)
      (z : V) (hz : z ∈ tsupport (φ a)) (v : Fin n → ℝ) :
      lambda * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, ai F.metric a (t, z) i j * v i * v j := by
    have hle : lambda ≤ localLambda a := Finset.min'_le _ _
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
    exact (mul_le_mul_of_nonneg_right hle (Finset.sum_nonneg (fun i _ => sq_nonneg _))).trans
      ((hlocalLambda a ha).2 t ht z hz v)
  have hbaseT (a : M) {z : V} (hz : z ∈ (c a).target) :
      (c a).symm z ∈ (eT a).baseSet := by
    simpa only [eT, c, V, TangentBundle.trivializationAt_baseSet] using (c a).map_target hz
  have hinverse (a : M) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => (G F.metric a p).inverse) (J ×ˢ (c a).target) := by
    have hs := (contMDiffOn_family_metric_frame_inverse F.smooth a).2.2
    have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ (fun p : ℝ × V => (p.1, (c a).symm p.2))
        (J ×ˢ (c a).target) := by
      apply contMDiffOn_fst.prodMk
      exact (contMDiffOn_chart_symm (H := V) (x := a)).comp contMDiffOn_snd
        (fun p hp => hp.2)
    have hcomp := hs.comp hc (fun p hp => ⟨hp.1, hbaseT a hp.2⟩)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcomp
    exact hcomp.contDiffOn
  have haJoint (a : M) (i j : Fin n) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => ai F.metric a p i j) (J ×ˢ (c a).target) := by
    simpa only [ai, Function.comp_def, EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn
        ((hinverse a).clm_apply (contDiffOn_const (c := EuclideanSpace.proj j)))
  let CT := CR / (lambda / 4) + CR + CQ
  have hCT : 0 ≤ CT := by dsimp only [CT]; positivity
  have hintegral (a : M) (ha : a ∈ s) :=
    exists_uniform_curvature_coordinate_integral_rate_bound (I := Fin dS) hK
      (c a).open_target
      (a := fun t z i j => ai F.metric a (t, z) i j)
      (fun i j => (haJoint a i j).continuousOn.mono
        (Set.prod_mono (fun t ht => (hKsub ht).1) subset_rfl))
      (fun t ht i j => ((haJoint a i j).comp
        (contDiffOn_const.prodMk contDiffOn_id)
        (fun z hz => ⟨(hKsub ht).1, hz⟩)).of_le (by simp))
      ((hφ a ha).1.of_le (by simp)) (hφ a ha).2.1 (hφ a ha).2.2
      hlambda hCU hCT (haell a ha)
  let localC := fun a : M => if ha : a ∈ s then Classical.choose (hintegral a ha) else 0
  have hlocalC (a : M) (ha : a ∈ s) : 0 ≤ localC a := by
    dsimp only [localC]
    rw [dif_pos ha]
    exact (Classical.choose_spec (hintegral a ha)).1
  let C := ∑ a ∈ s, localC a
  have hC : 0 ≤ C := Finset.sum_nonneg (fun a ha => hlocalC a ha)
  refine ⟨lambda, C, hlambda, hC, ?_⟩
  intro t ht
  have htK := interior_subset ht
  have htJ : t ∈ J ∩ J' := hKsub htK
  have htI : t ∈ interior (J ∩ J') := interior_mono hKsub ht
  obtain ⟨R0, hR0, hRsm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F.smooth F.connection
  obtain ⟨R1, hR1, hR'sm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F'.smooth F'.connection
  have hReq : R0 = R := by
    funext r x
    ext u v w
    exact (hR0 r x u v w).trans (hR r x u v w).symm
  have hR'eq : R1 = R' := by
    funext r x
    ext u v w
    exact (hR1 r x u v w).trans (hR' r x u v w).symm
  rw [hReq] at hRsm
  rw [hR'eq] at hR'sm
  have hF := F.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J from inter_subset_left) subset_rfl)
  have hF' := F'.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J' from inter_subset_right) subset_rfl)
  have hAsm := contMDiffOn_connection_family_difference hF hF' F.connection F'.connection
  change (∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * fS a i (t, z) *
      fderiv ℝ (fS a i) (t, z) (1, 0)) ≤
    C * (∑ a ∈ s, ∫ z in tsupport (φ a), density a (t, z)) -
    lambda / 4 * (∑ a ∈ s, ∑ i, ∫ z, φ a z ^ 2 * ∑ j : Fin n,
      (fderiv ℝ (fun y => fS a i (t, y)) z (EuclideanSpace.single j 1)) ^ 2)
  rw [Finset.mul_sum s _ C, Finset.mul_sum s _ (lambda / 4), ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a ha
  have hbaseH : (c a).source ⊆ (eH a).baseSet := by
    simp only [c, eH, V, FH, BH, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, mem_univ x⟩
  have hbaseA : (c a).source ⊆ (eA a).baseSet := by
    simp only [c, eA, V, FA, BA, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, hx⟩
  have hbaseS : (c a).source ⊆ (eS a).baseSet := by
    simp only [c, eS, V, FS, BS, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    exact fun x hx => ⟨hx, hx, hx, hx⟩
  have hHcoord : ContDiffOn ℝ ∞ (fun p : ℝ × V => qH (Hbar a p))
      ((J ∩ J') ×ˢ (c a).target) := by
    have h1 := contDiffOn_family_bundle_coordinates (E := BH) qH
      (fun r x => (F.metric r).inner x) hF a hbaseH
    have h2 := contDiffOn_family_bundle_coordinates (E := BH) qH
      (fun r x => (F'.metric r).inner x) hF' a hbaseH
    apply (h1.sub h2).congr
    intro p hp
    change qH ((eH a) (TotalSpace.mk' FH _ (_ - _))).2 = _
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eH a) _
      (hbaseH ((c a).map_target hp.2)), map_sub, map_sub]
    rfl
  have hAcoord := contDiffOn_family_bundle_coordinates (E := BA) qA
    (fun r x => CovariantDerivative.difference
      (F.connection r).connection (F'.connection r).connection x) hAsm a hbaseA
  have hScoord : ContDiffOn ℝ ∞ (fun p : ℝ × V => qS (Sbar a p))
      ((J ∩ J') ×ˢ (c a).target) := by
    have h1 := contDiffOn_family_bundle_coordinates (E := BS) (J := J ∩ J') qS R
      (hRsm.mono (Set.prod_mono inter_subset_left subset_rfl)) a hbaseS
    have h2 := contDiffOn_family_bundle_coordinates (E := BS) (J := J ∩ J') qS R'
      (hR'sm.mono (Set.prod_mono inter_subset_right subset_rfl)) a hbaseS
    apply (h1.sub h2).congr
    intro p hp
    change qS ((eS a) (TotalSpace.mk' FS _ (_ - _))).2 = _
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eS a) _
      (hbaseS ((c a).map_target hp.2)), map_sub, map_sub]
    rfl
  have hH (i : Fin dH) : ContinuousOn (fun z => fH a i (t, z)) (c a).target :=
    ((EuclideanSpace.proj i).continuous.comp_continuousOn hHcoord.continuousOn).comp
      (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨htJ, hz⟩)
  have hA (i : Fin dA) : ContinuousOn (fun z => fA a i (t, z)) (c a).target :=
    ((EuclideanSpace.proj i).continuous.comp_continuousOn hAcoord.continuousOn).comp
      (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨htJ, hz⟩)
  have hS (i : Fin dS) : ContDiffOn ℝ ∞ (fun z => fS a i (t, z)) (c a).target :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hScoord).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun z hz => ⟨htJ, hz⟩)
  have hSj (i : Fin dS) : ContDiffOn ℝ ∞ (fS a i)
      (interior (J ∩ J') ×ˢ (c a).target) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hScoord).mono
      (Set.prod_mono interior_subset subset_rfl)
  have hSt (i : Fin dS) : ContinuousOn
      (fun z => fderiv ℝ (fS a i) (t, z) (1, 0)) (c a).target :=
    (((hSj i).continuousOn_fderiv_of_isOpen
      (isOpen_interior.prod (c a).open_target) (by simp)).clm_apply continuousOn_const).comp
      (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨htI, hz⟩)
  have hdensity : ContinuousOn (fun z => density a (t, z)) (c a).target :=
    ((continuousOn_finsetSum _ (fun i _ => (hH i).pow 2)).add
      (continuousOn_finsetSum _ (fun i _ => (hA i).pow 2))).add
      (continuousOn_finsetSum _ (fun i _ => (hS i).continuousOn.pow 2))
  have hPDE := ricciFlow_curvature_bundle_difference_coordinate_pde
    qS J J' F F' R R' hR hR' a t htI
  have hU : ∀ α i, ContDiffOn ℝ 1 (fun z => U a (t, z) α i) (c a).target := hPDE.1
  have hW : ∀ α, ContinuousOn (fun z => W a (t, z) α + qQ a α (t, z)) (c a).target :=
    hPDE.2.1
  have htime : ∀ α, ∀ z ∈ (c a).target,
      fderiv ℝ (fS a α) (t, z) (1, 0) =
        (∑ i, fderiv ℝ (fun y => ∑ d, ai F.metric a (t, y) i d *
          fderiv ℝ (fun z => fS a α (t, z)) y (e d)) z (e i)) +
        (∑ i, fderiv ℝ (fun y => U a (t, y) α i) z (e i)) +
        (W a (t, z) α + qQ a α (t, z)) := hPDE.2.2
  have hpoint (z : V) (hz : z ∈ tsupport (φ a)) :
      (∑ α, 2 * fS a α (t, z) * (W a (t, z) α + qQ a α (t, z))) ≤
        lambda / 4 * (∑ α, ∑ i, (fderiv ℝ (fun y => fS a α (t, y)) z (e i)) ^ 2) +
          CT * density a (t, z) := by
    have hg := (hflux a ha t htK z hz).2 (lambda / 4) (by positivity)
    have hq := hreaction a ha t htK z hz
    have hq' : (∑ α, 2 * fS a α (t, z) * qQ a α (t, z)) ≤ CQ * density a (t, z) := by
      apply hq.trans
      apply mul_le_mul_of_nonneg_left _ hCQ
      dsimp only [density]
      have hA0 : 0 ≤ ∑ i, fA a i (t, z) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      linarith
    change (∑ α, 2 * fS a α (t, z) * W a (t, z) α) ≤
      lambda / 4 * (∑ α, ∑ i, (fderiv ℝ (fun y => fS a α (t, y)) z (e i)) ^ 2) +
        (CR / (lambda / 4) + CR) * density a (t, z) at hg
    simp only [mul_add, Finset.sum_add_distrib]
    dsimp only [CT]
    linarith
  have hlocal := (Classical.choose_spec (hintegral a ha)).2 t htK
    (fun α z => fS a α (t, z))
    (fun α => (hS α).of_le (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
    (fun α z i => U a (t, z) α i) hU
    (fun α z => W a (t, z) α + qQ a α (t, z))
    (fun α z => fderiv ℝ (fS a α) (t, z) (1, 0)) hW hSt
    (fun z => density a (t, z)) hdensity
    (fun z _ => by dsimp only [density]; positivity)
    (fun z _ => by
      dsimp only [density]
      have hH0 : 0 ≤ ∑ i, fH a i (t, z) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hA0 : 0 ≤ ∑ i, fA a i (t, z) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      linarith)
    (fun z hz => (hflux a ha t htK z hz).1) hpoint htime
  have hco : Classical.choose (hintegral a ha) ≤ C := by
    have hle : localC a ≤ C := Finset.single_le_sum (fun b hb => hlocalC b hb) ha
    simpa only [localC, dif_pos ha] using hle
  exact hlocal.trans (sub_le_sub_right
    (mul_le_mul_of_nonneg_right hco (integral_nonneg (fun z => by
      dsimp only [density]; positivity))) _)

theorem eqOn_of_compact_slab_rates
    {E : ℝ → ℝ} {J J' : Set ℝ}
    (hJ : J.OrdConnected) (hJ' : J'.OrdConnected)
    (hJ0 : IsLeast J 0) (hJ'0 : IsLeast J' 0)
    (hE0 : E 0 = 0)
    (hcertificate : ∀ K : Set ℝ, IsCompact K → K ⊆ J ∩ J' →
      ∃ C : ℝ, ContinuousOn E K ∧
        (∀ t ∈ K, 0 ≤ E t) ∧
        (∀ t ∈ interior K, DifferentiableAt ℝ E t) ∧
        (∀ t ∈ interior K, deriv E t ≤ C * E t)) :
    EqOn E (fun _ => 0) (J ∩ J') := by
  intro t ht
  have ht0 : 0 ≤ t := hJ0.2 ht.1
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · exact hE0
  let K : Set ℝ := Icc 0 t
  have hKsub : K ⊆ J ∩ J' := by
    intro s hs
    exact ⟨hJ.out hJ0.1 ht.1 hs, hJ'.out hJ'0.1 ht.2 hs⟩
  obtain ⟨C, hcont, hnonneg, hdiff, hrate⟩ :=
    hcertificate K (isCompact_Icc) hKsub
  have hzero := eq_zero_on_interval_of_deriv_le_mul
    (a := (0 : ℝ)) (b := t) hcont
    (fun s hs => hdiff s (by simpa [K] using hs)) hE0
    (fun s hs => hnonneg s (by simpa [K] using hs))
    (fun s hs => hrate s (by simpa [K] using hs))
  exact hzero ⟨htpos.le, le_rfl⟩


theorem ricciFlowUniqueness_of_difference_energy
    {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] : RicciFlowUniqueness n M := by
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let FH := V →L[ℝ] V →L[ℝ] ℝ
  let FA := V →L[ℝ] V →L[ℝ] V
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] ℝ
  let BA := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
  let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x
  let : NormedAddCommGroup FH := inferInstance
  let : NormedSpace ℝ FH := inferInstance
  let : NormedAddCommGroup FA := inferInstance
  let : NormedSpace ℝ FA := inferInstance
  let : NormedAddCommGroup FS := inferInstance
  let : NormedSpace ℝ FS := inferInstance
  let : ∀ x, AddCommGroup (BH x) := inferInstance
  let : ∀ x, Module ℝ (BH x) := inferInstance
  let : ∀ x, AddCommGroup (BA x) := inferInstance
  let : ∀ x, Module ℝ (BA x) := inferInstance
  let : ∀ x, AddCommGroup (BS x) := inferInstance
  let : ∀ x, Module ℝ (BS x) := inferInstance
  let : MeasurableSpace V := borel _
  let : BorelSpace V := ⟨rfl⟩
  classical
  intro J J' F F' hJ0 hJ'0 hinit
  obtain ⟨qH, qA, qS, s, φ, C0, hC0, hφ, _, hfamily⟩ :=
    exists_ricci_flow_coupled_difference_energy (n := n) (M := M)
  obtain ⟨R, R', hR, hR', hRsm, hR'sm, hcert⟩ := hfamily J J' F F'
  let c := chartAt V (M := M)
  let eH := trivializationAt FH BH
  let eA := trivializationAt FA BA
  let eS := trivializationAt FS BS
  let H : (t : ℝ) → (x : M) → BH x :=
    fun t x => (F.metric t).inner x - (F'.metric t).inner x
  let A : (t : ℝ) → (x : M) → BA x := fun t x =>
    CovariantDerivative.difference (F.connection t).connection (F'.connection t).connection x
  let S : (t : ℝ) → (x : M) → BS x := fun t x => R t x - R' t x
  let fH := fun (a : M) (i : Fin (Module.finrank ℝ FH)) (p : ℝ × V) =>
    qH ((eH a) (TotalSpace.mk' FH ((c a).symm p.2) (H p.1 ((c a).symm p.2)))).2 i
  let fA := fun (a : M) (i : Fin (Module.finrank ℝ FA)) (p : ℝ × V) =>
    qA ((eA a) (TotalSpace.mk' FA ((c a).symm p.2) (A p.1 ((c a).symm p.2)))).2 i
  let fS := fun (a : M) (i : Fin (Module.finrank ℝ FS)) (p : ℝ × V) =>
    qS ((eS a) (TotalSpace.mk' FS ((c a).symm p.2) (S p.1 ((c a).symm p.2)))).2 i
  let energy := fun {d : ℕ} (f : M → Fin d → ℝ × V → ℝ) (t : ℝ) =>
    ∑ a ∈ s, ∑ i, ∫ z, (φ a z * f a i (t, z)) ^ 2
  let rate := fun {d : ℕ} (f : M → Fin d → ℝ × V → ℝ) (t : ℝ) =>
    ∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * f a i (t, z) *
      fderiv ℝ (f a i) (t, z) (1, 0)
  let E := fun t => energy fH t + energy fA t + energy fS t
  let density := fun (a : M) (p : ℝ × V) =>
    (∑ i, fH a i p ^ 2) + (∑ i, fA a i p ^ 2) + (∑ i, fS a i p ^ 2)
  let Rho := fun t => ∑ a ∈ s, ∫ z in tsupport (φ a), density a (t, z)
  let G := fun t => ∑ a ∈ s, ∑ i, ∫ z, φ a z ^ 2 * ∑ j : Fin n,
    (fderiv ℝ (fun y => fS a i (t, y)) z (EuclideanSpace.single j 1)) ^ 2
  have hF := F.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J from inter_subset_left) subset_rfl)
  have hF' := F'.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J' from inter_subset_right) subset_rfl)
  have hAsm := contMDiffOn_connection_family_difference hF hF' F.connection F'.connection
  have hcoords (a : M) :
      (∀ i, ContinuousOn (fH a i) ((J ∩ J') ×ˢ (c a).target)) ∧
      (∀ i, ContinuousOn (fA a i) ((J ∩ J') ×ˢ (c a).target)) ∧
      (∀ i, ContinuousOn (fS a i) ((J ∩ J') ×ˢ (c a).target)) := by
    have hbaseH : (c a).source ⊆ (eH a).baseSet := by
      simp only [c, eH, V, FH, BH, hom_trivializationAt_baseSet,
        TangentBundle.trivializationAt_baseSet]
      exact fun x hx => ⟨hx, hx, mem_univ x⟩
    have hbaseA : (c a).source ⊆ (eA a).baseSet := by
      simp only [c, eA, V, FA, BA, hom_trivializationAt_baseSet,
        TangentBundle.trivializationAt_baseSet]
      exact fun x hx => ⟨hx, hx, hx⟩
    have hbaseS : (c a).source ⊆ (eS a).baseSet := by
      simp only [c, eS, V, FS, BS, hom_trivializationAt_baseSet,
        TangentBundle.trivializationAt_baseSet]
      exact fun x hx => ⟨hx, hx, hx, hx⟩
    have hHcoord : ContDiffOn ℝ ∞
        (fun p : ℝ × V => qH ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
          (H p.1 ((c a).symm p.2)))).2) ((J ∩ J') ×ˢ (c a).target) := by
      have h1 := contDiffOn_family_bundle_coordinates (E := BH) qH
        (fun t x => (F.metric t).inner x) hF a hbaseH
      have h2 := contDiffOn_family_bundle_coordinates (E := BH) qH
        (fun t x => (F'.metric t).inner x) hF' a hbaseH
      apply (h1.sub h2).congr
      intro p hp
      change qH ((eH a) (TotalSpace.mk' FH _ (_ - _))).2 = _
      rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eH a) _
        (hbaseH ((c a).map_target hp.2)), map_sub, map_sub]
      rfl
    have hAcoord := contDiffOn_family_bundle_coordinates (E := BA) qA A hAsm a hbaseA
    have hScoord : ContDiffOn ℝ ∞
        (fun p : ℝ × V => qS ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
          (S p.1 ((c a).symm p.2)))).2) ((J ∩ J') ×ˢ (c a).target) := by
      have h1 := contDiffOn_family_bundle_coordinates (E := BS) (J := J ∩ J') qS R
        (hRsm.mono (Set.prod_mono inter_subset_left subset_rfl)) a hbaseS
      have h2 := contDiffOn_family_bundle_coordinates (E := BS) (J := J ∩ J') qS R'
        (hR'sm.mono (Set.prod_mono inter_subset_right subset_rfl)) a hbaseS
      apply (h1.sub h2).congr
      intro p hp
      change qS ((eS a) (TotalSpace.mk' FS _ (_ - _))).2 = _
      rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eS a) _
        (hbaseS ((c a).map_target hp.2)), map_sub, map_sub]
      rfl
    exact ⟨fun i => (EuclideanSpace.proj i).continuous.comp_continuousOn hHcoord.continuousOn,
      fun i => (EuclideanSpace.proj i).continuous.comp_continuousOn hAcoord.continuousOn,
      fun i => (EuclideanSpace.proj i).continuous.comp_continuousOn hScoord.continuousOn⟩
  intro b hb
  have hb0 : 0 ≤ b := hJ0.2 hb.1
  rcases eq_or_lt_of_le hb0 with rfl | hbpos
  · exact hinit
  let K := Icc (0 : ℝ) b
  have hKsub : K ⊆ J ∩ J' := fun t ht =>
    ⟨F.interval.out hJ0.1 hb.1 ht, F'.interval.out hJ'0.1 hb.2 ht⟩
  obtain ⟨hHc, hAc, hSc, hEc, hnonneg, hzero, hderiv, hbound, hinitzero⟩ :=
    hcert K isCompact_Icc hKsub
  obtain ⟨CM, hCM, hmetric⟩ := exists_metric_difference_energy_rate_bound (M := M) qH qS
  obtain ⟨CA, hCA, hconnection⟩ := exists_connection_difference_integral_rate_bound
    qH qA qS s φ hφ J J' F F' hinit R R' hR hR' K isCompact_Icc hKsub
  obtain ⟨lambda, CS, hlambda, hCS, hcurvature⟩ :=
    exists_curvature_difference_integral_rate_bound
      qH qA qS s φ hφ J J' F F' R R' hR hR' K isCompact_Icc hKsub
  let B := (s.card : ℝ) * C0
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hC0
  have hRho (t : ℝ) (ht : t ∈ K) : Rho t ≤ B * E t := by
    have hp (a : M) (ha : a ∈ s) :
        (∫ z in tsupport (φ a), density a (t, z)) ≤ C0 * E t := by
      have hint {d : ℕ} (f : Fin d → ℝ × V → ℝ)
          (hf : ∀ i, ContinuousOn (f i) ((J ∩ J') ×ˢ (c a).target)) :
          IntegrableOn (fun z => ∑ i, f i (t, z) ^ 2) (tsupport (φ a)) :=
        ContinuousOn.integrableOn_compact (hφ a ha).2.1
          ((continuousOn_finsetSum _ (fun i _ =>
            ((hf i).comp (continuousOn_const.prodMk continuousOn_id)
              (fun z hz => ⟨hKsub ht, hz⟩)).pow 2)).mono (hφ a ha).2.2)
      have hHi := hint (fH a) (hcoords a).1
      have hAi := hint (fA a) (hcoords a).2.1
      have hSi := hint (fS a) (hcoords a).2.2
      dsimp only [density]
      have hsum := integral_add (hHi.add hAi) hSi
      have hparts := integral_add hHi hAi
      simp only [Pi.add_apply] at hsum hparts
      rw [hsum, hparts]
      exact hbound t ht a ha
    have hsum := Finset.sum_le_sum (s := s) (fun a ha => hp a ha)
    simpa only [Rho, Finset.sum_const, nsmul_eq_mul, B, mul_assoc] using hsum
  let C := (1 + CM) + ((CA / (lambda / 8) + CA) + CS) * B
  have hrates (t : ℝ) (ht : t ∈ interior K) : deriv E t ≤ C * E t := by
    have htK : t ∈ K := interior_subset ht
    have htJ : t ∈ interior (J ∩ J') := interior_mono hKsub ht
    obtain ⟨hH0, hA0, hS0, hE0⟩ := hnonneg t htK
    have hm := hmetric s φ
      (fun a ha => ⟨(hφ a ha).1.continuous, (hφ a ha).2⟩)
      J J' F F' R R' hR hR' t htJ
    have ha := hconnection (lambda / 8) (by positivity) t ht
    have hs := hcurvature t ht
    change rate fH t ≤ energy fH t + CM * energy fS t at hm
    change rate fA t ≤ lambda / 8 * G t + (CA / (lambda / 8) + CA) * Rho t at ha
    change rate fS t ≤ CS * Rho t - lambda / 4 * G t at hs
    have hmE : rate fH t ≤ (1 + CM) * E t := by
      have hcmH := mul_nonneg hCM hH0
      have hcmA := mul_nonneg hCM hA0
      dsimp only [E]
      nlinarith only [hm, hA0, hS0, hcmH, hcmA]
    have hco : 0 ≤ (CA / (lambda / 8) + CA) + CS := by positivity
    have hRhoE := mul_le_mul_of_nonneg_left (hRho t htK) hco
    have hG : 0 ≤ G t := Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun i _ => integral_nonneg (fun z =>
        mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => sq_nonneg _)))))
    have hgrad := mul_nonneg hlambda.le hG
    rw [(hderiv t ht).2.2.2.deriv]
    change rate fH t + rate fA t + rate fS t ≤ C * E t
    dsimp only [C]
    nlinarith only [hmE, ha, hs, hRhoE, hgrad]
  have hE0 : E 0 = 0 := (hinitzero ⟨le_rfl, hbpos.le⟩ hinit).2.2.2
  have hzeroE := eq_zero_on_interval_of_deriv_le_mul
    (a := (0 : ℝ)) (b := b) hEc
    (fun t ht => (hderiv t (by simpa [K] using ht)).2.2.2.differentiableAt)
    hE0 (fun t ht => (hnonneg t ht).2.2.2)
    (fun t ht => hrates t (by simpa [K] using ht))
  exact (hzero b ⟨hbpos.le, le_rfl⟩).mp (hzeroE ⟨hbpos.le, le_rfl⟩)

end PoincareConjecture.Proofs.M03
