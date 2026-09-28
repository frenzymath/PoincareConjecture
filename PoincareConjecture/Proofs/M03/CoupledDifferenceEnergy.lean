import PoincareConjecture.Proofs.M03.MetricDifferenceEnergy
import PoincareConjecture.Proofs.M03.ConnectionDifference
import PoincareConjecture.Proofs.M03.CurvatureHom










set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle MeasureTheory Set

universe u

namespace PoincareConjecture.Proofs.M03

theorem exists_ricci_flow_coupled_difference_energy
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] :
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
    let dH := Module.finrank ℝ FH
    let dA := Module.finrank ℝ FA
    let dS := Module.finrank ℝ FS
    letI : MeasurableSpace V := borel _
    letI : BorelSpace V := ⟨rfl⟩
    ∃ (qH : FH ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
      (qA : FA ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
      (qS : FS ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
      (s : Finset M) (φ : M → V → ℝ) (C : ℝ),
      0 ≤ C ∧
      (∀ a ∈ s, ContDiff ℝ ∞ (φ a) ∧ HasCompactSupport (φ a) ∧
        tsupport (φ a) ⊆ (chartAt V a).target) ∧
      (∀ x : M, ∃ a ∈ s, x ∈ (chartAt V a).source ∧
        φ a (chartAt V a x) = 1) ∧
      ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J'),
        ∃ (R R' : (t : ℝ) → (x : M) → BS x),
          (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) ∧
          (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, FS)) ∞
            (fun p : ℝ × M => TotalSpace.mk' FS p.2 (R p.1 p.2))
            (J ×ˢ Set.univ) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, FS)) ∞
            (fun p : ℝ × M => TotalSpace.mk' FS p.2 (R' p.1 p.2))
            (J' ×ˢ Set.univ) ∧
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
            let componentEnergy := fun {d : ℕ}
                (f : M → Fin d → ℝ × V → ℝ) (t : ℝ) =>
              ∑ a ∈ s, ∑ i, ∫ z, (φ a z * f a i (t, z)) ^ 2
            let componentRate := fun {d : ℕ}
                (f : M → Fin d → ℝ × V → ℝ) (t : ℝ) =>
              ∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * f a i (t, z) *
                fderiv ℝ (f a i) (t, z) (1, 0)
            let EH := componentEnergy fH
            let EA := componentEnergy fA
            let ES := componentEnergy fS
            let E := fun t => EH t + EA t + ES t
            ContinuousOn EH K ∧ ContinuousOn EA K ∧ ContinuousOn ES K ∧
            ContinuousOn E K ∧
            (∀ t ∈ K, 0 ≤ EH t ∧ 0 ≤ EA t ∧ 0 ≤ ES t ∧ 0 ≤ E t) ∧
            (∀ t ∈ K, E t = 0 ↔ F.metric t = F'.metric t) ∧
            (∀ t ∈ interior K,
              HasDerivAt EH (componentRate fH t) t ∧
              HasDerivAt EA (componentRate fA t) t ∧
              HasDerivAt ES (componentRate fS t) t ∧
              HasDerivAt E
                (componentRate fH t + componentRate fA t + componentRate fS t) t) ∧
            (∀ t ∈ K, ∀ a ∈ s,
              (∫ z in tsupport (φ a), ∑ i, (fH a i (t, z)) ^ 2) +
                (∫ z in tsupport (φ a), ∑ i, (fA a i (t, z)) ^ 2) +
                (∫ z in tsupport (φ a), ∑ i, (fS a i (t, z)) ^ 2) ≤ C * E t) ∧
            (0 ∈ K → F.metric 0 = F'.metric 0 →
              EH 0 = 0 ∧ EA 0 = 0 ∧ ES 0 = 0 ∧ E 0 = 0) := by
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
  let : NormedAddCommGroup FS := inferInstance
  let : NormedSpace ℝ FS := inferInstance
  let : ∀ x, AddCommGroup (BA x) := inferInstance
  let : ∀ x, Module ℝ (BA x) := inferInstance
  let : ∀ x, AddCommGroup (BS x) := inferInstance
  let : ∀ x, Module ℝ (BS x) := inferInstance
  let : MeasurableSpace V := borel _
  let : BorelSpace V := ⟨rfl⟩
  classical
  obtain ⟨qH, s, φ, CH, hCH, hφ, hcover, hmetric⟩ :=
    exists_metric_difference_energy (n := n) (M := M)
  obtain ⟨qA, _, _, _⟩ := exists_model_fiber_energy_coordinates (F := FA)
  obtain ⟨qS, _, _, _⟩ := exists_model_fiber_energy_coordinates (F := FS)
  have hbaseA : ∀ a ∈ s, (chartAt V a).source ⊆
      (trivializationAt FA BA a).baseSet := by
    intro a _
    simp only [V, FA, BA, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    intro x hx
    exact ⟨hx, hx, hx⟩
  have hbaseS : ∀ a ∈ s, (chartAt V a).source ⊆
      (trivializationAt FS BS a).baseSet := by
    intro a _
    simp only [V, FS, BS, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    intro x hx
    exact ⟨hx, hx, hx, hx⟩
  obtain ⟨CA, hCA, henergyA⟩ := exists_finite_bundle_family_energy_bound (E := BA) qA s φ
    (fun a ha => (hφ a ha).1.continuous) (fun a ha => (hφ a ha).2.1)
    (fun a ha => (hφ a ha).2.2) hbaseA hcover
  obtain ⟨CS, hCS, henergyS⟩ := exists_finite_bundle_family_energy_bound (E := BS) qS s φ
    (fun a ha => (hφ a ha).1.continuous) (fun a ha => (hφ a ha).2.1)
    (fun a ha => (hφ a ha).2.2) hbaseS hcover
  refine ⟨qH, qA, qS, s, φ, CH + CA + CS,
    add_nonneg (add_nonneg hCH hCA) hCS, hφ, hcover, ?_⟩
  intro J J' F F'
  obtain ⟨R, hR, hRsm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F.smooth F.connection
  obtain ⟨R', hR', hR'sm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F'.smooth F'.connection
  refine ⟨R, R', hR, hR', hRsm, hR'sm, ?_⟩
  intro K hK hKsub
  let c := chartAt V (M := M)
  let eH := trivializationAt FH BH
  let eA := trivializationAt FA BA
  let eS := trivializationAt FS BS
  let H : (t : ℝ) → (x : M) → BH x :=
    fun t x => (F.metric t).inner x - (F'.metric t).inner x
  let A : (t : ℝ) → (x : M) → BA x := fun t x =>
    CovariantDerivative.difference
      (F.connection t).connection (F'.connection t).connection x
  let S : (t : ℝ) → (x : M) → BS x := fun t x => R t x - R' t x
  let fH : M → Fin (Module.finrank ℝ FH) → ℝ × V → ℝ := fun a i p =>
    qH ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
      (H p.1 ((c a).symm p.2)))).2 i
  let fA : M → Fin (Module.finrank ℝ FA) → ℝ × V → ℝ := fun a i p =>
    qA ((eA a) (TotalSpace.mk' FA ((c a).symm p.2)
      (A p.1 ((c a).symm p.2)))).2 i
  let fS : M → Fin (Module.finrank ℝ FS) → ℝ × V → ℝ := fun a i p =>
    qS ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
      (S p.1 ((c a).symm p.2)))).2 i
  let componentEnergy := fun {d : ℕ} (f : M → Fin d → ℝ × V → ℝ) (t : ℝ) =>
    ∑ a ∈ s, ∑ i, ∫ z, (φ a z * f a i (t, z)) ^ 2
  let componentRate := fun {d : ℕ} (f : M → Fin d → ℝ × V → ℝ) (t : ℝ) =>
    ∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * f a i (t, z) *
      fderiv ℝ (f a i) (t, z) (1, 0)
  let EH := componentEnergy fH
  let EA := componentEnergy fA
  let ES := componentEnergy fS
  let E := fun t => EH t + EA t + ES t
  have hF : RiemannianMetric.IsSmoothFamilyOn F.metric K :=
    F.smooth.mono (Set.prod_mono (fun _ ht => (hKsub ht).1) subset_rfl)
  have hF' : RiemannianMetric.IsSmoothFamilyOn F'.metric K :=
    F'.smooth.mono (Set.prod_mono (fun _ ht => (hKsub ht).2) subset_rfl)
  have hAsm := contMDiffOn_connection_family_difference hF hF' F.connection F'.connection
  have hRk := hRsm.mono (Set.prod_mono (fun _ ht => (hKsub ht).1) subset_rfl)
  have hR'k := hR'sm.mono (Set.prod_mono (fun _ ht => (hKsub ht).2) subset_rfl)
  have hSsm : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, FS)) ∞
      (fun p : ℝ × M => TotalSpace.mk' FS p.2 (S p.1 p.2)) (K ×ˢ Set.univ) := by
    intro p hp
    apply Bundle.contMDiffWithinAt_totalSpace.mpr
    refine ⟨contMDiffWithinAt_snd, ?_⟩
    have hc := (Bundle.contMDiffWithinAt_totalSpace.mp (hRk p hp)).2
    have hc' := (Bundle.contMDiffWithinAt_totalSpace.mp (hR'k p hp)).2
    let e := trivializationAt FS BS p.2
    have he : p.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.2
    have hnear : ∀ᶠ z in 𝓝[K ×ˢ (Set.univ : Set M)] p, z.2 ∈ e.baseSet :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he))
    apply (hc.sub hc').congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [hnear] with z hz
    exact (e.linearEquivAt ℝ z.2 hz).map_sub (R z.1 z.2) (R' z.1 z.2)
  obtain ⟨hHc, hHn, hHz, hHd, hHb⟩ := hmetric J J' F F' K hK hKsub
  obtain ⟨hAc, hAn, hAz, hAd, hAb⟩ := henergyA K hK A hAsm
  obtain ⟨hSc, hSn, hSz, hSd, hSb⟩ := henergyS K hK S hSsm
  have hAzero (t : ℝ) (heq : F.metric t = F'.metric t) (x : M) : A t x = 0 := by
    have hsame {g g' : RiemannianMetric n M} (D : LeviCivitaData g)
        (D' : LeviCivitaData g') (hgg' : g = g') :
        CovariantDerivative.difference D.connection D'.connection x = 0 := by
      subst g'
      exact connection_difference_eq_zero D D' x
    exact hsame (F.connection t) (F'.connection t) heq

  have hcurv {g g' : RiemannianMetric n M} (D : LeviCivitaData g)
      (D' : LeviCivitaData g')
      (hzero : ∀ x, CovariantDerivative.difference D.connection D'.connection x = 0)
      (x : M) (u v w : TangentSpace (𝓡 n) x) :
      D.curvature x u v w = D'.curvature x u v w := by
    have hconn (Y : (y : M) → TangentSpace (𝓡 n) y) (y : M)
        (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% Y) y) :
        D.connection Y y = D'.connection Y y := by
      have hd := IsCovariantDerivativeOn.difference_apply
        D.connection.isCovariantDerivativeOnUniv D'.connection.isCovariantDerivativeOnUniv
        (Set.mem_univ y) hY
      change CovariantDerivative.difference D.connection D'.connection y (Y y) =
        D.connection Y y - D'.connection Y y at hd
      rw [hzero y, zero_apply] at hd
      exact sub_eq_zero.mp hd.symm
    let X := FiberBundle.extend V u
    let Y := FiberBundle.extend V v
    let Z := FiberBundle.extend V w
    obtain ⟨U₁, hU₁, hX₁⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) V u
    obtain ⟨U₂, hU₂, hY₂⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) V v
    obtain ⟨U₃, hU₃, hZ₃⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) V w
    obtain ⟨U, hU, hUopen, hxU⟩ :=
      mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hU₁ hU₂) hU₃)
    have hX := hX₁.mono (fun _ hy => (hU hy).1.1)
    have hY := hY₂.mono (fun _ hy => (hU hy).1.2)
    have hZ := hZ₃.mono (fun _ hy => (hU hy).2)
    have hmd (W : (y : M) → TangentSpace (𝓡 n) y)
        (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) U)
        {y : M} (hy : y ∈ U) :
        MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% W) y :=
      (hW.contMDiffAt (hUopen.mem_nhds hy)).mdifferentiableAt (by simp)
    have houter (W : (y : M) → TangentSpace (𝓡 n) y)
        (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) U) :
        D.connection (fun y => D.connection Z y (W y)) x =
          D'.connection (fun y => D'.connection Z y (W y)) x := by
      have hQ := D.contMDiffOn_connection_apply hUopen W Z hW hZ
      have hQ' := D'.contMDiffOn_connection_apply hUopen W Z hW hZ
      have hnear : ∀ᶠ y in 𝓝 x,
          D.connection Z y (W y) = D'.connection Z y (W y) := by
        filter_upwards [hUopen.mem_nhds hxU] with y hy
        exact congrArg (fun L => L (W y)) (hconn Z y (hmd Z hZ hy))
      exact (hconn _ x (hmd _ hQ hxU)).trans
        (D'.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
          (hmd _ hQ hxU) (hmd _ hQ' hxU) (by simp) hnear)
    change D.curvatureOnFields X Y Z x = D'.curvatureOnFields X Y Z x
    delta LeviCivitaData.curvatureOnFields
    rw [houter Y hY, houter X hX, hconn Z x (hmd Z hZ hxU)]
  have hSzero (t : ℝ) (heq : F.metric t = F'.metric t) (x : M) : S t x = 0 := by
    apply sub_eq_zero.mpr
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rw [hR, hR']
    exact hcurv (F.connection t) (F'.connection t) (hAzero t heq) x u v w
  have hzero (t : ℝ) (ht : t ∈ K) (heq : F.metric t = F'.metric t) :
      EH t = 0 ∧ EA t = 0 ∧ ES t = 0 :=
    ⟨(hHz t ht).mpr heq, (hAz t ht).mpr (hAzero t heq),
      (hSz t ht).mpr (hSzero t heq)⟩
  change ContinuousOn EH K ∧ _
  refine ⟨hHc, hAc, hSc, (hHc.add hAc).add hSc, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨hHn t ht, hAn t ht, hSn t ht,
      add_nonneg (add_nonneg (hHn t ht) (hAn t ht)) (hSn t ht)⟩
  · intro t ht
    constructor
    · intro he
      apply (hHz t ht).mp
      change E t = 0 at he
      have hh : 0 ≤ EH t := hHn t ht
      have ha : 0 ≤ EA t := hAn t ht
      have hs : 0 ≤ ES t := hSn t ht
      dsimp only [E] at he
      linarith
    · intro heq
      obtain ⟨hh, ha, hs⟩ := hzero t ht heq
      change E t = 0
      dsimp only [E]
      rw [hh, ha, hs, add_zero, add_zero]
  · intro t ht
    exact ⟨hHd t ht, hAd t ht, hSd t ht, ((hHd t ht).add (hAd t ht)).add (hSd t ht)⟩
  · intro t ht a ha
    have hh := hHb t ht a ha
    have hA := hAb t ht a ha
    have hS := hSb t ht a ha
    have hnH : 0 ≤ EH t := hHn t ht
    have hnA : 0 ≤ EA t := hAn t ht
    have hnS : 0 ≤ ES t := hSn t ht
    have hsum : CH * EH t + CA * EA t + CS * ES t ≤ (CH + CA + CS) * E t := by
      dsimp only [E]
      nlinarith [mul_nonneg hCH hnA, mul_nonneg hCH hnS,
        mul_nonneg hCA hnH, mul_nonneg hCA hnS,
        mul_nonneg hCS hnH, mul_nonneg hCS hnA]
    exact (add_le_add (add_le_add hh hA) hS).trans hsum
  · intro h0 heq
    obtain ⟨hh, ha, hs⟩ := hzero 0 h0 heq
    refine ⟨hh, ha, hs, ?_⟩
    change E 0 = 0
    dsimp only [E]
    rw [hh, ha, hs, add_zero, add_zero]

end PoincareConjecture.Proofs.M03
