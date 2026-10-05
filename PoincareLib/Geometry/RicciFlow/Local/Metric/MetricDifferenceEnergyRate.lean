/- Adapted from Mapher `PoincareMT/Proofs/M03/MetricDifferenceEnergyRate.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Local.Metric.MetricDifferenceEvolution
import PoincareLib.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureHom
import PoincareLib.Geometry.RicciFlow.Local.Energy.Coordinates.FiniteBundleFamilyEnergy
import PoincareLib.Geometry.RicciFlow.Local.Connection.DifferenceEvolution

/-!
# Rate of the actual metric difference energy

The Ricci contraction is fixed in the native tangent coordinates. Its
operator norm bounds the metric rate by metric and curvature energies.
Derivation: proof-work/tasks/M03/reviews/actual-metric-energy-rate-research.json.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle MeasureTheory Set

universe u

namespace PoincareMT.RicciFlow.Local

theorem exists_metric_difference_energy_rate_bound
    {n dH dS : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] :
    let V := EuclideanSpace ℝ (Fin n)
    letI : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    letI : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    letI : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    let FH := V →L[ℝ] V →L[ℝ] ℝ
    let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
    let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ
    let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x
    letI : MeasurableSpace V := borel _
    letI : BorelSpace V := ⟨rfl⟩
    ∀ (qH : FH ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
      (qS : FS ≃L[ℝ] EuclideanSpace ℝ (Fin dS)),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (s : Finset M) (φ : M → V → ℝ),
          (∀ a ∈ s, Continuous (φ a) ∧ HasCompactSupport (φ a) ∧
            tsupport (φ a) ⊆ (chartAt V a).target) →
          ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J')
            (R R' : (t : ℝ) → (x : M) → BS x),
            (∀ t x u v w, R t x u v w =
              (F.connection t).curvature x u v w) →
            (∀ t x u v w, R' t x u v w =
              (F'.connection t).curvature x u v w) →
            let c := chartAt V
            let eH := trivializationAt FH BH
            let eS := trivializationAt FS BS
            let H : (t : ℝ) → (x : M) → BH x :=
              fun t x => (F.metric t).inner x - (F'.metric t).inner x
            let S : (t : ℝ) → (x : M) → BS x :=
              fun t x => R t x - R' t x
            let fH : M → Fin dH → ℝ × V → ℝ := fun a i p =>
              qH ((eH a) (TotalSpace.mk' FH
                ((c a).symm p.2) (H p.1 ((c a).symm p.2)))).2 i
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
            ∀ t ∈ interior (J ∩ J'),
              componentRate fH t ≤
                componentEnergy fH t + C * componentEnergy fS t := by
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
  let FH := V →L[ℝ] V →L[ℝ] ℝ
  let FS := V →L[ℝ] V →L[ℝ] V →L[ℝ] V
  let BH := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] ℝ
  let BS := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x
  let : NormedAddCommGroup FH := inferInstance
  let : NormedSpace ℝ FH := inferInstance
  let : NormedAddCommGroup FS := inferInstance
  let : NormedSpace ℝ FS := inferInstance
  let : ∀ x, AddCommGroup (BH x) := inferInstance
  let : ∀ x, Module ℝ (BH x) := inferInstance
  let : ∀ x, AddCommGroup (BS x) := inferInstance
  let : ∀ x, Module ℝ (BS x) := inferInstance
  let : MeasurableSpace V := borel _
  let : BorelSpace V := ⟨rfl⟩
  classical
  dsimp only
  intro qH qS
  let τ : FS →L[ℝ] FH := ∑ k : Fin n,
    (ContinuousLinearMap.compL ℝ V (V →L[ℝ] V) (V →L[ℝ] ℝ)
      (ContinuousLinearMap.compL ℝ V V ℝ (EuclideanSpace.proj k))).comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V →L[ℝ] V)
        (EuclideanSpace.single k 1))
  let L : EuclideanSpace ℝ (Fin dS) →L[ℝ] EuclideanSpace ℝ (Fin dH) :=
    qH.toContinuousLinearMap.comp (τ.comp qS.symm.toContinuousLinearMap)
  let C : ℝ := 4 * ‖L‖ ^ 2
  refine ⟨C, mul_nonneg (by norm_num) (sq_nonneg _), ?_⟩
  intro s φ hφ J J' F F' R R' hR hR'
  let c := chartAt V (M := M)
  let eH := trivializationAt FH BH
  let eS := trivializationAt FS BS
  let H : (t : ℝ) → (x : M) → BH x :=
    fun t x => (F.metric t).inner x - (F'.metric t).inner x
  let S : (t : ℝ) → (x : M) → BS x := fun t x => R t x - R' t x
  let fH : M → Fin dH → ℝ × V → ℝ := fun a i p =>
    qH ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
      (H p.1 ((c a).symm p.2)))).2 i
  let fS : M → Fin dS → ℝ × V → ℝ := fun a i p =>
    qS ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
      (S p.1 ((c a).symm p.2)))).2 i
  obtain ⟨R₀, hR₀, hRsm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F.smooth F.connection
  obtain ⟨R₁, hR₁, hR'sm⟩ :=
    exists_contMDiffOn_curvature_family_trilinearMap F'.smooth F'.connection
  have hReq : R₀ = R := by
    funext t x
    ext u v w
    exact (hR₀ t x u v w).trans (hR t x u v w).symm
  have hR'eq : R₁ = R' := by
    funext t x
    ext u v w
    exact (hR₁ t x u v w).trans (hR' t x u v w).symm
  rw [hReq] at hRsm
  rw [hR'eq] at hR'sm
  intro t ht
  have htJ : t ∈ J ∩ J' := interior_subset ht
  have htN : J ∩ J' ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  change (∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * fH a i (t, z) *
    fderiv ℝ (fH a i) (t, z) (1, 0)) ≤
    (∑ a ∈ s, ∑ i, ∫ z, (φ a z * fH a i (t, z)) ^ 2) +
    C * ∑ a ∈ s, ∑ i, ∫ z, (φ a z * fS a i (t, z)) ^ 2
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  let hbar : ℝ × V → FH := fun p =>
    ((eH a) (TotalSpace.mk' FH ((c a).symm p.2) (H p.1 ((c a).symm p.2)))).2
  let sbar : ℝ × V → FS := fun p =>
    ((eS a) (TotalSpace.mk' FS ((c a).symm p.2) (S p.1 ((c a).symm p.2)))).2
  let h : ℝ × V → EuclideanSpace ℝ (Fin dH) := fun p => qH (hbar p)
  let r : ℝ × V → EuclideanSpace ℝ (Fin dS) := fun p => qS (sbar p)
  have hbaseH : (c a).source ⊆ (eH a).baseSet := by
    simp only [c, eH, V, FH, BH, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    intro x hx
    exact ⟨hx, hx, mem_univ x⟩
  have hbaseS : (c a).source ⊆ (eS a).baseSet := by
    simp only [c, eS, V, FS, BS, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    intro x hx
    exact ⟨hx, hx, hx, hx⟩
  have hh : ContDiffOn ℝ ∞ h ((J ∩ J') ×ˢ (c a).target) := by
    have h₁ := (contDiffOn_family_bundle_coordinates (E := BH) qH
      (fun t x => (F.metric t).inner x) F.smooth a hbaseH).mono
      (Set.prod_mono (show J ∩ J' ⊆ J from Set.inter_subset_left) subset_rfl)
    have h₂ := (contDiffOn_family_bundle_coordinates (E := BH) qH
      (fun t x => (F'.metric t).inner x) F'.smooth a hbaseH).mono
      (Set.prod_mono (show J ∩ J' ⊆ J' from Set.inter_subset_right) subset_rfl)
    apply (h₁.sub h₂).congr
    intro p hp
    have hx := hbaseH ((c a).map_target hp.2)
    change qH ((eH a) (TotalSpace.mk' FH _ (_ - _))).2 = _
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eH a) _ hx, map_sub, map_sub]
    rfl
  have hr : ContDiffOn ℝ ∞ r ((J ∩ J') ×ˢ (c a).target) := by
    have h₁ := (contDiffOn_family_bundle_coordinates (E := BS) qS R hRsm a
      hbaseS).mono
      (Set.prod_mono (show J ∩ J' ⊆ J from Set.inter_subset_left) subset_rfl)
    have h₂ := (contDiffOn_family_bundle_coordinates (E := BS) qS R' hR'sm a
      hbaseS).mono
      (Set.prod_mono (show J ∩ J' ⊆ J' from Set.inter_subset_right) subset_rfl)
    apply (h₁.sub h₂).congr
    intro p hp
    have hx := hbaseS ((c a).map_target hp.2)
    change qS ((eS a) (TotalSpace.mk' FS _ (_ - _))).2 = _
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eS a) _ hx, map_sub, map_sub]
    rfl
  -- Identify the time derivative in the fixed model fiber by scalar evaluations.
  have htime (z : V) (hz : z ∈ (c a).target) (i : Fin dH) :
      fderiv ℝ (fH a i) (t, z) (1, 0) = -2 * L (r (t, z)) i := by
    let x := (c a).symm z
    let e := trivializationAt V (TangentSpace (𝓡 n)) a
    have hx : x ∈ e.baseSet := by
      simpa only [e, V, TangentBundle.trivializationAt_baseSet] using (c a).map_target hz
    let A := e.linearEquivAt ℝ x hx
    let b := (PiLp.basisFun 2 ℝ (Fin n)).map A.symm
    have hbrepr (v : TangentSpace (𝓡 n) x) (k : Fin n) :
        b.repr v k = (A v) k := by
      simp [b, Module.Basis.map_repr, PiLp.basisFun_repr]
    have hbeq (k : Fin n) : b k = A.symm (EuclideanSpace.single k 1) := by
      simp [b, PiLp.basisFun_apply]
    have hτ (T : FS) (u v : V) :
        τ T u v = ∑ k : Fin n, (T (EuclideanSpace.single k 1) u v) k := by
      simp [τ]
      apply Finset.sum_congr rfl
      intro k _
      rfl
    have hheval (t' : ℝ) (u v : V) : hbar (t', z) u v =
        (F.metric t').inner x (A.symm u) (A.symm v) -
          (F'.metric t').inner x (A.symm u) (A.symm v) := by
      dsimp only [hbar, eH]
      rw [hom_trivializationAt_apply]
      rw [inCoordinates_apply_eq₂ (F₁ := V) (F₂ := V) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M => ℝ) hx hx (mem_univ x)]
      simp only [Bundle.Trivial.fiberBundle_trivializationAt',
        Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]
      change H t' x (e.symm x u) (e.symm x v) = _
      rfl
    have hseval (u v w : V) : sbar (t, z) u v w =
        A ((R t x - R' t x) (A.symm u) (A.symm v) (A.symm w)) := by
      have hxhom : x ∈ (trivializationAt (V →L[ℝ] V)
          (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y) a).baseSet := by
        rw [hom_trivializationAt_baseSet]
        exact ⟨hx, hx⟩
      dsimp only [sbar, eS]
      rw [hom_trivializationAt_apply]
      rw [inCoordinates_apply_eq₂ (F₁ := V) (F₂ := V) (F₃ := V →L[ℝ] V)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        hx hx hxhom]
      rw [Trivialization.linearMapAt_apply, if_pos hxhom, hom_trivializationAt_apply]
      change ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n)) V
        (TangentSpace (𝓡 n)) a x a x
        (S t x (e.symm x u) (e.symm x v)) w = _
      simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
        Trivialization.continuousLinearMapAt_apply]
      change e.linearMapAt ℝ x (S t x (e.symm x u) (e.symm x v) (e.symmL ℝ x w)) = _
      rw [Trivialization.symmL_apply (R := ℝ) e hx w]
      rw [Trivialization.linearMapAt_apply, if_pos hx]
      rfl
    have hpN : (J ∩ J') ×ˢ (c a).target ∈ 𝓝 (t, z) :=
      prod_mem_nhds htN ((c a).open_target.mem_nhds hz)
    have hhd : DifferentiableAt ℝ h (t, z) :=
      ((hh (t, z) ⟨htJ, hz⟩).contDiffAt hpN).differentiableAt (by simp)
    have hcurve : HasDerivAt (fun t' : ℝ => (t', z)) (1, 0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
    have hnative : DifferentiableAt ℝ (fun t' => hbar (t', z)) t := by
      have hd := qH.symm.differentiableAt.comp t (hhd.comp t hcurve.differentiableAt)
      simpa only [Function.comp_def, h, ContinuousLinearEquiv.symm_apply_apply] using hd
    have hn := hnative.hasDerivAt
    have hnative_eq : deriv (fun t' => hbar (t', z)) t = (-2 : ℝ) • τ (sbar (t, z)) := by
      ext u v
      have heval := (hn.clm_apply (hasDerivAt_const t u)).clm_apply
        (hasDerivAt_const t v)
      simp only [map_zero, add_zero] at heval
      have hactual := (hasDerivWithinAt_metric_difference_basis F F' htJ x b
        (A.symm u) (A.symm v)).hasDerivAt htN
      have htrace : (∑ k, b.repr ((F.connection t).curvature x (b k) (A.symm u)
          (A.symm v) - (F'.connection t).curvature x (b k) (A.symm u) (A.symm v)) k) =
          τ (sbar (t, z)) u v := by
        rw [hτ]
        apply Finset.sum_congr rfl
        intro k _
        rw [hbrepr, hbeq, hseval]
        simp only [sub_apply, hR, hR']
      rw [htrace] at hactual
      have heq := heval.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun t' => (hheval t' u v).symm))
      simpa only [smul_apply, smul_eq_mul] using heq.unique hactual
    rw [hnative_eq] at hn
    have hcoord := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt t
      (qH.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hn)
    have hscalar := (EuclideanSpace.proj i).differentiableAt.comp (t, z) hhd
    have hjoint := hscalar.hasFDerivAt.comp_hasDerivAt t hcurve
    have heq := hjoint.unique hcoord
    simpa only [fH, h, hbar, L, r, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      map_smul, EuclideanSpace.coe_proj, PiLp.smul_apply, smul_eq_mul] using heq
  let u : V → EuclideanSpace ℝ (Fin dH) := fun z => φ a z • h (t, z)
  let v : V → EuclideanSpace ℝ (Fin dS) := fun z => φ a z • r (t, z)
  have hhc : ContinuousOn (fun z => h (t, z)) (c a).target :=
    hh.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨htJ, hz⟩)
  have hrc : ContinuousOn (fun z => r (t, z)) (c a).target :=
    hr.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨htJ, hz⟩)
  have hu : Continuous u := ((hφ a ha).1.continuousOn.smul hhc).continuous_of_tsupport_subset
    (c a).open_target ((tsupport_smul_subset_left _ _).trans (hφ a ha).2.2)
  have hv : Continuous v := ((hφ a ha).1.continuousOn.smul hrc).continuous_of_tsupport_subset
    (c a).open_target ((tsupport_smul_subset_left _ _).trans (hφ a ha).2.2)
  have huc : HasCompactSupport u := (hφ a ha).2.1.smul_right
  have hvc : HasCompactSupport v := (hφ a ha).2.1.smul_right
  have hui (i : Fin dH) : Continuous (fun z => u z i) :=
    (EuclideanSpace.proj i).continuous.comp hu
  have hvi (i : Fin dS) : Continuous (fun z => v z i) :=
    (EuclideanSpace.proj i).continuous.comp hv
  have huli (i : Fin dH) : HasCompactSupport (fun z => u z i) :=
    huc.comp_left (show (EuclideanSpace.proj i) 0 = 0 from map_zero _)
  have hvli (i : Fin dS) : HasCompactSupport (fun z => v z i) :=
    hvc.comp_left (show (EuclideanSpace.proj i) 0 = 0 from map_zero _)
  have hEHi (i : Fin dH) : Integrable (fun z => (u z i) ^ 2) := by
    apply ((hui i).pow 2).integrable_of_hasCompactSupport
    exact (huli i).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have hESi (i : Fin dS) : Integrable (fun z => (v z i) ^ 2) := by
    apply ((hvi i).pow 2).integrable_of_hasCompactSupport
    exact (hvli i).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have hDi (i : Fin dH) : Integrable (fun z => -4 * u z i * L (v z) i) := by
    apply ((continuous_const.mul (hui i)).mul
      ((EuclideanSpace.proj i).continuous.comp (L.continuous.comp hv))).integrable_of_hasCompactSupport
    exact ((huli i).mul_left).mul_right
  have hrate (i : Fin dH) (z : V) :
      2 * φ a z ^ 2 * fH a i (t, z) * fderiv ℝ (fH a i) (t, z) (1, 0) =
        -4 * u z i * L (v z) i := by
    by_cases hφz : φ a z = 0
    · simp [hφz, u, v]
    · have hz : z ∈ (c a).target :=
        (hφ a ha).2.2 (subset_tsupport _ (Function.mem_support.mpr hφz))
      rw [htime z hz]
      simp only [u, v, map_smul, PiLp.smul_apply, smul_eq_mul]
      change 2 * φ a z ^ 2 * h (t, z) i * (-2 * L (r (t, z)) i) = _
      ring
  have hpoint (z : V) : (∑ i, -4 * u z i * L (v z) i) ≤
      (∑ i, (u z i) ^ 2) + C * ∑ i, (v z i) ^ 2 := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show -4 * u z i * L (v z) i ≤ (u z i) ^ 2 + 4 * (L (v z) i) ^ 2 by
        nlinarith [sq_nonneg (u z i + 2 * L (v z) i)])
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hop := L.le_opNorm (v z)
    have hsquare : ‖L (v z)‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖v z‖ ^ 2 := by
      nlinarith [mul_self_le_mul_self (norm_nonneg _) hop]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hsquare
    dsimp only [C]
    nlinarith
  have hDH := integrable_finsetSum Finset.univ (fun i _ => hDi i)
  have hEH := integrable_finsetSum Finset.univ (fun i _ => hEHi i)
  have hES := integrable_finsetSum Finset.univ (fun i _ => hESi i)
  have hint := integral_mono hDH (hEH.add (hES.const_mul C)) hpoint
  rw [integral_finsetSum _ (fun i _ => hDi i),
    integral_add' hEH (hES.const_mul C), integral_const_mul,
    integral_finsetSum _ (fun i _ => hEHi i),
    integral_finsetSum _ (fun i _ => hESi i)] at hint
  simp_rw [hrate]
  simpa only [u, v, h, r, hbar, sbar, fH, fS, PiLp.smul_apply, smul_eq_mul] using hint

end PoincareMT.RicciFlow.Local
