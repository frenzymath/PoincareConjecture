import PoincareConjecture.Proofs.M03.MetricDifferenceEvolution
import PoincareConjecture.Proofs.M03.CurvatureHom
import PoincareConjecture.Proofs.M03.FiniteBundleFamilyEnergy
import PoincareConjecture.Proofs.M03.ConnectionDifferenceEvolution

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle MeasureTheory Set

universe u

namespace PoincareConjecture.Proofs.M03

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

section TerminalMetric

open Manifold Filter

theorem exists_ricciFlow_endpoint_metric_of_curvature_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T C : ℝ} (hT : 0 < T) (F : RicciFlow n M (Ico 0 T))
    (hRm : ∀ s ∈ Ico 0 T, ∀ x : M,
      (F.connection s).curvatureTensorNorm x ≤ C) :
    let A : ℝ := 2 * (n : ℝ) * max C 0
    ∃ gT : RiemannianMetric n M,
      (∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
        Real.exp (-(A * T)) * (F.metric 0).inner x v v ≤ gT.inner x v v ∧
        gT.inner x v v ≤ Real.exp (A * T) * (F.metric 0).inner x v v) ∧
      (∀ x : M, ∀ u v : TangentSpace (𝓡 n) x,
        Tendsto (fun s => (F.metric s).inner x u v) (𝓝[<] T)
          (𝓝 (gT.inner x u v)) ∧
        ∀ s ∈ Ico 0 T,
          |(F.metric s).inner x u v - gT.inner x u v| ≤
            A * Real.exp (A * T) * (T - s) *
              (F.metric 0).tangentNorm x u *
              (F.metric 0).tangentNorm x v) ∧
      (∀ a : ℝ, 0 < a → a < T → ∀ x0 : M,
        let V := EuclideanSpace ℝ (Fin n)
        let c := chartAt V x0
        let e := trivializationAt V (TangentSpace (𝓡 n)) x0
        let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        let G := fun (s : ℝ) (i j : Fin n) (z : V) =>
          (F.metric s).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
        let GT := fun (i j : Fin n) (z : V) =>
          gT.inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
        ∀ q : ℕ, ∀ K : Set V, IsCompact K → K ⊆ c.target →
          (∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Ico a T, ∀ z ∈ K,
            ∀ i j : Fin n,
              ‖iteratedFDeriv ℝ q (G s i j) z -
                  iteratedFDeriv ℝ q (GT i j) z‖ ≤ L * (T - s)) ∧
          (∀ i j : Fin n,
            TendstoUniformlyOn (fun s z => iteratedFDeriv ℝ q (G s i j) z)
              (iteratedFDeriv ℝ q (GT i j)) (𝓝[<] T) K)) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let A : ℝ := 2 * (n : ℝ) * max C 0
  let d := Real.exp (-(A * T))
  have hd : 0 < d := Real.exp_pos _
  have hcontrol := metric_endpoint_control_of_curvature_bound hT F hRm
  let ι := fun x : M => Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := fun x : M => (F.metric 0).orthonormalBasis x
  let p := fun (x : M) (i : ι x) => (F.metric 0).inner x (b x i)
  have hlim (x : M) (i j : ι x) := (hcontrol.2 x (b x i) (b x j)).2
  choose lam hlam using hlim
  let B := fun x : M => ∑ i : ι x, ∑ j : ι x,
    lam x i j • (p x i).smulRight (p x j)
  have hrepr (x : M) (v : TangentSpace (𝓡 n) x) :
      ∑ i : ι x, p x i v • b x i = v := by
    exact (b x).sum_repr' v
  have hBvalue (x : M) (v w : TangentSpace (𝓡 n) x) :
      B x v w = ∑ i : ι x, ∑ j : ι x, lam x i j * (p x i v * p x j w) := by
    simp only [B, sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have hexpand (s : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
      (F.metric s).inner x v w = ∑ i : ι x, ∑ j : ι x,
        (F.metric s).inner x (b x i) (b x j) * (p x i v * p x j w) := by
    calc
      _ = (F.metric s).inner x (∑ i : ι x, p x i v • b x i)
          (∑ j : ι x, p x j w • b x j) := by rw [hrepr, hrepr]
      _ = _ := by
        simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hBlim (x : M) (v w : TangentSpace (𝓡 n) x) :
      Tendsto (fun s => (F.metric s).inner x v w) (𝓝[<] T) (𝓝 (B x v w)) := by
    have heq : (fun s => (F.metric s).inner x v w) =
        (fun s => ∑ i : ι x, ∑ j : ι x,
          (F.metric s).inner x (b x i) (b x j) * (p x i v * p x j w)) :=
      funext (fun s => hexpand s x v w)
    rw [heq, hBvalue]
    exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _
      (fun j _ => (hlam x i j).1.mul tendsto_const_nhds))
  have hsymm (x : M) (v w : TangentSpace (𝓡 n) x) : B x v w = B x w v := by
    have he : (fun s => (F.metric s).inner x v w) =
        (fun s => (F.metric s).inner x w v) := funext (fun s => (F.metric s).symm x v w)
    have hh := hBlim x v w
    rw [he] at hh
    exact tendsto_nhds_unique hh (hBlim x w v)
  have hdom : ∀ᶠ s in 𝓝[<] T, s ∈ Ico 0 T := Ico_mem_nhdsLT hT
  have hdiag (x : M) (v : TangentSpace (𝓡 n) x) :
      d * (F.metric 0).inner x v v ≤ B x v v ∧
      B x v v ≤ Real.exp (A * T) * (F.metric 0).inner x v v := by
    constructor
    · exact le_of_tendsto_of_tendsto tendsto_const_nhds (hBlim x v v)
        (hdom.mono (fun s hs => (hcontrol.1 s hs x v).1))
    · exact le_of_tendsto_of_tendsto (hBlim x v v) tendsto_const_nhds
        (hdom.mono (fun s hs => (hcontrol.1 s hs x v).2))
  have hpos (x : M) (v : TangentSpace (𝓡 n) x) (hv : v ≠ 0) : 0 < B x v v :=
    (mul_pos hd ((F.metric 0).pos x v hv)).trans_le (hdiag x v).1
  have hunit (x : M) : Bornology.IsVonNBounded ℝ {v | B x v v < 1} := by
    apply (NormedSpace.isVonNBounded_ball ℝ (TangentSpace (𝓡 n) x)
      (Real.sqrt d⁻¹)).subset
    intro v hv
    rw [Metric.mem_ball, dist_zero_right]
    have hnorm : (F.metric 0).inner x v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    have hsq : ‖v‖ ^ 2 < d⁻¹ := by
      rw [inv_eq_one_div, lt_div_iff₀ hd]
      have hh := (hdiag x v).1.trans_lt hv
      rw [hnorm] at hh
      nlinarith only [hh]
    nlinarith only [hsq, norm_nonneg v, Real.sqrt_nonneg d⁻¹,
      Real.sq_sqrt (inv_nonneg.mpr hd.le)]
  have hcoeff (a : ℝ) (ha : 0 < a) (haT : a < T) (x0 : M) :
      let c := chartAt V x0
      let e := trivializationAt V (TangentSpace (𝓡 n)) x0
      let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      let G := fun (s : ℝ) (i j : Fin n) (z : V) =>
        (F.metric s).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
      let GT := fun (i j : Fin n) (z : V) =>
        B (c.symm z) (E i (c.symm z)) (E j (c.symm z))
      ∀ i j : Fin n, ContDiffOn ℝ ∞ (GT i j) c.target ∧
        ∀ q : ℕ, ∀ K : Set V, IsCompact K → K ⊆ c.target →
          (∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Ico a T, ∀ z ∈ K,
            ‖iteratedFDeriv ℝ q (G s i j) z -
              iteratedFDeriv ℝ q (GT i j) z‖ ≤ L * (T - s)) ∧
          TendstoUniformlyOn (fun s z => iteratedFDeriv ℝ q (G s i j) z)
            (iteratedFDeriv ℝ q (GT i j)) (𝓝[<] T) K := by
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let G := fun (s : ℝ) (i j : Fin n) (z : V) =>
      (F.metric s).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
    let GT := fun (i j : Fin n) (z : V) =>
      B (c.symm z) (E i (c.symm z)) (E j (c.symm z))
    dsimp only
    intro i j
    have hbase {z : V} (hz : z ∈ c.target) : c.symm z ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
    have hE (k : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (T% (E k)) e.baseSet := e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb k
    have hfamily (s : ℝ) : RiemannianMetric.IsSmoothFamilyOn
        (fun _ : ℝ => F.metric s) Set.univ :=
      ((F.metric s).contMDiff.comp contMDiff_snd).contMDiffOn
    have hf (s : ℝ) : ContDiffOn ℝ ∞ (G s i j) c.target := by
      have hp := (contMDiffOn_family_metric_pair (hfamily s)
        (E i) (E j) (hE i) (hE j)).comp
          (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
            (fun y : M => ((0 : ℝ), y)) e.baseSet from
            contMDiffOn_const.prodMk contMDiffOn_id)
          (fun y hy => ⟨Set.mem_univ (0 : ℝ), hy⟩)
      exact (hp.comp (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0))
        (fun z hz => hbase hz)).contDiffOn
    have hjets (q : ℕ) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ c.target) :
        ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Ico a T, ∀ t ∈ Ico a T, ∀ z ∈ K,
          ‖iteratedFDeriv ℝ q (G t i j) z - iteratedFDeriv ℝ q (G s i j) z‖ ≤
            L * |t - s| := by
      obtain ⟨B0, R, hB0, hR, hb, hr, hlip⟩ :=
        ricciFlow_metric_coordinate_jets_terminal_control hT F hRm ha haT x0 hK hKU q
      exact ⟨R, hR, fun s hs t ht z hz => hlip q le_rfl s hs t ht z hz i j⟩
    obtain ⟨fT, hsm, hrest⟩ := exists_contDiffOn_limit_of_iteratedFDeriv_time_lipschitz
      c.open_target haT (fun s => G s i j) (fun s _ => hf s) hjets
    have heq (z : V) (hz : z ∈ c.target) : fT z = GT i j z := by
      have hzero := ((hrest 0 {z} isCompact_singleton
        (singleton_subset_iff.mpr hz)).2).tendsto_at (mem_singleton z)
      have hv := ((continuousMultilinearCurryFin0 ℝ V ℝ).continuous.tendsto
        (iteratedFDeriv ℝ 0 fT z)).comp hzero
      change Tendsto (fun s => (iteratedFDeriv ℝ 0 (G s i j) z) 0) (𝓝[<] T)
        (𝓝 ((iteratedFDeriv ℝ 0 fT z) 0)) at hv
      simp only [iteratedFDeriv_zero_apply] at hv
      exact tendsto_nhds_unique hv (hBlim (c.symm z) (E i (c.symm z)) (E j (c.symm z)))
    refine ⟨hsm.congr (fun z hz => (heq z hz).symm), ?_⟩
    intro q K hK hKU
    have heqjet (z : V) (hz : z ∈ c.target) :
        iteratedFDeriv ℝ q fT z = iteratedFDeriv ℝ q (GT i j) z := by
      have hgerm : fT =ᶠ[𝓝 z] GT i j := by
        filter_upwards [c.open_target.mem_nhds hz] with y hy
        exact heq y hy
      exact (hgerm.iteratedFDeriv (𝕜 := ℝ) q).eq_of_nhds
    obtain ⟨⟨L, hL, hb⟩, hu⟩ := hrest q K hK hKU
    constructor
    · refine ⟨L, hL, ?_⟩
      intro s hs z hz
      simpa only [heqjet z (hKU hz)] using hb s hs z hz
    · exact hu.congr_right (fun z hz => heqjet z (hKU hz))
  have hsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (V →L[ℝ] V →L[ℝ] ℝ) x (B x)) := by
    intro x0
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let BC := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 y x0 y (B y)
    let P : Fin n → Fin n → V →L[ℝ] V →L[ℝ] ℝ :=
      fun i j => (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)
    have hx0 : x0 ∈ e.baseSet := mem_baseSet_trivializationAt V (TangentSpace (𝓡 n)) x0
    have hEvalue {y : M} (hy : y ∈ e.baseSet) (i : Fin n) :
        E i y = e.symmL ℝ y (cb i) := by
      dsimp only [E]
      rw [e.localFrame_apply_of_mem_baseSet cb hy]
      simp only [Trivialization.basisAt, Module.Basis.map_apply,
        Trivialization.linearEquivAt_symm_apply]
      exact (Trivialization.symmL_apply (R := ℝ) e hy (cb i)).symm
    have hEexpand {y : M} (hy : y ∈ e.baseSet) (v : V) :
        e.symmL ℝ y v = ∑ i : Fin n, v i • E i y := by
      have hv : v = ∑ i : Fin n, v i • cb i := by
        simpa only [cb, EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis] using
          ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
      calc
        _ = e.symmL ℝ y (∑ i : Fin n, v i • cb i) := congrArg (e.symmL ℝ y) hv
        _ = _ := by simp only [map_sum, map_smul, hEvalue hy]
    have hBCeq {y : M} (hy : y ∈ e.baseSet) :
        BC y = ∑ i : Fin n, ∑ j : Fin n, B y (E i y) (E j y) • P i j := by
      ext v w
      dsimp only [BC]
      rw [inCoordinates_apply_eq₂ (F₁ := V) (F₂ := V) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M => ℝ) hy hy (by simp)]
      rw [← Trivialization.symmL_apply (R := ℝ) e hy v,
        ← Trivialization.symmL_apply (R := ℝ) e hy w]
      simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
        LinearMap.id_coe, id_eq]
      rw [hEexpand hy, hEexpand hy]
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, ContinuousLinearMap.smulRight_apply,
        smul_eq_mul, Finset.mul_sum, P]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change w j * (v i * B y (E i y) (E j y)) =
        B y (E i y) (E j y) * (v i * w j)
      ring
    have hscalar (i j : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => B y (E i y) (E j y)) e.baseSet := by
      have hh := (hcoeff (T / 2) (by linarith) (by linarith) x0 i j).1
      have hc := hh.contMDiffOn.comp
        (contMDiffOn_chart (I := 𝓡 n) (n := ∞) (x := x0))
        (fun y hy => c.map_source hy)
      have hc' : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
          (fun y => B y (E i y) (E j y)) c.source :=
        hc.congr (fun y hy => by dsimp only [Function.comp_def]; rw [c.left_inv hy])
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hc'
    have hsum : ContMDiffOn (𝓡 n) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) ∞
        (fun y => ∑ i : Fin n, ∑ j : Fin n, B y (E i y) (E j y) • P i j) e.baseSet :=
      contMDiffOn_finsetSum (fun i _ => contMDiffOn_finsetSum (fun j _ =>
        (hscalar i j).smul contMDiffOn_const))
    have hBC : ContMDiffAt (𝓡 n) 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) ∞ BC x0 :=
      (hsum.contMDiffAt (e.open_baseSet.mem_nhds hx0)).congr_of_eventuallyEq
        (by
          filter_upwards [e.open_baseSet.mem_nhds hx0] with y hy
          exact hBCeq hy)
    exact (contMDiffAt_hom_bundle (fun y =>
      (TotalSpace.mk' (V →L[ℝ] V →L[ℝ] ℝ) y (B y) :
        TotalSpace (V →L[ℝ] V →L[ℝ] ℝ)
          (fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)))).mpr
      ⟨contMDiffAt_id, hBC⟩
  let gT : RiemannianMetric n M :=
    { inner := B, symm := hsymm, pos := hpos, isVonNBounded := hunit, contMDiff := hsmooth }
  refine ⟨gT, hdiag, ?_, ?_⟩
  · intro x v w
    obtain ⟨L, hL, hbound⟩ := (hcontrol.2 x v w).2
    have heq : L = B x v w := tendsto_nhds_unique hL (hBlim x v w)
    exact ⟨hBlim x v w, fun s hs => by simpa only [heq] using hbound s hs⟩
  · intro a ha haT x0
    dsimp only
    intro q K hK hKU
    have hpair := fun i j : Fin n => (hcoeff a ha haT x0 i j).2 q K hK hKU
    choose L hL hb using (fun i j : Fin n => (hpair i j).1)
    constructor
    · refine ⟨∑ i : Fin n, ∑ j : Fin n, L i j,
        Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hL i j)), ?_⟩
      intro s hs z hz i j
      apply (hb i j s hs z hz).trans
      apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hs.2.le)
      exact (Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => hL i k)
        (Finset.mem_univ j)).trans
          (Finset.single_le_sum
            (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
              Finset.sum_nonneg (fun l _ => hL k l)) (Finset.mem_univ i))
    · exact fun i j => (hpair i j).2

end TerminalMetric

end PoincareConjecture.Proofs.M03
