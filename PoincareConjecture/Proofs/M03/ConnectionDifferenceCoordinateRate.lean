import PoincareConjecture.Proofs.M03.ConnectionDifferenceEvolution
import PoincareConjecture.Proofs.M03.MetricDifferenceEvolution
import PoincareConjecture.Proofs.M03.CurvatureHom
import PoincareConjecture.Proofs.M03.MetricInverse
import PoincareConjecture.Proofs.M03.FamilyBundleCoordinates

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

private theorem covector_reconstruct {n : Nat}
    (l : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    l = ∑ i : Fin n,
      (l (EuclideanSpace.single i 1)) • EuclideanSpace.proj i := by
  classical
  let b := PiLp.basisFun 2 ℝ (Fin n)
  have hv (v : EuclideanSpace ℝ (Fin n)) :
      v = ∑ i : Fin n, v i • EuclideanSpace.single i 1 := by
    calc
      v = ∑ i : Fin n, (b.repr v) i • b i := (b.sum_repr v).symm
      _ = ∑ i : Fin n, v i • EuclideanSpace.single i 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [b, PiLp.basisFun_repr, PiLp.basisFun_apply]
  apply ContinuousLinearMap.ext
  intro v
  calc
    l v = l (∑ i : Fin n, v i • EuclideanSpace.single i 1) := congrArg l (hv v)
    _ = (∑ i : Fin n,
      (l (EuclideanSpace.single i 1)) • EuclideanSpace.proj i) v := by
      simp only [map_sum, map_smul]
      simp [EuclideanSpace.proj, mul_comm]

private theorem inverse_reconstruct {n : Nat}
    {G : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hG : G.IsInvertible) (v : EuclideanSpace ℝ (Fin n)) :
    G.inverse (∑ i : Fin n,
      (G v (EuclideanSpace.single i 1)) • EuclideanSpace.proj i) = v := by
  have hc := covector_reconstruct (G v)
  rw [← hc]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) => L v) hG.inverse_comp_self

private theorem native_from_pairings {n : Nat}
    {G : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hG : G.IsInvertible) (dv : EuclideanSpace ℝ (Fin n))
    (p : Fin n -> ℝ)
    (hp : ∀ i : Fin n, G dv (EuclideanSpace.single i 1) = p i) :
    dv = G.inverse (∑ i : Fin n, p i • EuclideanSpace.proj i) := by
  calc
    dv = G.inverse (∑ i : Fin n,
        (G dv (EuclideanSpace.single i 1)) • EuclideanSpace.proj i) :=
      (inverse_reconstruct hG dv).symm
    _ = G.inverse (∑ i : Fin n, p i • EuclideanSpace.proj i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hp i]

private theorem tensor_coordinate_reconstruct {n dA : ℕ}
    (qA : (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin dA))
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (α : Fin dA) :
    qA T α = ∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n,
      (qA ((EuclideanSpace.proj j).smulRight
        ((EuclideanSpace.proj i).smulRight (EuclideanSpace.single l 1))) α) *
        (T (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) l := by
  classical
  let B : Fin n → Fin n → Fin n →
      EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun l j i => (EuclideanSpace.proj j).smulRight
      ((EuclideanSpace.proj i).smulRight (EuclideanSpace.single l 1))
  have hvec (u : EuclideanSpace ℝ (Fin n)) :
      u = ∑ j : Fin n, u j • EuclideanSpace.single j 1 := by
    let b := PiLp.basisFun 2 ℝ (Fin n)
    calc
      u = ∑ j : Fin n, (b.repr u) j • b j := (b.sum_repr u).symm
      _ = ∑ j : Fin n, u j • EuclideanSpace.single j 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [b, PiLp.basisFun_repr, PiLp.basisFun_apply]
  have hT : T = ∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n,
      (T (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) l • B l j i := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    ext l
    rw [hvec u, hvec v]
    simp only [map_sum, map_smul, smul_eq_mul]
    simp [B, EuclideanSpace.single, Pi.single_apply, Finset.smul_sum,
      Finset.sum_smul, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [hT, map_sum]
  simp only [map_sum, map_smul]
  simp [B, EuclideanSpace.single, Pi.single_apply, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

private theorem fixed_scalar_derivative
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → ℝ) (a : M) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) a).target)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f
      ((chartAt (EuclideanSpace ℝ (Fin n)) a).symm z))
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q => f ((chartAt (EuclideanSpace ℝ (Fin n)) a).symm q)) z v =
      mvfderiv (𝓡 n) f ((chartAt (EuclideanSpace ℝ (Fin n)) a).symm z)
        ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) a).symmL
          ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) a).symm z) v) := by
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V a
  let e := trivializationAt V (TangentSpace (𝓡 n)) a
  let x := c.symm z
  have hx : x ∈ c.source := c.map_target hz
  have hcx : c x = z := c.right_inv hz
  have hc : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm z :=
    ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := a)).contMDiffAt
      (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  have he : e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm z := by
    have h := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := a) hx
    simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
      mfderivWithin_univ] at h
    change e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (c x) at h
    rw [hcx] at h
    exact h
  rw [← mfderiv_eq_fderiv]
  change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z v = mvfderiv (𝓡 n) f x (e.symmL ℝ x v)
  rw [mvfderiv_comp_apply z hf hc v, ← he]
  rfl

private theorem centered_scalar_derivative
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → ℝ) (x : M)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (v : TangentSpace (𝓡 n) x) :
    fderiv ℝ (fun z => f ((extChartAt (𝓡 n) x).symm z))
        ((extChartAt (𝓡 n) x) x) v = mvfderiv (𝓡 n) f x v := by
  let c := extChartAt (𝓡 n) x
  have hc : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hcs : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
      c.symm (c x) :=
    ((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) x).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))).mdifferentiableAt
        (by simp)
  have hid : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) c.symm (c x) =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) (c x)) := by
    simpa only [(𝓡 n).range_eq_univ, mfderivWithin_univ] using
      (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
  have hdf : fderiv ℝ (fun z => f (c.symm z)) (c x) = mvfderiv (𝓡 n) f x := by
    rw [← mfderiv_eq_fderiv]
    change mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (f ∘ c.symm) (c x) = _
    have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (c.symm (c x)) := by
      simpa only [hc] using hf
    rw [mvfderiv_comp (c x) hf' hcs, hid]
    change mvfderiv (𝓡 n) f (c.symm (c x)) = mvfderiv (𝓡 n) f x
    rw [hc]
  exact congrArg (fun L => L v) hdf

private theorem ricci_pair_smooth
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (F.connection t).ricci y (Y y) (Z y)) x := by
  let c := extChartAt (𝓡 n) x
  have hcx : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hcxt : c x ∈ c.target := mem_extChartAt_target x
  have hc : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ c.symm (c x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).contMDiffAt
      (extChartAt_target_mem_nhds' hcxt)
  have hn : interior J ×ˢ (c.target ∩ c.symm ⁻¹' U) ∈ 𝓝 (t, c x) :=
    prod_mem_nhds (isOpen_interior.mem_nhds ht)
      (Filter.inter_mem (extChartAt_target_mem_nhds' hcxt)
        (hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa only [hcx] using hx))))
  have hh := (contDiffOn_ricciFlow_ricci_chart_pair F hU Y Z hY hZ x).contDiffAt hn
  have hs := hh.comp (c x) (contDiffAt_const.prodMk contDiffAt_id)
  rw [contMDiffAt_iff_source]
  simpa only [(𝓡 n).range_eq_univ, contMDiffWithinAt_univ, Function.comp_def, c] using
    hs.contMDiffAt

theorem exists_connection_difference_coordinate_rate_bound
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
    ∀ (qH : FH ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
      (qA : FA ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
      (qS : FS ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
      (s : Finset M) (Q : M → Set V),
      (∀ a ∈ s, IsCompact (Q a) ∧ Q a ⊆ (chartAt V a).target) →
      ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J'),
        F.metric 0 = F'.metric 0 →
        ∀ (R R' : (t : ℝ) → (x : M) → BS x),
          (∀ t x u v w, R t x u v w =
            (F.connection t).curvature x u v w) →
          (∀ t x u v w, R' t x u v w =
            (F'.connection t).curvature x u v w) →
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
            let gradient : M → ℝ → V → ℝ := fun a t z =>
              ∑ i : Fin dS, ∑ j : Fin n,
                (fderiv ℝ (fun y => fS a i (t, y)) z
                  (EuclideanSpace.single j 1)) ^ 2
            ∃ C : ℝ, 0 ≤ C ∧
              ∀ ε : ℝ, 0 < ε →
                ∀ t ∈ interior K, ∀ a ∈ s, ∀ z ∈ Q a,
                  (∑ i : Fin dA, 2 * fA a i (t, z) *
                    fderiv ℝ (fA a i) (t, z) (1, 0)) ≤
                      ε * gradient a t z + (C / ε + C) * density a (t, z) := by
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
  classical
  dsimp only
  intro qH qA qS s Q hQ J J' F F' hinit R R' hR hR' K hK hKsub
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
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
  let τ : FS →L[ℝ] FH := ∑ k : Fin n,
    (ContinuousLinearMap.compL ℝ V (V →L[ℝ] V) (V →L[ℝ] ℝ)
      (ContinuousLinearMap.compL ℝ V V ℝ (EuclideanSpace.proj k))).comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V →L[ℝ] V)
        (EuclideanSpace.single k 1))
  have hτ (T : FS) (u v : V) :
      τ T u v = ∑ k : Fin n, (T (EuclideanSpace.single k 1) u v) k := by
    simp [τ]
    apply Finset.sum_congr rfl
    intro k hk
    rfl
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
  have hF := F.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J from Set.inter_subset_left) subset_rfl)
  have hF' := F'.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J' from Set.inter_subset_right) subset_rfl)
  have hAsm := contMDiffOn_connection_family_difference hF hF' F.connection F'.connection
  have hbaseA (a : M) : (c a).source ⊆ (eA a).baseSet := by
    simp only [c, eA, V, FA, BA, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    intro x hx
    exact ⟨hx, hx, hx⟩
  have hacoord (a : M) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => qA ((eA a) (TotalSpace.mk' FA ((c a).symm p.2)
        (A p.1 ((c a).symm p.2)))).2) ((J ∩ J') ×ˢ (c a).target) :=
    contDiffOn_family_bundle_coordinates (E := BA) qA A hAsm a (hbaseA a)
  have hbaseH (a : M) : (c a).source ⊆ (eH a).baseSet := by
    simp only [c, eH, V, FH, BH, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    intro x hx
    exact ⟨hx, hx, mem_univ x⟩
  have hbaseS (a : M) : (c a).source ⊆ (eS a).baseSet := by
    simp only [c, eS, V, FS, BS, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    intro x hx
    exact ⟨hx, hx, hx, hx⟩
  have hHcoord (a : M) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => qH ((eH a) (TotalSpace.mk' FH ((c a).symm p.2)
        (H p.1 ((c a).symm p.2)))).2) ((J ∩ J') ×ˢ (c a).target) := by
    have h₁ := (contDiffOn_family_bundle_coordinates (E := BH) qH
      (fun t x => (F.metric t).inner x) F.smooth a (hbaseH a)).mono
      (t := (J ∩ J') ×ˢ (c a).target)
      (Set.prod_mono (show J ∩ J' ⊆ J from Set.inter_subset_left) subset_rfl)
    have h₂ := (contDiffOn_family_bundle_coordinates (E := BH) qH
      (fun t x => (F'.metric t).inner x) F'.smooth a (hbaseH a)).mono
      (t := (J ∩ J') ×ˢ (c a).target)
      (Set.prod_mono (show J ∩ J' ⊆ J' from Set.inter_subset_right) subset_rfl)
    apply (h₁.sub h₂).congr
    intro p hp
    have hx := (hbaseH a) ((c a).map_target hp.2)
    change qH ((eH a) (TotalSpace.mk' FH _ (_ - _))).2 = _
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eH a) _ hx,
      map_sub, map_sub]
    rfl

  have hScoord (a : M) : ContDiffOn ℝ ∞
      (fun p : ℝ × V => qS ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
        (S p.1 ((c a).symm p.2)))).2) ((J ∩ J') ×ˢ (c a).target) := by
    have h₁ := (contDiffOn_family_bundle_coordinates (E := BS) qS R hRsm a
      (hbaseS a)).mono (t := (J ∩ J') ×ˢ (c a).target)
      (Set.prod_mono (show J ∩ J' ⊆ J from Set.inter_subset_left) subset_rfl)
    have h₂ := (contDiffOn_family_bundle_coordinates (E := BS) qS R' hR'sm a
      (hbaseS a)).mono (t := (J ∩ J') ×ˢ (c a).target)
      (Set.prod_mono (show J ∩ J' ⊆ J' from Set.inter_subset_right) subset_rfl)
    apply (h₁.sub h₂).congr
    intro p hp
    have hx := (hbaseS a) ((c a).map_target hp.2)
    change qS ((eS a) (TotalSpace.mk' FS _ (_ - _))).2 = _
    rw [← Trivialization.linearEquivAt_apply (R := ℝ) (eS a) _ hx,
      map_sub, map_sub]
    rfl
  let eT := trivializationAt V (TangentSpace (𝓡 n) : M → Type _)
  let frame := fun (a : M) (i : Fin n) (y : M) =>
    (eT a).symmL ℝ y (EuclideanSpace.single i 1)
  let gmod := fun (g : ℝ → RiemannianMetric n M) (a : M) (p : ℝ × V) =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      a ((c a).symm p.2) a ((c a).symm p.2) ((g p.1).inner ((c a).symm p.2))
  let gamma := fun (a : M) (p : ℝ × V) (i j : Fin n) =>
    (eT a).continuousLinearMapAt ℝ ((c a).symm p.2)
      ((F.connection p.1).connection (frame a j) ((c a).symm p.2)
        (frame a i ((c a).symm p.2)))
  let gamma' := fun (a : M) (p : ℝ × V) (i j : Fin n) =>
    (eT a).continuousLinearMapAt ℝ ((c a).symm p.2)
      ((F'.connection p.1).connection (frame a j) ((c a).symm p.2)
        (frame a i ((c a).symm p.2)))
  let rmod' := fun (a : M) (p : ℝ × V) =>
    τ (((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
      (R' p.1 ((c a).symm p.2)))).2)
  have hframe (a : M) (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (frame a i)) (eT a).baseSet := by
    rw [(eT a).contMDiffOn_section_baseSet_iff (IB := 𝓡 n) (n := ∞)]
    refine (contMDiffOn_const (c := EuclideanSpace.single i 1)).congr ?_
    intro y hy
    simpa [frame, Trivialization.symmL_apply _ hy] using
      congrArg Prod.snd ((eT a).apply_mk_symm hy (EuclideanSpace.single i 1))
  have hchartK (a : M) (ha : a ∈ s) : ContinuousOn
      (fun p : ℝ × V => (p.1, (c a).symm p.2)) (K ×ˢ Q a) := by
    apply continuousOn_fst.prodMk
    exact (c a).continuousOn_symm.comp continuousOn_snd
      (fun p hp => (hQ a ha).2 hp.2)
  have hbaseT (a : M) {z : V} (hz : z ∈ (c a).target) :
      (c a).symm z ∈ (eT a).baseSet := by
    simpa only [eT, c, V, TangentBundle.trivializationAt_baseSet] using
      (c a).map_target hz
  have hginv (g : ℝ → RiemannianMetric n M)
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J')) (a : M) (ha : a ∈ s) :
      ContinuousOn (fun p => (gmod g a p).inverse) (K ×ˢ Q a) := by
    have hgsm := (contMDiffOn_family_metric_frame_inverse hg a).2.2
    exact hgsm.continuousOn.comp (hchartK a ha) (fun p hp =>
      ⟨hKsub hp.1, hbaseT a ((hQ a ha).2 hp.2)⟩)
  have hgamma (g : ℝ → RiemannianMetric n M)
      (D : (t : ℝ) → LeviCivitaData (g t))
      (hg : RiemannianMetric.IsSmoothFamilyOn g (J ∩ J'))
      (a : M) (ha : a ∈ s) (i j : Fin n) :
      ContinuousOn (fun p : ℝ × V =>
        (eT a).continuousLinearMapAt ℝ ((c a).symm p.2)
          ((D p.1).connection (frame a j) ((c a).symm p.2)
            (frame a i ((c a).symm p.2)))) (K ×ˢ Q a) := by
    have hs := contMDiffOn_connection_family_apply hg D (eT a).open_baseSet
      (frame a j) (frame a i) (hframe a j) (hframe a i)
    have hmaps : MapsTo (fun p : ℝ × M => TotalSpace.mk' V p.2
        ((D p.1).connection (frame a j) p.2 (frame a i p.2)))
        ((J ∩ J') ×ˢ (eT a).baseSet) (eT a).source := by
      intro p hp
      exact ((eT a).mem_source).mpr hp.2
    have hc := ((eT a).contMDiffOn_iff hmaps).mp hs
    apply (hc.2.continuousOn.comp (hchartK a ha) (fun p hp =>
      ⟨hKsub hp.1, hbaseT a ((hQ a ha).2 hp.2)⟩)).congr
    intro p hp
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ (eT a)
      (hbaseT a ((hQ a ha).2 hp.2)) _
  have hrmod' (a : M) : ContDiffOn ℝ ∞ (rmod' a)
      (J' ×ˢ (c a).target) := by
    have hh := contDiffOn_family_bundle_coordinates (E := BS) qS R' hR'sm a
      (hbaseS a)
    have hnative := qS.symm.contDiff.comp_contDiffOn hh
    have hnative' : ContDiffOn ℝ ∞
        (fun p : ℝ × V => ((eS a) (TotalSpace.mk' FS ((c a).symm p.2)
          (R' p.1 ((c a).symm p.2)))).2) (J' ×ˢ (c a).target) := by
      simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hnative
    exact τ.contDiff.comp_contDiffOn hnative'
  have hpartial (a : M) (j k i : Fin n) : ContinuousOn
      (fun p : ℝ × V => fderiv ℝ (fun z => rmod' a (p.1, z)
          (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)) p.2
        (EuclideanSpace.single i 1)) (J' ×ˢ (c a).target) := by
    let r : ℝ × V → ℝ := fun p => rmod' a p
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
    have hr : ContDiffOn ℝ ∞ r (J' ×ˢ (c a).target) :=
      ((hrmod' a).clm_apply contDiffOn_const).clm_apply contDiffOn_const
    have hw : ContDiffOn ℝ ∞ (fun p : ℝ × V =>
        fderivWithin ℝ (fun z => r (p.1, z)) (c a).target p.2
          (EuclideanSpace.single i 1)) (J' ×ˢ (c a).target) := by
      intro p hp
      have hh : ContDiffWithinAt ℝ ∞
          (fun q : (ℝ × V) × V => r (q.1.1, q.2))
          ((J' ×ˢ (c a).target) ×ˢ (c a).target) (p, p.2) :=
        (hr p hp).comp (p, p.2)
          (contDiffWithinAt_fst.fst.prodMk contDiffWithinAt_snd)
          (fun (q : (ℝ × V) × V)
            (hq : q ∈ (J' ×ˢ (c a).target) ×ˢ (c a).target) => ⟨hq.1.1, hq.2⟩)
      exact hh.fderivWithin_apply contDiffWithinAt_snd contDiffWithinAt_const
        (c a).open_target.uniqueDiffOn (by simp) hp (fun q hq => hq.2)
    apply hw.continuousOn.congr
    intro p hp
    change fderiv ℝ (fun z => r (p.1, z)) p.2 _ =
      fderivWithin ℝ (fun z => r (p.1, z)) (c a).target p.2 _
    rw [fderivWithin_of_mem_nhds ((c a).open_target.mem_nhds hp.2)]
  let cp := fun (a : M) (p : ℝ × V) (i j k : Fin n) =>
    fderiv ℝ (fun z => rmod' a (p.1, z) (EuclideanSpace.single j 1)
      (EuclideanSpace.single k 1)) p.2 (EuclideanSpace.single i 1) -
      rmod' a p (gamma' a p i j) (EuclideanSpace.single k 1) -
      rmod' a p (EuclideanSpace.single j 1) (gamma' a p i k)
  let vp := fun (a : M) (p : ℝ × V) (i j : Fin n) =>
    (gmod F'.metric a p).inverse
      (∑ k : Fin n, (-cp a p i j k - cp a p j k i + cp a p k i j) •
        EuclideanSpace.proj k)
  have hrcont (a : M) (ha : a ∈ s) : ContinuousOn (rmod' a) (K ×ˢ Q a) :=
    (hrmod' a).continuousOn.mono (Set.prod_mono (fun t ht => (hKsub ht).2)
      (hQ a ha).2)
  have hcp (a : M) (ha : a ∈ s) (i j k : Fin n) :
      ContinuousOn (fun p => cp a p i j k) (K ×ˢ Q a) := by
    apply ((hpartial a j k i).mono (Set.prod_mono (fun t ht => (hKsub ht).2)
      (hQ a ha).2)).sub
      (((hrcont a ha).clm_apply (hgamma F'.metric F'.connection hF' a ha i j)).clm_apply
        continuousOn_const) |>.sub
      (((hrcont a ha).clm_apply continuousOn_const).clm_apply
        (hgamma F'.metric F'.connection hF' a ha i k))
  have hvp (a : M) (ha : a ∈ s) (i j : Fin n) :
      ContinuousOn (fun p => vp a p i j) (K ×ˢ Q a) := by
    apply (hginv F'.metric hF' a ha).clm_apply
    apply continuousOn_finsetSum
    intro k hk
    exact (((hcp a ha i j k).neg.sub (hcp a ha j k i)).add (hcp a ha k i j)).smul
      continuousOn_const
  let theta := fun (α : Fin dA) (l j i : Fin n) =>
    qA ((EuclideanSpace.proj j).smulRight
      ((EuclideanSpace.proj i).smulRight (EuclideanSpace.single l 1))) α
  let sigma := fun (β : Fin dS) => τ (qS.symm (EuclideanSpace.single β 1))
  let combine := fun (a : M) (p : ℝ × V) (α : Fin dA)
      (v : Fin n → Fin n → Fin n → ℝ) =>
    ∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
      theta α l j i * ((gmod F.metric a p).inverse (EuclideanSpace.proj k)) l * v i j k
  let cd := fun (a : M) (p : ℝ × V) (α : Fin dA) (β : Fin dS × Fin n) =>
    combine a p α (fun i j k =>
      -(if i = β.2 then sigma β.1 (EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1) else 0) -
       (if j = β.2 then sigma β.1 (EuclideanSpace.single k 1)
          (EuclideanSpace.single i 1) else 0) +
       (if k = β.2 then sigma β.1 (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) else 0))
  let ch := fun (a : M) (p : ℝ × V) (α : Fin dA) (β : Fin dH) =>
    combine a p α (fun i j k =>
      -(qH.symm (EuclideanSpace.single β 1)) (vp a p i j) (EuclideanSpace.single k 1))
  let ca := fun (a : M) (p : ℝ × V) (α β : Fin dA) =>
    combine a p α (fun i j k => 2 * rmod' a p
      ((qA.symm (EuclideanSpace.single β 1)) (EuclideanSpace.single j 1)
        (EuclideanSpace.single i 1)) (EuclideanSpace.single k 1))
  let cs := fun (a : M) (p : ℝ × V) (α : Fin dA) (β : Fin dS) =>
    combine a p α (fun i j k =>
      sigma β (gamma a p i j) (EuclideanSpace.single k 1) +
      sigma β (EuclideanSpace.single j 1) (gamma a p i k) +
      sigma β (gamma a p j k) (EuclideanSpace.single i 1) +
      sigma β (EuclideanSpace.single k 1) (gamma a p j i) -
      sigma β (gamma a p k i) (EuclideanSpace.single j 1) -
      sigma β (EuclideanSpace.single i 1) (gamma a p k j))
  have hcombine (a : M) (ha : a ∈ s) (α : Fin dA)
      (v : (ℝ × V) → Fin n → Fin n → Fin n → ℝ)
      (hv : ∀ i j k, ContinuousOn (fun p => v p i j k) (K ×ˢ Q a)) :
      ContinuousOn (fun p => combine a p α (v p)) (K ×ˢ Q a) := by
    apply continuousOn_finsetSum
    intro l hl
    apply continuousOn_finsetSum
    intro j hj
    apply continuousOn_finsetSum
    intro i hi
    apply continuousOn_finsetSum
    intro k hk
    apply ContinuousOn.mul _ (hv i j k)
    exact continuousOn_const.mul ((EuclideanSpace.proj l).continuous.comp_continuousOn
      ((hginv F.metric hF a ha).clm_apply continuousOn_const))
  have hcd (a : M) (ha : a ∈ s) (α : Fin dA) (β : Fin dS × Fin n) :
      ContinuousOn (fun p => cd a p α β) (K ×ˢ Q a) := by
    apply hcombine a ha α
    intro i j k
    exact continuousOn_const
  have hch (a : M) (ha : a ∈ s) (α : Fin dA) (β : Fin dH) :
      ContinuousOn (fun p => ch a p α β) (K ×ˢ Q a) := by
    apply hcombine a ha α
    intro i j k
    exact ((continuousOn_const.clm_apply (hvp a ha i j)).clm_apply continuousOn_const).neg
  have hca (a : M) (ha : a ∈ s) (α β : Fin dA) :
      ContinuousOn (fun p => ca a p α β) (K ×ˢ Q a) := by
    apply hcombine a ha α
    intro i j k
    exact continuousOn_const.mul
      (((hrcont a ha).clm_apply continuousOn_const).clm_apply continuousOn_const)
  have hcs (a : M) (ha : a ∈ s) (α : Fin dA) (β : Fin dS) :
      ContinuousOn (fun p => cs a p α β) (K ×ˢ Q a) := by
    apply hcombine a ha α
    intro i j k
    exact (((((continuousOn_const.clm_apply (hgamma F.metric F.connection hF a ha i j)).clm_apply
      continuousOn_const).add ((continuousOn_const.clm_apply continuousOn_const).clm_apply
      (hgamma F.metric F.connection hF a ha i k))).add
      ((continuousOn_const.clm_apply (hgamma F.metric F.connection hF a ha j k)).clm_apply
        continuousOn_const)).add ((continuousOn_const.clm_apply continuousOn_const).clm_apply
      (hgamma F.metric F.connection hF a ha j i))).sub
      ((continuousOn_const.clm_apply (hgamma F.metric F.connection hF a ha k i)).clm_apply
        continuousOn_const) |>.sub
      ((continuousOn_const.clm_apply continuousOn_const).clm_apply
        (hgamma F.metric F.connection hF a ha k j))
  let coeffSq := fun (a : M) (p : ℝ × V) =>
    (∑ α : Fin dA, ∑ β : Fin dS × Fin n, (cd a p α β) ^ 2) +
      (∑ α : Fin dA, ∑ β : Fin dH, (ch a p α β) ^ 2) +
      (∑ α : Fin dA, ∑ β : Fin dA, (ca a p α β) ^ 2) +
      (∑ α : Fin dA, ∑ β : Fin dS, (cs a p α β) ^ 2)
  have hcoeffSq (a : M) (ha : a ∈ s) : ContinuousOn (coeffSq a) (K ×ˢ Q a) := by
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · apply ContinuousOn.add
        · exact continuousOn_finsetSum Finset.univ (fun α _ =>
            continuousOn_finsetSum Finset.univ (fun β _ => (hcd a ha α β).pow 2))
        · exact continuousOn_finsetSum Finset.univ (fun α _ =>
            continuousOn_finsetSum Finset.univ (fun β _ => (hch a ha α β).pow 2))
      · exact continuousOn_finsetSum Finset.univ (fun α _ =>
          continuousOn_finsetSum Finset.univ (fun β _ => (hca a ha α β).pow 2))
    · exact continuousOn_finsetSum Finset.univ (fun α _ =>
        continuousOn_finsetSum Finset.univ (fun β _ => (hcs a ha α β).pow 2))
  have hcompactBound (a : M) (ha : a ∈ s) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ K ×ˢ Q a, coeffSq a p ≤ B := by
    obtain ⟨B, hB⟩ := (hK.prod (hQ a ha).1).exists_bound_of_continuousOn (hcoeffSq a ha)
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro p hp
    exact (le_abs_self _).trans ((hB p hp).trans (le_max_left _ _))
  let bound := fun a : M => if ha : a ∈ s then Classical.choose (hcompactBound a ha) else 0
  have hbound (a : M) (ha : a ∈ s) :
      0 ≤ bound a ∧ ∀ p ∈ K ×ˢ Q a, coeffSq a p ≤ bound a := by
    dsimp only [bound]
    rw [dif_pos ha]
    exact Classical.choose_spec (hcompactBound a ha)
  let B : ℝ := ∑ a ∈ s, bound a
  have hB : 0 ≤ B := Finset.sum_nonneg (fun a ha => (hbound a ha).1)
  have hBbound (a : M) (ha : a ∈ s) {p : ℝ × V} (hp : p ∈ K ×ˢ Q a) :
      coeffSq a p ≤ B :=
    ((hbound a ha).2 p hp).trans (Finset.single_le_sum (fun b hb => (hbound b hb).1) ha)
  refine ⟨B + 1, by positivity, ?_⟩
  intro ε hε t ht a ha z hz
  have hzChart : z ∈ (c a).target := (hQ a ha).2 hz
  have htInt : t ∈ interior (J ∩ J') := interior_mono hKsub ht
  have htJ : t ∈ J ∩ J' := interior_subset htInt
  have htJint : t ∈ interior J := interior_mono inter_subset_left htInt
  have htJ'int : t ∈ interior J' := interior_mono inter_subset_right htInt
  have htN : J ∩ J' ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp htInt
  have hpointA : DifferentiableAt ℝ
      (fun p : ℝ × V => qA ((eA a) (TotalSpace.mk' FA ((c a).symm p.2)
        (A p.1 ((c a).symm p.2)))).2) (t, z) :=
    ((hacoord a (t, z) ⟨htJ, hzChart⟩).contDiffAt
      (prod_mem_nhds htN ((c a).open_target.mem_nhds hzChart))).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun r : ℝ => (r, z)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  have hcoord : HasDerivAt
      (fun r : ℝ => qA ((eA a) (TotalSpace.mk' FA ((c a).symm z)
        (A r ((c a).symm z)))).2)
      (fderiv ℝ (fun p : ℝ × V => qA ((eA a) (TotalSpace.mk' FA ((c a).symm p.2)
        (A p.1 ((c a).symm p.2)))).2) (t, z) (1, 0)) t :=
    by simpa only [Function.comp_def] using
      hpointA.hasFDerivAt.comp_hasDerivAt t hcurve
  let e := trivializationAt V (TangentSpace (𝓡 n)) a
  let x := (c a).symm z
  let E := fun k : Fin n => fun y : M => e.symmL ℝ y (EuclideanSpace.single k 1)
  have hx : x ∈ e.baseSet := by
    simpa only [x, e, c, V, TangentBundle.trivializationAt_baseSet] using
      (c a).map_target hzChart
  have hG (g : RiemannianMetric n M) :
      (ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
        a x a x (g.inner x)).IsInvertible := by
    apply isInvertible_bilinear_of_pos
    intro v hv
    have heval :
        ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
          (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
          a x a x (g.inner x) v v =
          g.inner x (e.symmL ℝ x v) (e.symmL ℝ x v) := by
      rw [inCoordinates_apply_eq₂
        (F₁ := V) (F₂ := V) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M => ℝ) hx hx (by simp)]
      rw [← Trivialization.symmL_apply (R := ℝ) e hx v]
      simp
    rw [heval]
    apply g.pos x
    intro hzv
    have hzv' := congrArg (e.continuousLinearMapAt ℝ x) hzv
    rw [Trivialization.continuousLinearMapAt_symmL _ hx, map_zero] at hzv'
    exact hv hzv'
  have hE (k : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E k)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := 𝓡 n) (n := ∞)]
    refine (contMDiffOn_const (c := EuclideanSpace.single k 1)).congr ?_
    intro y hy
    simpa [E, Trivialization.symmL_apply _ hy] using
      congrArg Prod.snd (e.apply_mk_symm hy (EuclideanSpace.single k 1))
  let G := fun g : RiemannianMetric n M =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      a x a x (g.inner x)
  let L := e.continuousLinearMapAt ℝ x
  have hbridge (f : M → ℝ)
      (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) (k : Fin n) :
      fderiv ℝ (fun q => f ((extChartAt (𝓡 n) x).symm q))
          ((extChartAt (𝓡 n) x) x) (E k x) =
        fderiv ℝ (fun q => f ((c a).symm q)) z
          (EuclideanSpace.single k 1) := by
    exact (centered_scalar_derivative f x hf (E k x)).trans
      (fixed_scalar_derivative f a hzChart hf (EuclideanSpace.single k 1)).symm
  have hpairF (k l : Fin n) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => (F.connection t).ricci y (E k y) (E l y)) x :=
    ricci_pair_smooth F htJint e.open_baseSet (E k) (E l)
      (hE k) (hE l) hx
  have hpairF' (k l : Fin n) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => (F'.connection t).ricci y (E k y) (E l y)) x :=
    ricci_pair_smooth F' htJ'int e.open_baseSet (E k) (E l)
      (hE k) (hE l) hx
  let C' := fun (i j k : Fin n) =>
    fderiv ℝ (fun q => (F'.connection t).ricci ((extChartAt (𝓡 n) x).symm q)
      (E j ((extChartAt (𝓡 n) x).symm q)) (E k ((extChartAt (𝓡 n) x).symm q)))
      ((extChartAt (𝓡 n) x) x) (E i x) -
      (F'.connection t).ricci x ((F'.connection t).connection (E j) x (E i x))
        (E k x) -
      (F'.connection t).ricci x (E j x)
        ((F'.connection t).connection (E k) x (E i x))
  let C := fun (i j k : Fin n) =>
    fderiv ℝ (fun q =>
      ((F.connection t).ricci ((extChartAt (𝓡 n) x).symm q)
        (E j ((extChartAt (𝓡 n) x).symm q))
        (E k ((extChartAt (𝓡 n) x).symm q))) -
      ((F'.connection t).ricci ((extChartAt (𝓡 n) x).symm q)
        (E j ((extChartAt (𝓡 n) x).symm q))
        (E k ((extChartAt (𝓡 n) x).symm q))))
      ((extChartAt (𝓡 n) x) x) (E i x) -
      ((F.connection t).ricci x ((F.connection t).connection (E j) x (E i x))
        (E k x) -
       (F'.connection t).ricci x ((F.connection t).connection (E j) x (E i x))
        (E k x)) -
      ((F.connection t).ricci x (E j x)
        ((F.connection t).connection (E k) x (E i x)) -
       (F'.connection t).ricci x (E j x)
        ((F.connection t).connection (E k) x (E i x)))
  have hC (i j k : Fin n) :
      C i j k = fderiv ℝ (fun q =>
        ((F.connection t).ricci ((c a).symm q)
          (E j ((c a).symm q)) (E k ((c a).symm q))) -
        ((F'.connection t).ricci ((c a).symm q)
          (E j ((c a).symm q)) (E k ((c a).symm q)))) z
        (EuclideanSpace.single i 1) -
        ((F.connection t).ricci x ((F.connection t).connection (E j) x (E i x))
          (E k x) -
         (F'.connection t).ricci x ((F.connection t).connection (E j) x (E i x))
          (E k x)) -
        ((F.connection t).ricci x (E j x)
          ((F.connection t).connection (E k) x (E i x)) -
         (F'.connection t).ricci x (E j x)
          ((F.connection t).connection (E k) x (E i x))) := by
    dsimp only [C]
    rw [hbridge _ ((hpairF j k).sub (hpairF' j k) |>.mdifferentiableAt (by simp)) i]
  have hC' (i j k : Fin n) :
      C' i j k = fderiv ℝ (fun q =>
        ((F'.connection t).ricci ((c a).symm q)
          (E j ((c a).symm q)) (E k ((c a).symm q)))) z
        (EuclideanSpace.single i 1) -
        (F'.connection t).ricci x ((F'.connection t).connection (E j) x (E i x))
          (E k x) -
        (F'.connection t).ricci x (E j x)
          ((F'.connection t).connection (E k) x (E i x)) := by
    dsimp only [C']
    rw [hbridge _ ((hpairF' j k).mdifferentiableAt (by simp)) i]
  have hpair' (i j k : Fin n) :
      HasDerivAt (fun r : ℝ => (F'.connection r).connection (E j) x (E i x))
        (deriv (fun r : ℝ => (F'.connection r).connection (E j) x (E i x)) t) t ∧
      (F'.metric t).inner x
          (deriv (fun r : ℝ => (F'.connection r).connection (E j) x (E i x)) t)
          (E k x) = -C' i j k - C' j k i + C' k i j := by
    simpa only [C'] using
      (ricciFlow_connection_variation_pairing F' htJ'int
        e.open_baseSet (E i) (E j) (E k) (hE i) (hE j) (hE k) hx)
  let W' := fun (i j : Fin n) (r : ℝ) =>
    (F'.connection r).connection (E j) x (E i x)
  let Acurve := fun (i j : Fin n) (r : ℝ) =>
    CovariantDerivative.difference (F.connection r).connection
      (F'.connection r).connection x (E j x) (E i x)
  let GF := G (F.metric t)
  let GF' := G (F'.metric t)
  have hG_eval (g : RiemannianMetric n M) (v : TangentSpace (𝓡 n) x)
      (k : Fin n) : G g (L v) (EuclideanSpace.single k 1) =
        g.inner x v (E k x) := by
    dsimp [G, L]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hx hx (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hx (L v),
      ← Trivialization.symmL_apply (R := ℝ) e hx (EuclideanSpace.single k 1)]
    rw [Trivialization.symmL_continuousLinearMapAt e hx v]
    simp [E]
  have hA_pair (i j k : Fin n) :
      HasDerivAt (Acurve i j) (deriv (Acurve i j) t) t ∧
      (F.metric t).inner x (deriv (Acurve i j) t) (E k x) =
        -C i j k - C j k i + C k i j +
          2 * (F'.connection t).ricci x ((Acurve i j) t) (E k x) -
          ((F.metric t).inner x (deriv (W' i j) t) (E k x) -
            (F'.metric t).inner x (deriv (W' i j) t) (E k x)) := by
    simpa only [C, Acurve, W'] using
      (ricciFlow_connection_difference_evolution_pairing F F' hinit htJint htJ'int
        e.open_baseSet (E i) (E j) (E k) (hE i) (hE j) (hE k) hx)
  have hWnative (i j : Fin n) :
      L (deriv (W' i j) t) = GF'.inverse
        (∑ k : Fin n, (-C' i j k - C' j k i + C' k i j) • EuclideanSpace.proj k) := by
    apply native_from_pairings (hG (F'.metric t))
    intro k
    rw [hG_eval]
    exact (hpair' i j k).2
  let Hmod := GF - GF'
  have hAnative (i j : Fin n) :
      L (deriv (Acurve i j) t) = GF.inverse
        (∑ k : Fin n,
          (-C i j k - C j k i + C k i j +
            2 * (F'.connection t).ricci x ((Acurve i j) t) (E k x) -
            Hmod (GF'.inverse
              (∑ l : Fin n, (-C' i j l - C' j l i + C' l i j) •
                EuclideanSpace.proj l)) (EuclideanSpace.single k 1)) •
            EuclideanSpace.proj k) := by
    apply native_from_pairings (hG (F.metric t))
    intro k
    rw [hG_eval]
    have hp := (hA_pair i j k).2
    rw [← hG_eval (F.metric t) (deriv (W' i j) t) k,
      ← hG_eval (F'.metric t) (deriv (W' i j) t) k,
      hWnative i j] at hp
    dsimp [Hmod, GF, GF']
    simpa only [sub_apply] using hp
  let hCoord : FH :=
    ((eH a) (TotalSpace.mk' FH x (H t x))).2
  let aCoord : FA :=
    ((eA a) (TotalSpace.mk' FA x (A t x))).2
  let sCoord : FS :=
    ((eS a) (TotalSpace.mk' FS x (S t x))).2
  have hHmodel (u v : V) : Hmod u v = hCoord u v := by
    change G (F.metric t) u v - G (F'.metric t) u v = hCoord u v
    have hGeval (g : RiemannianMetric n M) (u v : V) :
        G g u v = g.inner x (e.symmL ℝ x u) (e.symmL ℝ x v) := by
      dsimp [G]
      rw [inCoordinates_apply_eq₂
        (F₁ := V) (F₂ := V) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M => ℝ) hx hx (by simp)]
      rw [← Trivialization.symmL_apply (R := ℝ) e hx u,
        ← Trivialization.symmL_apply (R := ℝ) e hx v]
      simp
    rw [hGeval, hGeval]
    dsimp [hCoord, eH]
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hx hx (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hx u,
      ← Trivialization.symmL_apply (R := ℝ) e hx v]
    simp [H]
  have hSmodel (u v w : V) :
      sCoord u v w =
        e.linearMapAt ℝ x (S t x (e.symmL ℝ x u) (e.symmL ℝ x v)
          (e.symmL ℝ x w)) := by
    have hxhom : x ∈ (trivializationAt (V →L[ℝ] V)
        (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y) a).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hx, hx⟩
    dsimp [sCoord, eS]
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := V →L[ℝ] V)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
      hx hx hxhom]
    rw [Trivialization.linearMapAt_apply, if_pos hxhom, hom_trivializationAt_apply]
    change ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n)) V
      (TangentSpace (𝓡 n)) a x a x
      (S t x (e.symm x u) (e.symm x v)) w = _
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      Trivialization.continuousLinearMapAt_apply]
    rw [Trivialization.symmL_apply (R := ℝ) e hx u,
      Trivialization.symmL_apply (R := ℝ) e hx v,
      Trivialization.symmL_apply (R := ℝ) e hx w]
  let sbar : V → FS := fun q =>
    ((eS a) (TotalSpace.mk' FS ((c a).symm q) (S t ((c a).symm q)))).2
  have hsbar_eval (q : V) (hq : q ∈ (c a).target) (u v w : V) :
      sbar q u v w =
        e.linearMapAt ℝ ((c a).symm q)
          (S t ((c a).symm q)
            (e.symmL ℝ ((c a).symm q) u)
            (e.symmL ℝ ((c a).symm q) v)
            (e.symmL ℝ ((c a).symm q) w)) := by
    have hy : (c a).symm q ∈ e.baseSet := by
      simpa only [e, c, V, TangentBundle.trivializationAt_baseSet] using
        (c a).map_target hq
    have hyhom : (c a).symm q ∈ (trivializationAt (V →L[ℝ] V)
        (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y) a).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hy, hy⟩
    dsimp [sbar, eS]
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := V →L[ℝ] V)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
      hy hy hyhom]
    rw [Trivialization.linearMapAt_apply, if_pos hyhom, hom_trivializationAt_apply]
    change ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n)) V
      (TangentSpace (𝓡 n)) a ((c a).symm q) a ((c a).symm q)
      (S t ((c a).symm q) (e.symm ((c a).symm q) u)
        (e.symm ((c a).symm q) v)) w = _
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      Trivialization.continuousLinearMapAt_apply]
    rw [Trivialization.symmL_apply (R := ℝ) e hy u,
      Trivialization.symmL_apply (R := ℝ) e hy v,
      Trivialization.symmL_apply (R := ℝ) e hy w]
  have htrace (q : V) (hq : q ∈ (c a).target) (u v : V) :
      τ (sbar q) u v =
        (F.connection t).ricci ((c a).symm q)
            (e.symmL ℝ ((c a).symm q) u) (e.symmL ℝ ((c a).symm q) v) -
        (F'.connection t).ricci ((c a).symm q)
            (e.symmL ℝ ((c a).symm q) u) (e.symmL ℝ ((c a).symm q) v) := by
    let y := (c a).symm q
    have hy : y ∈ e.baseSet := by
      simpa only [y, e, c, V, TangentBundle.trivializationAt_baseSet] using
        (c a).map_target hq
    let b := (PiLp.basisFun 2 ℝ (Fin n)).map (e.linearEquivAt ℝ y hy).symm
    have hbrepr (v : TangentSpace (𝓡 n) y) (p : Fin n) :
        b.repr v p = ((e.linearEquivAt ℝ y hy) v) p := by
      simp [b, Module.Basis.map_repr, PiLp.basisFun_repr]
    have hb (p : Fin n) : b p = E p y := by
      simp [b, E, Trivialization.symmL_apply _ hy]
    rw [hτ]
    rw [ricci_eq_sum_basis_of_curvature_pairing (F.connection t) y
      (e.symmL ℝ y u) (e.symmL ℝ y v) b,
      ricci_eq_sum_basis_of_curvature_pairing (F'.connection t) y
      (e.symmL ℝ y u) (e.symmL ℝ y v) b]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hb]
    rw [hbrepr, hbrepr]
    rw [← hR t y (E p y) (e.symmL ℝ y u) (e.symmL ℝ y v),
      ← hR' t y (E p y) (e.symmL ℝ y u) (e.symmL ℝ y v)]
    have hs := hsbar_eval q hq (EuclideanSpace.single p 1) u v
    rw [hs]
    change (e.linearMapAt ℝ y
      ((R t y) (e.symmL ℝ y (EuclideanSpace.single p 1))
        (e.symmL ℝ y u) (e.symmL ℝ y v) -
       (R' t y) (e.symmL ℝ y (EuclideanSpace.single p 1))
        (e.symmL ℝ y u) (e.symmL ℝ y v))).ofLp p = _
    rw [e.linearMapAt_def_of_mem hy, map_sub,
      hR t y (E p y) (e.symmL ℝ y u) (e.symmL ℝ y v),
      hR' t y (E p y) (e.symmL ℝ y u) (e.symmL ℝ y v)]
    rfl
  have hqS (T : FS) : T = ∑ β : Fin dS,
      (qS T β) • qS.symm (EuclideanSpace.single β 1) := by
    let b := PiLp.basisFun 2 ℝ (Fin dS)
    have hb (u : EuclideanSpace ℝ (Fin dS)) :
        u = ∑ β : Fin dS, u β • EuclideanSpace.single β 1 := by
      calc
        u = ∑ β, (b.repr u) β • b β := (b.sum_repr u).symm
        _ = ∑ β, u β • EuclideanSpace.single β 1 := by
          apply Finset.sum_congr rfl
          intro β hβ
          simp [b, PiLp.basisFun_repr, PiLp.basisFun_apply]
    calc
      T = qS.symm (qS T) := (qS.symm_apply_apply T).symm
      _ = qS.symm (∑ β, (qS T β) • EuclideanSpace.single β 1) :=
        congrArg qS.symm (hb (qS T))
      _ = _ := by simp only [map_sum, map_smul]
  let σ := fun (β : Fin dS) (u v : V) =>
    τ (qS.symm (EuclideanSpace.single β 1)) u v
  have htrace_expand (q : V) (hq : q ∈ (c a).target) (u v : V) :
      τ (sbar q) u v = ∑ β : Fin dS,
        fS a β (t, q) * σ β u v := by
    rw [hqS (sbar q), map_sum]
    simp only [map_smul, smul_eq_mul, sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro β hβ
    rfl
  have hCderiv (i j k : Fin n) :
      fderiv ℝ (fun q : V =>
        ((F.connection t).ricci ((c a).symm q)
          (E j ((c a).symm q)) (E k ((c a).symm q))) -
        ((F'.connection t).ricci ((c a).symm q)
          (E j ((c a).symm q)) (E k ((c a).symm q)))) z
        (EuclideanSpace.single i 1) =
      ∑ β : Fin dS,
        σ β (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) *
          (fderiv ℝ (fun q => fS a β (t, q)) z
            (EuclideanSpace.single i 1)) := by
    let r : V → ℝ := fun q =>
      ((F.connection t).ricci ((c a).symm q)
        (E j ((c a).symm q)) (E k ((c a).symm q))) -
      ((F'.connection t).ricci ((c a).symm q)
        (E j ((c a).symm q)) (E k ((c a).symm q)))
    have heq : r =ᶠ[𝓝 z] (fun q => ∑ β : Fin dS,
        fS a β (t, q) * σ β (EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1)) := by
      filter_upwards [(c a).open_target.mem_nhds hzChart] with q hq
      dsimp [r]
      rw [← htrace q hq (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1)]
      exact htrace_expand q hq (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1)
    have hf (β : Fin dS) :
        DifferentiableAt ℝ (fun q => fS a β (t, q)) z := by
      have hh := (hScoord a (t, z) ⟨htJ, hzChart⟩).contDiffAt
        (prod_mem_nhds htN ((c a).open_target.mem_nhds hzChart))
      have hd := hh.differentiableAt (by simp)
      have hg : DifferentiableAt ℝ (fun q : V => (t, q)) z := by
        fun_prop
      have hcoord := hd.comp z hg
      have hproj := (EuclideanSpace.proj β).differentiableAt.comp z hcoord
      simpa only [fS, Function.comp_def, EuclideanSpace.coe_proj] using hproj
    change fderiv ℝ r z (EuclideanSpace.single i 1) = _
    rw [heq.fderiv_eq]
    rw [fderiv_fun_sum (fun β _ =>
      (hf β).mul_const (σ β (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1)))]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro β hβ
    rw [fderiv_mul_const (hf β)
      (σ β (EuclideanSpace.single j 1) (EuclideanSpace.single k 1))]
    simp only [smul_apply, smul_eq_mul]
  have hCexpand (i j k : Fin n) :
      C i j k =
        (∑ β : Fin dS,
          σ β (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) *
            fderiv ℝ (fun q => fS a β (t, q)) z
              (EuclideanSpace.single i 1)) -
        ((F.connection t).ricci x
            ((F.connection t).connection (E j) x (E i x)) (E k x) -
          (F'.connection t).ricci x
            ((F.connection t).connection (E j) x (E i x)) (E k x)) -
        ((F.connection t).ricci x (E j x)
            ((F.connection t).connection (E k) x (E i x)) -
          (F'.connection t).ricci x (E j x)
            ((F.connection t).connection (E k) x (E i x))) := by
    rw [hC i j k, hCderiv i j k]
  let θ := fun (α : Fin dA) (l j i : Fin n) =>
    (qA ((EuclideanSpace.proj j).smulRight
      ((EuclideanSpace.proj i).smulRight (EuclideanSpace.single l 1))) α)
  have hAeval (r : ℝ) (i j l : Fin n) :
      (((eA a) (TotalSpace.mk' FA x (A r x))).2
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) l =
        (L (Acurve i j r)) l := by
    have hxhom : x ∈ (trivializationAt (V →L[ℝ] V)
        (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y) a).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hx, hx⟩
    dsimp [eA]
    rw [hom_trivializationAt_apply]
    dsimp only [Bundle.TotalSpace.mk']
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := V)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun y : M => TangentSpace (𝓡 n) y)
      hx hx hx]
    rw [Trivialization.linearMapAt_apply, if_pos hx]
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hx]
    dsimp [Acurve, E]
    rw [Trivialization.symmL_apply (R := ℝ) e hx,
      Trivialization.symmL_apply (R := ℝ) e hx]
  have hAmodel (i j l : Fin n) :
      (aCoord (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) l =
        (L (Acurve i j t)) l := by
    exact hAeval t i j l
  have hfrepr (r : ℝ) (α : Fin dA) :
      fA a α (r, z) = ∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n,
        θ α l j i * (L (Acurve i j r)) l := by
    dsimp only [fA]
    rw [tensor_coordinate_reconstruct qA
      (((eA a) (TotalSpace.mk' FA x (A r x))).2) α]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [hAeval]
  have hderivA (α : Fin dA) :
      HasDerivAt (fun r : ℝ => fA a α (r, z))
        (∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n,
          θ α l j i * (L (deriv (Acurve i j) t)) l) t := by
    have hterm (l j i : Fin n) :
        HasDerivAt (fun r : ℝ => θ α l j i * (L (Acurve i j r)) l)
          (θ α l j i * (L (deriv (Acurve i j) t)) l) t := by
      have hL := (hasDerivAt_const t L).clm_apply (hA_pair i j l).1
      have hproj : HasDerivAt
          (fun r : ℝ => (EuclideanSpace.proj l) (L (Acurve i j r)))
          ((EuclideanSpace.proj l) (L (deriv (Acurve i j) t))) t :=
        by
          simpa only [zero_apply, zero_add, add_zero] using
            (hasDerivAt_const t (EuclideanSpace.proj l)).clm_apply hL
      have hp := hproj.const_mul (θ α l j i)
      simpa [Function.comp_def, EuclideanSpace.coe_proj,
        ContinuousLinearMap.coe_coe] using hp
    have hs := HasDerivAt.sum (u := Finset.univ) (fun l _ =>
      HasDerivAt.sum (u := Finset.univ) (fun j _ =>
        HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm l j i)))
    have hsumfun :
        (fun r : ℝ => ∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n,
          θ α l j i * (L (Acurve i j r)) l) =
          (∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n,
            fun r : ℝ => θ α l j i * (L (Acurve i j r)) l) := by
      funext r
      simp only [Finset.sum_apply]
    rw [← hsumfun] at hs
    exact hs.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun r => hfrepr r α))
  have hderiv_coord (α : Fin dA) :
      fderiv ℝ (fA a α) (t, z) (1, 0) =
        ∑ l : Fin n, ∑ j : Fin n, ∑ i : Fin n,
          θ α l j i * (L (deriv (Acurve i j) t)) l := by
    have hfunα : DifferentiableAt ℝ (fA a α) (t, z) := by
      have h := (EuclideanSpace.proj α).differentiableAt.comp (t, z) hpointA
      simpa only [fA, Function.comp_def, EuclideanSpace.coe_proj] using h
    have hjointα := hfunα.hasFDerivAt.comp_hasDerivAt t hcurve
    exact hjointα.unique (hderivA α)
  have hsum : (∑ i : Fin dA, 2 * fA a i (t, z) *
      fderiv ℝ (fA a i) (t, z) (1, 0)) =
      ∑ i : Fin dA, 2 * fA a i (t, z) *
        (∑ l : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          θ i l j k * (L (deriv (Acurve k j) t)) l) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hd := hderiv_coord i
    simpa only using congrArg (fun q : ℝ => 2 * fA a i (t, z) * q) hd
  have hrprime (q : V) (hq : q ∈ (c a).target) (u v : V) :
      rmod' a (t, q) u v = (F'.connection t).ricci ((c a).symm q)
        (e.symmL ℝ ((c a).symm q) u) (e.symmL ℝ ((c a).symm q) v) := by
    let y := (c a).symm q
    have hy : y ∈ e.baseSet := hbaseT a hq
    let b := (PiLp.basisFun 2 ℝ (Fin n)).map (e.linearEquivAt ℝ y hy).symm
    have hbrepr (w : TangentSpace (𝓡 n) y) (k : Fin n) :
        b.repr w k = ((e.linearEquivAt ℝ y hy) w) k := by
      simp [b, Module.Basis.map_repr, PiLp.basisFun_repr]
    have hb (k : Fin n) : b k = E k y := by
      simp [b, E, Trivialization.symmL_apply _ hy]
    have heval (u v w : V) :
        (((eS a) (TotalSpace.mk' FS y (R' t y))).2) u v w =
          e.linearMapAt ℝ y (R' t y (e.symmL ℝ y u)
            (e.symmL ℝ y v) (e.symmL ℝ y w)) := by
      have hyhom : y ∈ (trivializationAt (V →L[ℝ] V)
          (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y) a).baseSet := by
        rw [hom_trivializationAt_baseSet]
        exact ⟨hy, hy⟩
      dsimp only [eS]
      rw [hom_trivializationAt_apply]
      rw [inCoordinates_apply_eq₂
        (F₁ := V) (F₂ := V) (F₃ := V →L[ℝ] V)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        hy hy hyhom]
      rw [Trivialization.linearMapAt_apply, if_pos hyhom, hom_trivializationAt_apply]
      change ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n)) V
        (TangentSpace (𝓡 n)) a y a y
        (R' t y (e.symm y u) (e.symm y v)) w = _
      simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
        Trivialization.continuousLinearMapAt_apply]
      rw [Trivialization.symmL_apply (R := ℝ) e hy u,
        Trivialization.symmL_apply (R := ℝ) e hy v,
        Trivialization.symmL_apply (R := ℝ) e hy w]
    change τ (((eS a) (TotalSpace.mk' FS y (R' t y))).2) u v = _
    rw [hτ, ricci_eq_sum_basis_of_curvature_pairing (F'.connection t) y
      (e.symmL ℝ y u) (e.symmL ℝ y v) b]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hb, hbrepr, heval, hR']
    rw [e.linearMapAt_def_of_mem hy]
    rfl
  have hcp_eq (i j k : Fin n) : C' i j k = cp a (t, z) i j k := by
    have heq : (fun q => (F'.connection t).ricci ((c a).symm q)
        (E j ((c a).symm q)) (E k ((c a).symm q))) =ᶠ[𝓝 z]
        (fun q => rmod' a (t, q) (EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1)) := by
      filter_upwards [(c a).open_target.mem_nhds hzChart] with q hq
      exact (hrprime q hq _ _).symm
    rw [hC', heq.fderiv_eq]
    dsimp only [cp]
    rw [hrprime z hzChart, hrprime z hzChart]
    change _ = _ - (F'.connection t).ricci x
        (e.symmL ℝ x (L ((F'.connection t).connection (E j) x (E i x)))) (E k x) -
      (F'.connection t).ricci x (E j x)
        (e.symmL ℝ x (L ((F'.connection t).connection (E k) x (E i x))))
    rw [Trivialization.symmL_continuousLinearMapAt e hx,
      Trivialization.symmL_continuousLinearMapAt e hx]
  have hvp_eq (i j : Fin n) : GF'.inverse
      (∑ k : Fin n, (-C' i j k - C' j k i + C' k i j) • EuclideanSpace.proj k) =
        vp a (t, z) i j := by
    simp only [hcp_eq]
    rfl
  have hRicciModel (u v : TangentSpace (𝓡 n) x) :
      (F.connection t).ricci x u v - (F'.connection t).ricci x u v =
        τ (sbar z) (L u) (L v) := by
    rw [htrace z hzChart]
    rw [Trivialization.symmL_continuousLinearMapAt e hx,
      Trivialization.symmL_continuousLinearMapAt e hx]
  have hLE (i : Fin n) : L (E i x) = EuclideanSpace.single i 1 :=
    Trivialization.continuousLinearMapAt_symmL e hx _
  have hCfull (i j k : Fin n) : C i j k =
      (∑ β : Fin dS, sigma β (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) *
        fderiv ℝ (fun q => fS a β (t, q)) z (EuclideanSpace.single i 1)) -
      (∑ β : Fin dS, fS a β (t, z) * sigma β (gamma a (t, z) i j)
        (EuclideanSpace.single k 1)) -
      (∑ β : Fin dS, fS a β (t, z) * sigma β (EuclideanSpace.single j 1)
        (gamma a (t, z) i k)) := by
    rw [hCexpand, hRicciModel, hRicciModel, hLE, hLE]
    rw [htrace_expand z hzChart, htrace_expand z hzChart]
  have hqcoord {d : ℕ} {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
      (q : T ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (w : T) :
      w = ∑ β : Fin d, q w β • q.symm (EuclideanSpace.single β 1) := by
    let b := PiLp.basisFun 2 ℝ (Fin d)
    have hb : q w = ∑ β : Fin d, q w β • EuclideanSpace.single β 1 := by
      calc
        q w = ∑ β : Fin d, (b.repr (q w)) β • b β := (b.sum_repr (q w)).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro β hβ
          simp [b, PiLp.basisFun_repr, PiLp.basisFun_apply]
    calc
      w = q.symm (q w) := (q.symm_apply_apply w).symm
      _ = q.symm (∑ β : Fin d, q w β • EuclideanSpace.single β 1) := congrArg q.symm hb
      _ = _ := by simp only [map_sum, map_smul]
  have hHexpand (i j k : Fin n) :
      Hmod (vp a (t, z) i j) (EuclideanSpace.single k 1) =
        ∑ β : Fin dH, fH a β (t, z) *
          (qH.symm (EuclideanSpace.single β 1)) (vp a (t, z) i j)
            (EuclideanSpace.single k 1) := by
    rw [hHmodel, hqcoord qH hCoord]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    rfl
  have hRexpand (i j k : Fin n) :
      (F'.connection t).ricci x (Acurve i j t) (E k x) =
        ∑ β : Fin dA, fA a β (t, z) * rmod' a (t, z)
          ((qA.symm (EuclideanSpace.single β 1)) (EuclideanSpace.single j 1)
            (EuclideanSpace.single i 1)) (EuclideanSpace.single k 1) := by
    have haeval : aCoord (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) =
        L (Acurve i j t) := by
      ext l
      exact hAmodel i j l
    have hh := hrprime z hzChart (L (Acurve i j t)) (EuclideanSpace.single k 1)
    rw [Trivialization.symmL_continuousLinearMapAt e hx] at hh
    rw [← hh, ← haeval, hqcoord qA aCoord]
    simp only [sum_apply, smul_apply, map_sum, map_smul, smul_eq_mul]
    rfl
  let d := fun β : Fin dS × Fin n => fderiv ℝ (fun q => fS a β.1 (t, q)) z
    (EuclideanSpace.single β.2 1)
  let dcoef := fun (β : Fin dS × Fin n) (i j k : Fin n) =>
    -(if i = β.2 then sigma β.1 (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) else 0) -
     (if j = β.2 then sigma β.1 (EuclideanSpace.single k 1)
        (EuclideanSpace.single i 1) else 0) +
     (if k = β.2 then sigma β.1 (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) else 0)
  let hcoef := fun (β : Fin dH) (i j k : Fin n) =>
    -(qH.symm (EuclideanSpace.single β 1)) (vp a (t, z) i j) (EuclideanSpace.single k 1)
  let acoef := fun (β : Fin dA) (i j k : Fin n) => 2 * rmod' a (t, z)
    ((qA.symm (EuclideanSpace.single β 1)) (EuclideanSpace.single j 1)
      (EuclideanSpace.single i 1)) (EuclideanSpace.single k 1)
  let scoef := fun (β : Fin dS) (i j k : Fin n) =>
    sigma β (gamma a (t, z) i j) (EuclideanSpace.single k 1) +
    sigma β (EuclideanSpace.single j 1) (gamma a (t, z) i k) +
    sigma β (gamma a (t, z) j k) (EuclideanSpace.single i 1) +
    sigma β (EuclideanSpace.single k 1) (gamma a (t, z) j i) -
    sigma β (gamma a (t, z) k i) (EuclideanSpace.single j 1) -
    sigma β (EuclideanSpace.single i 1) (gamma a (t, z) k j)
  let lower : Fin n → Fin n → Fin n → ℝ :=
    (∑ β : Fin dS × Fin n, d β • dcoef β) +
      (∑ β : Fin dH, fH a β (t, z) • hcoef β) +
      (∑ β : Fin dA, fA a β (t, z) • acoef β) +
      (∑ β : Fin dS, fS a β (t, z) • scoef β)
  have hselect (v : Fin dS × Fin n → ℝ) (w : Fin dS → ℝ) (i : Fin n) :
      (∑ β : Fin dS × Fin n, v β * (if i = β.2 then w β.1 else 0)) =
        ∑ β : Fin dS, w β * v (β, i) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro β hβ
    simp only [mul_ite, mul_zero, Fintype.sum_ite_eq]
    exact mul_comm _ _
  have hdcoef (i j k : Fin n) : (∑ β : Fin dS × Fin n, d β * dcoef β i j k) =
      -(∑ β : Fin dS, sigma β (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) *
        fderiv ℝ (fun q => fS a β (t, q)) z (EuclideanSpace.single i 1)) -
      (∑ β : Fin dS, sigma β (EuclideanSpace.single k 1) (EuclideanSpace.single i 1) *
        fderiv ℝ (fun q => fS a β (t, q)) z (EuclideanSpace.single j 1)) +
      (∑ β : Fin dS, sigma β (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
        fderiv ℝ (fun q => fS a β (t, q)) z (EuclideanSpace.single k 1)) := by
    simp only [dcoef, mul_add, mul_sub, mul_neg, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [hselect d (fun β => sigma β (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1)) i,
      hselect d (fun β => sigma β (EuclideanSpace.single k 1)
        (EuclideanSpace.single i 1)) j,
      hselect d (fun β => sigma β (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) k]
  have hlower (i j k : Fin n) :
      -C i j k - C j k i + C k i j +
        2 * (F'.connection t).ricci x (Acurve i j t) (E k x) -
        Hmod (GF'.inverse (∑ l : Fin n,
          (-C' i j l - C' j l i + C' l i j) • EuclideanSpace.proj l))
          (EuclideanSpace.single k 1) = lower i j k := by
    rw [hCfull, hCfull, hCfull, hRexpand, hvp_eq, hHexpand]
    simp only [lower, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hdcoef]
    simp only [hcoef, acoef, scoef, mul_add, mul_sub, mul_neg,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    simp only [Finset.mul_sum]
    simp only [mul_left_comm (2 : ℝ), mul_assoc]
    ring
  have hfactor (α : Fin dA) :
      fderiv ℝ (fA a α) (t, z) (1, 0) =
        (∑ β : Fin dS × Fin n, cd a (t, z) α β * d β) +
        (∑ β : Fin dH, ch a (t, z) α β * fH a β (t, z)) +
        (∑ β : Fin dA, ca a (t, z) α β * fA a β (t, z)) +
        (∑ β : Fin dS, cs a (t, z) α β * fS a β (t, z)) := by
    let T : (Fin n → Fin n → Fin n → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := combine a (t, z) α
        map_add' := by
          intro u v
          simp only [combine, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r v
          simp only [combine, Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro k hk
          ring }
    have hcalc : fderiv ℝ (fA a α) (t, z) (1, 0) = T lower := by
      rw [hderiv_coord]
      dsimp only [T, LinearMap.coe_mk, AddHom.coe_mk, combine]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [hAnative]
      simp only [hlower]
      change theta α l j i * (EuclideanSpace.proj l)
        (GF.inverse (∑ k : Fin n, lower i j k • EuclideanSpace.proj k)) = _
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      change theta α l j i *
        (lower i j k * ((gmod F.metric a (t, z)).inverse (EuclideanSpace.proj k)) l) = _
      ring
    rw [hcalc]
    dsimp only [lower]
    simp only [map_add, map_sum, map_smul, smul_eq_mul]
    change (∑ β : Fin dS × Fin n, d β * cd a (t, z) α β) +
      (∑ β : Fin dH, fH a β (t, z) * ch a (t, z) α β) +
      (∑ β : Fin dA, fA a β (t, z) * ca a (t, z) α β) +
      (∑ β : Fin dS, fS a β (t, z) * cs a (t, z) α β) = _
    simp only [mul_comm]
  have hyoung {I D : Type} [Fintype I] [Fintype D]
      (c : I → D → ℝ) (u : I → ℝ) (v : D → ℝ)
      {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
      (hc : (∑ i, ∑ j, (c i j) ^ 2) ≤ B) :
      (∑ i, 2 * u i * (∑ j, c i j * v j)) ≤
        δ * (∑ j, (v j) ^ 2) + (B / δ) * (∑ i, (u i) ^ 2) := by
    let U₂ := ∑ i, (u i) ^ 2
    let V₂ := ∑ j, (v j) ^ 2
    let P := ∑ i, u i * (∑ j, c i j * v j)
    have hU : 0 ≤ U₂ := by dsimp [U₂]; positivity
    have hV : 0 ≤ V₂ := by dsimp [V₂]; positivity
    have hcross : P ^ 2 ≤ U₂ * (∑ i, (∑ j, c i j * v j) ^ 2) := by
      simpa only [mul_comm] using (Finset.sum_mul_sq_le_sq_mul_sq
        (s := Finset.univ) (f := u) (g := fun i => ∑ j, c i j * v j))
    have hcoeff : (∑ i, (∑ j, c i j * v j) ^ 2) ≤ B * V₂ := by
      calc
        _ ≤ ∑ i, (∑ j, (c i j) ^ 2) * V₂ := by
          apply Finset.sum_le_sum
          intro i hi
          simpa only [mul_comm] using (Finset.sum_mul_sq_le_sq_mul_sq
            (s := Finset.univ) (f := c i) (g := v))
        _ = (∑ i, ∑ j, (c i j) ^ 2) * V₂ := by rw [← Finset.sum_mul]
        _ ≤ B * V₂ := mul_le_mul_of_nonneg_right hc hV
    have hP : 2 * P ≤ δ * V₂ + (B / δ) * U₂ := by
      by_cases hV0 : V₂ = 0
      · have hP0 : P = 0 := by
          have hnorm : ∑ i, (∑ j, c i j * v j) ^ 2 = 0 := by
            exact le_antisymm (by simpa [hV0] using hcoeff) (by positivity)
          have hi : ∀ i, ∑ j, c i j * v j = 0 := by
            intro i
            exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
              (s := Finset.univ) (fun i _ => sq_nonneg (∑ j, c i j * v j))).mp hnorm
                i (Finset.mem_univ i))
          simp [P, hi]
        simp only [hV0, hP0, mul_zero, zero_add]
        exact mul_nonneg (div_nonneg hB (le_of_lt hδ)) hU
      · have hVp : 0 < V₂ := lt_of_le_of_ne hV (Ne.symm hV0)
        have hY : 2 * P ≤ δ * V₂ + P ^ 2 / (δ * V₂) := by
          have hh := sq_nonneg (δ * V₂ - P)
          field_simp
          nlinarith
        have hQ : P ^ 2 / (δ * V₂) ≤ (B / δ) * U₂ := by
          apply (div_le_iff₀ (mul_pos hδ hVp)).mpr
          calc
            P ^ 2 ≤ U₂ * (∑ i, (∑ j, c i j * v j) ^ 2) := hcross
            _ ≤ U₂ * (B * V₂) := mul_le_mul_of_nonneg_left hcoeff hU
            _ = (B / δ) * U₂ * (δ * V₂) := by field_simp
        exact hY.trans (by nlinarith)
    simpa [U₂, V₂, P, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hP
  let remCoeff : Fin dA → Fin dH ⊕ (Fin dA ⊕ Fin dS) → ℝ := fun α =>
    Sum.elim (ch a (t, z) α) (Sum.elim (ca a (t, z) α) (cs a (t, z) α))
  let remValue : Fin dH ⊕ (Fin dA ⊕ Fin dS) → ℝ :=
    Sum.elim (fun β => fH a β (t, z))
      (Sum.elim (fun β => fA a β (t, z)) (fun β => fS a β (t, z)))
  have hcoeff := hBbound a ha (show (t, z) ∈ K ×ˢ Q a from ⟨interior_subset ht, hz⟩)
  have hnonnegD : 0 ≤ ∑ α : Fin dA, ∑ β : Fin dS × Fin n, (cd a (t, z) α β) ^ 2 := by
    positivity
  have hnonnegH : 0 ≤ ∑ α : Fin dA, ∑ β : Fin dH, (ch a (t, z) α β) ^ 2 := by
    positivity
  have hnonnegA : 0 ≤ ∑ α : Fin dA, ∑ β : Fin dA, (ca a (t, z) α β) ^ 2 := by
    positivity
  have hnonnegS : 0 ≤ ∑ α : Fin dA, ∑ β : Fin dS, (cs a (t, z) α β) ^ 2 := by
    positivity
  have hcD : (∑ α : Fin dA, ∑ β : Fin dS × Fin n, (cd a (t, z) α β) ^ 2) ≤ B := by
    dsimp only [coeffSq] at hcoeff
    linarith
  have hcR : (∑ α : Fin dA, ∑ β, (remCoeff α β) ^ 2) ≤ B := by
    simp only [remCoeff, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_add_distrib]
    dsimp only [coeffSq] at hcoeff
    linarith
  have hprincipal := hyoung (cd a (t, z)) (fun α => fA a α (t, z)) d hε hB hcD
  have hremainder := hyoung remCoeff (fun α => fA a α (t, z)) remValue
    (δ := 1) (by norm_num) hB hcR
  simp only [remCoeff, remValue, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    one_mul, div_one, ← add_assoc] at hremainder
  have hrateSum : (∑ α : Fin dA, 2 * fA a α (t, z) *
      fderiv ℝ (fA a α) (t, z) (1, 0)) =
      (∑ α : Fin dA, 2 * fA a α (t, z) *
        (∑ β : Fin dS × Fin n, cd a (t, z) α β * d β)) +
      (∑ α : Fin dA, 2 * fA a α (t, z) *
        ((∑ β : Fin dH, ch a (t, z) α β * fH a β (t, z)) +
          (∑ β : Fin dA, ca a (t, z) α β * fA a β (t, z)) +
          (∑ β : Fin dS, cs a (t, z) α β * fS a β (t, z)))) := by
    simp only [hfactor, mul_add, Finset.sum_add_distrib]
    ring
  have hH0 : 0 ≤ ∑ β : Fin dH, (fH a β (t, z)) ^ 2 := by positivity
  have hA0 : 0 ≤ ∑ β : Fin dA, (fA a β (t, z)) ^ 2 := by positivity
  have hS0 : 0 ≤ ∑ β : Fin dS, (fS a β (t, z)) ^ 2 := by positivity
  have hden : (∑ β : Fin dA, (fA a β (t, z)) ^ 2) ≤
      (∑ β : Fin dH, (fH a β (t, z)) ^ 2) +
        (∑ β : Fin dA, (fA a β (t, z)) ^ 2) +
        (∑ β : Fin dS, (fS a β (t, z)) ^ 2) := by linarith
  have hdens0 : 0 ≤ (∑ β : Fin dH, (fH a β (t, z)) ^ 2) +
      (∑ β : Fin dA, (fA a β (t, z)) ^ 2) +
      (∑ β : Fin dS, (fS a β (t, z)) ^ 2) := by positivity
  have hpbound := mul_le_mul (div_le_div_of_nonneg_right
      (show B ≤ B + 1 by linarith) (le_of_lt hε)) hden hA0
    (by positivity : 0 ≤ (B + 1) / ε)
  have hrbound := mul_le_mul_of_nonneg_left hden hB
  change (∑ α : Fin dA, 2 * fA a α (t, z) *
      fderiv ℝ (fA a α) (t, z) (1, 0)) ≤
    ε * (∑ β : Fin dS, ∑ j : Fin n,
      (fderiv ℝ (fun q => fS a β (t, q)) z (EuclideanSpace.single j 1)) ^ 2) +
      ((B + 1) / ε + (B + 1)) *
        ((∑ β : Fin dH, (fH a β (t, z)) ^ 2) +
          (∑ β : Fin dA, (fA a β (t, z)) ^ 2) +
          (∑ β : Fin dS, (fS a β (t, z)) ^ 2))
  rw [hrateSum]
  have hgrad : (∑ β : Fin dS × Fin n, (d β) ^ 2) =
      ∑ β : Fin dS, ∑ j : Fin n,
        (fderiv ℝ (fun q => fS a β (t, q)) z (EuclideanSpace.single j 1)) ^ 2 := by
    simp only [d, Fintype.sum_prod_type]
  rw [hgrad] at hprincipal
  nlinarith only [hprincipal, hremainder, hpbound, hrbound]

end PoincareConjecture.Proofs.M03
