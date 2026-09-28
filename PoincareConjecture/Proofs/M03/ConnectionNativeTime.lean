import PoincareConjecture.Proofs.M03.MetricInverse
import PoincareConjecture.Proofs.M03.CurvatureTrace
import PoincareConjecture.Proofs.M03.ScalarMixedDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope













set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set Filter

namespace PoincareConjecture.Proofs.M03

theorem coordinate_covector_reconstruction
    {n : Nat} (l : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
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
    l v = l (∑ i : Fin n, v i • EuclideanSpace.single i 1) :=
      congrArg l (hv v)
    _ = (∑ i : Fin n,
      (l (EuclideanSpace.single i 1)) • EuclideanSpace.proj i) v := by
      simp only [map_sum, map_smul]
      simp [EuclideanSpace.proj, mul_comm]

theorem inverse_bilinear_reconstruct
    {n : Nat}
    {G : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hG : G.IsInvertible) (v : EuclideanSpace ℝ (Fin n)) :
    G.inverse (∑ i : Fin n,
      (G v (EuclideanSpace.single i 1)) • EuclideanSpace.proj i) = v := by
  have hc := coordinate_covector_reconstruction (G v)
  rw [← hc]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) => L v) hG.inverse_comp_self

theorem native_derivative_of_lowered_pairings
    {n : Nat}
    {G : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hG : G.IsInvertible) (dv : EuclideanSpace ℝ (Fin n))
    (p : Fin n -> ℝ)
    (hp : ∀ i : Fin n,
      G dv (EuclideanSpace.single i 1) = p i) :
    dv = G.inverse (∑ i : Fin n, p i • EuclideanSpace.proj i) := by
  calc
    dv = G.inverse (∑ i : Fin n,
        (G dv (EuclideanSpace.single i 1)) • EuclideanSpace.proj i) :=
      (inverse_bilinear_reconstruct hG dv).symm
    _ = G.inverse (∑ i : Fin n, p i • EuclideanSpace.proj i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hp i]

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxRecDepth 2000 in
theorem ricciFlow_curvature_derivative_energy_terminal_bound
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T C a : ℝ} (_hT : 0 < T) (F : RicciFlow n M (Ico 0 T))
    (hC : ∀ s ∈ Ico 0 T, ∀ x : M, (F.connection s).curvatureTensorNorm x ≤ C)
    (ha : 0 < a) (haT : a < T) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let N := fun s (P A : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).connection A y (P y)
    let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).curvatureOnFields A B C y
    let K := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N s P (R s A B C) y - R s (N s P A) B C y -
        R s A (N s P B) C y - R s A B (N s P C) y
    let Q := fun s x =>
      let b := (F.metric s).orthonormalBasis x
      let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
      let k := fun γ : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        K s (E (γ 0)) (E (γ 1)) (E (γ 2)) (E (γ 3)) x
      ∑ γ, (F.metric s).inner x (k γ) (k γ)
    let L := 96 * ((n : ℝ) + 1) ^ 3 * max C 0
    ∃ Qa : ℝ, 0 ≤ Qa ∧ (∀ x : M, Q a x ≤ Qa) ∧
      (∀ s ∈ Ico a T, ∀ x : M, Q s x ≤ Qa * Real.exp (L * (s - a))) ∧
      (∀ s ∈ Ico a T, ∀ x : M, Q s x ≤ Qa * Real.exp (L * (T - a))) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ :=
    { contMDiff_mul := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact contDiff_mul.contMDiff }
  let V := EuclideanSpace ℝ (Fin n)
  let N := fun s (P A : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection A y (P y)
  let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).curvatureOnFields A B C y
  let K := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N s P (R s A B C) y - R s (N s P A) B C y -
      R s A (N s P B) C y - R s A B (N s P C) y
  let Q := fun s x =>
    let b := (F.metric s).orthonormalBasis x
    let E := fun i => FiberBundle.extend V (b i)
    let k := fun γ : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      K s (E (γ 0)) (E (γ 1)) (E (γ 2)) (E (γ 3)) x
    ∑ γ, (F.metric s).inner x (k γ) (k γ)
  let L := 96 * ((n : ℝ) + 1) ^ 3 * max C 0
  change ∃ Qa : ℝ, 0 ≤ Qa ∧ (∀ x : M, Q a x ≤ Qa) ∧
    (∀ s ∈ Ico a T, ∀ x : M, Q s x ≤ Qa * Real.exp (L * (s - a))) ∧
    (∀ s ∈ Ico a T, ∀ x : M, Q s x ≤ Qa * Real.exp (L * (T - a)))
  have hQnonneg (s : ℝ) (x : M) : 0 ≤ Q s x := by
    apply Finset.sum_nonneg
    intro γ _
    let v := K s
      (FiberBundle.extend V ((F.metric s).orthonormalBasis x (γ 0)))
      (FiberBundle.extend V ((F.metric s).orthonormalBasis x (γ 1)))
      (FiberBundle.extend V ((F.metric s).orthonormalBasis x (γ 2)))
      (FiberBundle.extend V ((F.metric s).orthonormalBasis x (γ 3))) x
    change 0 ≤ (F.metric s).inner x v v
    by_cases hv : v = 0
    · simp [hv]
    · exact ((F.metric s).pos x v hv).le
  let e := fun x0 : M => trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := fun x0 : M => (e x0).localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun (x0 : M) (s : ℝ) (y : M) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y ((F.metric s).inner y)
  let ai := fun (x0 : M) (s : ℝ) (y : M) (i j : Fin n) =>
    ((G x0 s y).inverse (EuclideanSpace.proj j)) i
  let k := fun (x0 : M) s (α : Fin 4 → Fin n) =>
    K s (E x0 (α 0)) (E x0 (α 1)) (E x0 (α 2)) (E x0 (α 3))
  let q := fun (x0 : M) s y => ∑ α : Fin 4 → Fin n, ∑ β : Fin 4 → Fin n,
    (∏ r, ai x0 s y (α r) (β r)) * (F.metric s).inner y (k x0 s α y) (k x0 s β y)
  have hqQ (x0 : M) (s : ℝ) {x : M} (hx : x ∈ (e x0).baseSet) :
      q x0 s x = Q s x :=
    curvature_derivative_squared_norm_frame_eq_orthonormal (F.connection s) x0 hx
  have hlocal (x0 : M) : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => q x0 p.1 p.2) (Ico 0 T ×ˢ (e x0).baseSet) := by
    let U := (e x0).baseSet
    let S := fun X : (y : M) → TangentSpace (𝓡 n) y =>
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% X) U
    let B := fun X : ℝ → (y : M) → TangentSpace (𝓡 n) y =>
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (fun p : ℝ × M => Bundle.TotalSpace.mk' V p.2 (X p.1 p.2)) (Ico 0 T ×ˢ U)
    have hU : IsOpen U := (e x0).open_baseSet
    have hE (i : Fin n) : S (E x0 i) :=
      (e x0).contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis i
    have hfixed (X : (y : M) → TangentSpace (𝓡 n) y) (hX : S X) : B (fun _ => X) :=
      hX.comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd (fun _ hp => hp.2)
    have hslice (X : ℝ → (y : M) → TangentSpace (𝓡 n) y) (hX : B X)
        (s : ℝ) (hs : s ∈ Ico 0 T) : S (X s) :=
      hX.comp (contMDiffOn_const.prodMk contMDiffOn_id) (fun _ hy => ⟨hs, hy⟩)
    have hpair {U' : Set M}
        (X Y : ℝ → (y : M) → TangentSpace (𝓡 n) y)
        (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
          (fun p : ℝ × M => Bundle.TotalSpace.mk' V p.2 (X p.1 p.2)) (Ico 0 T ×ˢ U'))
        (hY : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
          (fun p : ℝ × M => Bundle.TotalSpace.mk' V p.2 (Y p.1 p.2)) (Ico 0 T ×ˢ U')) :
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => (F.metric p.1).inner p.2 (X p.1 p.2) (Y p.1 p.2))
          (Ico 0 T ×ˢ U') := by
      have hp := ContMDiffOn.clm_bundle_apply₂
        (F₁ := V) (F₂ := V) (F₃ := ℝ)
        (E₁ := fun y : M => TangentSpace (𝓡 n) y)
        (E₂ := fun y : M => TangentSpace (𝓡 n) y) (E₃ := fun _ : M => ℝ)
        (ψ := fun p : ℝ × M => (F.metric p.1).inner p.2) (b := Prod.snd)
        (F.smooth.mono (Set.prod_mono subset_rfl (subset_univ U'))) hX hY
      intro p hpS
      exact (Bundle.contMDiffWithinAt_totalSpace.mp (hp p hpS)).2
    have hNmoving (P : (y : M) → TangentSpace (𝓡 n) y) (hP : S P)
        (X : ℝ → (y : M) → TangentSpace (𝓡 n) y) (hX : B X) :
        B (fun s => N s P (X s)) := by
      apply contMDiffOn_family_vector_of_metric_pair F.smooth hU
      intro U' hU' hU'U W hW
      have hX' := hX.mono (Set.prod_mono subset_rfl hU'U)
      have hW' := hW.comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
        (fun (p : ℝ × M) (hp : p ∈ Ico 0 T ×ˢ U') => hp.2)
      have hNW := contMDiffOn_connection_family_apply F.smooth F.connection
        hU' W P hW (hP.mono hU'U)
      have hd := contMDiffOn_family_spatial_mvfderiv
        (f := fun s y => (F.metric s).inner y (X s y) (W y)) hU'
        (hpair X (fun _ => W) hX' hW') P (hP.mono hU'U)
      apply (hd.sub (hpair X (fun s => N s P W) hX' hNW)).congr
      intro p hp
      have hXp := ((hslice X hX p.1 hp.1).contMDiffAt
        (hU.mem_nhds (hU'U hp.2))).mdifferentiableAt (by simp)
      have hWp := (hW.contMDiffAt (hU'.mem_nhds hp.2)).mdifferentiableAt (by simp)
      rw [(F.connection p.1).mvfderiv_inner P (X p.1) W hXp hWp]
      dsimp only [N]
      ring
    let : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
    let : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
    let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
    let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
    obtain ⟨Rc, hRc, hRcs⟩ :=
      exists_contMDiffOn_curvature_family_trilinearMap F.smooth F.connection
    have hRmoving (X Y Z : ℝ → (y : M) → TangentSpace (𝓡 n) y)
        (hX : B X) (hY : B Y) (hZ : B Z) : B (fun s => R s (X s) (Y s) (Z s)) := by
      have hRc' := hRcs.mono (Set.prod_mono subset_rfl (subset_univ U))
      have h1 := ContMDiffOn.clm_bundle_apply
        (F₁ := V) (F₂ := V →L[ℝ] V →L[ℝ] V)
        (E₁ := fun y : M => TangentSpace (𝓡 n) y)
        (E₂ := fun y : M => TangentSpace (𝓡 n) y →L[ℝ]
          TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        (b := Prod.snd) hRc' hX
      have h2 := ContMDiffOn.clm_bundle_apply
        (F₁ := V) (F₂ := V →L[ℝ] V)
        (E₁ := fun y : M => TangentSpace (𝓡 n) y)
        (E₂ := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        (b := Prod.snd) h1 hY
      have h3 := ContMDiffOn.clm_bundle_apply
        (F₁ := V) (F₂ := V)
        (E₁ := fun y : M => TangentSpace (𝓡 n) y)
        (E₂ := fun y : M => TangentSpace (𝓡 n) y)
        (b := Prod.snd) h2 hZ
      apply h3.congr
      intro p hp
      congr 1
      exact (curvature_eq_curvatureOnFields (F.connection p.1) hU
        (X p.1) (Y p.1) (Z p.1) (hslice X hX p.1 hp.1)
        (hslice Y hY p.1 hp.1) (hslice Z hZ p.1 hp.1) hp.2).symm.trans
          (hRc p.1 p.2 (X p.1 p.2) (Y p.1 p.2) (Z p.1 p.2)).symm
    have hNk (i j : Fin n) : B (fun s => N s (E x0 i) (E x0 j)) :=
      hNmoving (E x0 i) (hE i) (fun _ => E x0 j) (hfixed (E x0 j) (hE j))
    have hsub (X Y : ℝ → (y : M) → TangentSpace (𝓡 n) y)
        (hX : B X) (hY : B Y) : B (fun s y => X s y - Y s y) := by
      apply contMDiffOn_family_vector_of_metric_pair F.smooth hU
      intro U' hU' hU'U W hW
      have hW' := hW.comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
        (fun (p : ℝ × M) (hp : p ∈ Ico 0 T ×ˢ U') => hp.2)
      apply ((hpair X (fun _ => W) (hX.mono (Set.prod_mono subset_rfl hU'U)) hW').sub
        (hpair Y (fun _ => W) (hY.mono (Set.prod_mono subset_rfl hU'U)) hW')).congr
      intro p _
      change (F.metric p.1).inner p.2 (X p.1 p.2 - Y p.1 p.2) (W p.2) = _
      rw [map_sub, sub_apply]
    have hk (α : Fin 4 → Fin n) : B (fun s => k x0 s α) := by
      let A0 := fun s => N s (E x0 (α 0))
        (R s (E x0 (α 1)) (E x0 (α 2)) (E x0 (α 3)))
      let A1 := fun s => R s (N s (E x0 (α 0)) (E x0 (α 1)))
        (E x0 (α 2)) (E x0 (α 3))
      let A2 := fun s => R s (E x0 (α 1))
        (N s (E x0 (α 0)) (E x0 (α 2))) (E x0 (α 3))
      let A3 := fun s => R s (E x0 (α 1)) (E x0 (α 2))
        (N s (E x0 (α 0)) (E x0 (α 3)))
      have h0 : B A0 := hNmoving (E x0 (α 0)) (hE (α 0))
        (fun s => R s (E x0 (α 1)) (E x0 (α 2)) (E x0 (α 3)))
        (hRmoving (fun _ => E x0 (α 1)) (fun _ => E x0 (α 2)) (fun _ => E x0 (α 3))
          (hfixed (E x0 (α 1)) (hE (α 1))) (hfixed (E x0 (α 2)) (hE (α 2)))
          (hfixed (E x0 (α 3)) (hE (α 3))))
      have h1 : B A1 := hRmoving
        (fun s => N s (E x0 (α 0)) (E x0 (α 1)))
        (fun _ => E x0 (α 2)) (fun _ => E x0 (α 3))
        (hNk (α 0) (α 1)) (hfixed (E x0 (α 2)) (hE (α 2)))
        (hfixed (E x0 (α 3)) (hE (α 3)))
      have h2 : B A2 := hRmoving (fun _ => E x0 (α 1))
        (fun s => N s (E x0 (α 0)) (E x0 (α 2))) (fun _ => E x0 (α 3))
        (hfixed (E x0 (α 1)) (hE (α 1))) (hNk (α 0) (α 2))
        (hfixed (E x0 (α 3)) (hE (α 3)))
      have h3 : B A3 := hRmoving (fun _ => E x0 (α 1)) (fun _ => E x0 (α 2))
        (fun s => N s (E x0 (α 0)) (E x0 (α 3)))
        (hfixed (E x0 (α 1)) (hE (α 1))) (hfixed (E x0 (α 2)) (hE (α 2)))
        (hNk (α 0) (α 3))
      exact hsub (fun s y => A0 s y - A1 s y - A2 s y) A3
        (hsub (fun s y => A0 s y - A1 s y) A2 (hsub A0 A1 h0 h1) h2) h3
    have hinv := (contMDiffOn_family_metric_frame_inverse F.smooth x0).2.2
    have hai (i j : Fin n) : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => ai x0 p.1 p.2 i j) (Ico 0 T ×ˢ U) :=
      (contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply
        (hinv.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
    apply contMDiffOn_finsetSum
    intro α _
    apply contMDiffOn_finsetSum
    intro β _
    exact (contMDiffOn_finsetProd (fun r _ => hai (α r) (β r))).mul
      (hpair (fun s => k x0 s α) (fun s => k x0 s β) (hk α) (hk β))
  have hQsm (s : ℝ) (hs : s ∈ Ioo 0 T) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Q p.1 p.2) (s, x) := by
    have hx : x ∈ (e x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    have htime : Ico 0 T ∈ 𝓝 s := Ico_mem_nhds_iff.mpr hs
    have hdom : Ico 0 T ×ˢ (e x).baseSet ∈ 𝓝 (s, x) :=
      prod_mem_nhds htime ((e x).open_baseSet.mem_nhds hx)
    apply ((hlocal x).contMDiffAt hdom).congr_of_eventuallyEq
    filter_upwards [hdom] with p hp
    exact (hqQ x p.1 hp.2).symm
  have hQslice (s : ℝ) (hs : s ∈ Ioo 0 T) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (Q s) := by
    intro x
    exact (hQsm s hs x).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  have hQderiv (s : ℝ) (hs : s ∈ Ioo 0 T) (x : M) :
      HasDerivAt (fun r => Q r x) (deriv (fun r => Q r x) s) s := by
    have hh : ContDiffAt ℝ ∞ (fun r => Q r x) s :=
      ((hQsm s hs x).comp s (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt
    exact (hh.differentiableAt (by simp)).hasDerivAt
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hmaxrate (s : ℝ) (hs : s ∈ Ioo 0 T) (x : M)
      (hmax : IsLocalMax (Q s) x) :
      deriv (fun r => Q r x) s ≤ L * Q s x := by
    have hx : x ∈ (e x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    have hsq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q x s) (e x).baseSet := by
      have hmap : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
          (fun y : M => (s, y)) (e x).baseSet :=
        contMDiffOn_const.prodMk contMDiffOn_id
      have hsall := (hlocal x).comp (f := fun y : M => (s, y)) hmap
        (fun _ hy => ⟨⟨hs.1.le, hs.2⟩, hy⟩)
      exact hsall
    have heq : q x s =ᶠ[𝓝 x] Q s := by
      filter_upwards [(e x).open_baseSet.mem_nhds hx] with y hy
      exact hqQ x s hy
    have hqmax : IsLocalMax (q x s) x := heq.isLocalMax_iff.mpr hmax
    let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
      mvfderiv (𝓡 n) f y (P y)
    let lap := ∑ i, ∑ j, ai x s x i j *
      (d (E x i) (d (E x j) (q x s)) x - d (N s (E x i) (E x j)) (q x s) x)
    have hlap : lap ≤ 0 :=
      scalar_frame_laplacian_nonpos_of_isLocalMax (F.connection s) x hx
        (q x s) hsq hqmax
    have hsi : s ∈ interior (Ico 0 T) := by simpa only [interior_Ico] using hs
    have hheat := ricciFlow_curvature_derivative_scalar_heat_le F hsi x hx
    have hheat0 := hheat.1
    have hineq := hheat.2
    change deriv (fun r => q x r x) s - lap ≤
      -2 * _ + 96 * ((n : ℝ) + 1) ^ 3 * (F.connection s).curvatureTensorNorm x * q x s x
      at hineq
    have htime : (fun r => q x r x) = (fun r => Q r x) :=
      funext (fun r => hqQ x r hx)
    rw [htime, hqQ x s hx] at hineq
    have hcurv : (F.connection s).curvatureTensorNorm x ≤ max C 0 :=
      (hC s ⟨hs.1.le, hs.2⟩ x).trans (le_max_left _ _)
    have hcoef := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcurv
        (by positivity : 0 ≤ 96 * ((n : ℝ) + 1) ^ 3)) (hQnonneg s x)
    change 96 * ((n : ℝ) + 1) ^ 3 * (F.connection s).curvatureTensorNorm x * Q s x ≤
      L * Q s x at hcoef
    linarith only [hineq, hheat0, hlap, hcoef]
  cases isEmpty_or_nonempty M with
  | inl hM =>
    let : IsEmpty M := hM
    exact ⟨0, le_rfl, fun x => isEmptyElim x,
      fun _ _ x => isEmptyElim x, fun _ _ x => isEmptyElim x⟩
  | inr hM =>
    let : Nonempty M := hM
    obtain ⟨xa, _, hma⟩ := isCompact_univ.exists_isMaxOn
      (univ_nonempty : (univ : Set M).Nonempty) (hQslice a ⟨ha, haT⟩).continuous.continuousOn
    let Qa := Q a xa
    have hQa : 0 ≤ Qa := hQnonneg a xa
    have hQaBound (x : M) : Q a x ≤ Qa := isMaxOn_iff.mp hma x (mem_univ x)
    have hgrowth (b : ℝ) (hb : b ∈ Ico a T) (x : M) :
        Q b x ≤ Qa * Real.exp (L * (b - a)) := by
      rcases eq_or_lt_of_le hb.1 with hab | hab
      · subst b
        simpa only [sub_self, mul_zero, Real.exp_zero, mul_one] using hQaBound x
      let v := fun (s : ℝ) (y : M) => Real.exp (-L * (s - a)) * Q s y
      have hv : v b x ≤ Qa := by
        by_contra hnot
        have hgap : Qa < v b x := lt_of_not_ge hnot
        let ε := (v b x - Qa) / (2 * (b - a))
        have heps : 0 < ε := div_pos (sub_pos.mpr hgap) (by linarith)
        have hepsmul : 2 * (ε * (b - a)) = v b x - Qa := by
          dsimp only [ε]
          field_simp [ne_of_gt (sub_pos.mpr hab)]
        let w := fun p : ℝ × M => v p.1 p.2 - ε * (p.1 - a)
        let slab := Icc a b ×ˢ (univ : Set M)
        have hwgt : Qa < w (b, x) := by
          change Qa < v b x - ε * (b - a)
          linarith only [hepsmul, hgap]
        have hQcont : ContinuousOn (fun p : ℝ × M => Q p.1 p.2) slab := by
          intro p hp
          exact (hQsm p.1 ⟨ha.trans_le hp.1.1, hp.1.2.trans_lt hb.2⟩
            p.2).continuousAt.continuousWithinAt
        have hecont : Continuous (fun p : ℝ × M => Real.exp (-L * (p.1 - a))) := by
          fun_prop
        have helin : Continuous (fun p : ℝ × M => ε * (p.1 - a)) := by fun_prop
        have hwcont : ContinuousOn w slab :=
          (hecont.continuousOn.mul hQcont).sub helin.continuousOn
        have hslab : IsCompact slab := isCompact_Icc.prod isCompact_univ
        have hbx : (b, x) ∈ slab := ⟨⟨hab.le, le_rfl⟩, mem_univ x⟩
        obtain ⟨p, hp, hmax⟩ := hslab.exists_isMaxOn ⟨(b, x), hbx⟩ hwcont
        have hpgt : Qa < w p := hwgt.trans_le (isMaxOn_iff.mp hmax (b, x) hbx)
        have hpa : a < p.1 := by
          apply lt_of_le_of_ne hp.1.1
          intro heq
          have hwa : w p = Q a p.2 := by
            dsimp only [w, v]
            rw [← heq]
            simp only [sub_self, mul_zero, Real.exp_zero, one_mul, sub_zero]
          rw [hwa] at hpgt
          exact (not_lt_of_ge (hQaBound p.2)) hpgt
        have hpt : p.1 ∈ Ioo 0 T := ⟨ha.trans hpa, hp.1.2.trans_lt hb.2⟩
        have hQmax : IsLocalMax (Q p.1) p.2 := by
          apply Filter.Eventually.of_forall
          intro y
          have hh := isMaxOn_iff.mp hmax (p.1, y) ⟨hp.1, mem_univ y⟩
          change Real.exp (-L * (p.1 - a)) * Q p.1 y - ε * (p.1 - a) ≤
            Real.exp (-L * (p.1 - a)) * Q p.1 p.2 - ε * (p.1 - a) at hh
          exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp ((sub_le_sub_iff_right _).mp hh)
        let rate := Real.exp (-L * (p.1 - a)) *
          (deriv (fun r => Q r p.2) p.1 - L * Q p.1 p.2) - ε
        have hwd : HasDerivAt (fun r => w (r, p.2)) rate p.1 := by
          have he := (((hasDerivAt_id p.1).sub_const a).const_mul (-L)).exp
          have hl := ((hasDerivAt_id p.1).sub_const a).const_mul ε
          convert (he.mul (hQderiv p.1 hpt p.2)).sub hl using 1
          · rfl
          · rfl
          · rfl
          · dsimp only [rate, id_eq]
            ring
        have hrateNonneg : 0 ≤ rate := by
          apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hwd).1
          filter_upwards [Ico_mem_nhdsLT hpa] with r hr
          have hh := isMaxOn_iff.mp hmax (r, p.2)
            ⟨⟨hr.1, hr.2.le.trans hp.1.2⟩, mem_univ p.2⟩
          rw [slope_def_field]
          exact div_nonneg_of_nonpos (sub_nonpos.mpr hh) (sub_nonpos.mpr hr.2.le)
        have hrateNeg : rate < 0 := by
          have hh := hmaxrate p.1 hpt p.2 hQmax
          have hm := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-L * (p.1 - a))).le
            (sub_nonpos.mpr hh)
          dsimp only [rate]
          linarith only [hm, heps]
        exact (not_lt_of_ge hrateNonneg) hrateNeg
      calc
        Q b x = Real.exp (L * (b - a)) * v b x := by
          dsimp only [v]
          rw [← mul_assoc, ← Real.exp_add]
          have he : L * (b - a) + -L * (b - a) = 0 := by ring
          rw [he, Real.exp_zero, one_mul]
        _ ≤ Real.exp (L * (b - a)) * Qa :=
          mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
        _ = Qa * Real.exp (L * (b - a)) := mul_comm _ _
    refine ⟨Qa, hQa, hQaBound, hgrowth, ?_⟩
    intro s hs x
    exact (hgrowth s hs x).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2.le a) hL)) hQa)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem hasDerivAt_ricciFlow_iteratedCurvature_zero
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) (X : Fin 3 → (y : M) → TangentSpace (𝓡 n) y)
    (hX : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j))
        (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x0).baseSet)
    {x : M} (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let D := F.connection t
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x ((F.metric t).inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let R := D.curvature x
    let u := X 0 x
    let v := X 1 x
    let w := X 2 x
    let Z := fun r s : TangentSpace (𝓡 n) x =>
      R (R u v r) s w - (2 : ℝ) • R v r (R s u w) +
        (2 : ℝ) • R r u (R v s w) + R (R u v w) r s -
        R (R u r s) v w - R u (R v r s) w - R u v (R w r s)
    HasDerivAt
      (fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s) 0 X x)
      ((∑ i : Fin n, ∑ j : Fin n, a i j •
        curvatureOnFields_iteratedCovariantDerivative D 2
          (Fin.cons (E i) (Fin.cons (E j) X)) x) +
        ∑ i : Fin n, ∑ j : Fin n, a i j • Z (E i x) (E j x)) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let D := F.connection t
  let g := F.metric t
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  let u := X 0 x
  let v := X 1 x
  let w := X 2 x
  let b := g.orthonormalBasis x
  let ext := fun z : TangentSpace (𝓡 n) x => FiberBundle.extend V z
  let eb := fun r => ext (b r)
  let ex := trivializationAt V (TangentSpace (𝓡 n)) x
  have hxx : x ∈ ex.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let S := fun (U : Set M) (A : (y : M) → TangentSpace (𝓡 n) y) =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% A) U
  have hE (i : Fin n) : S e.baseSet (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hExt (z : TangentSpace (𝓡 n) x) : S ex.baseSet (ext z) := by
    suffices hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (ex ⟨y, ext z y⟩).2) ex.baseSet by
      intro y hy
      rw [ex.contMDiffWithinAt_section _ hy]
      exact hh y hy
    apply (contMDiffOn_const (c := (ex ⟨x, z⟩).2)).congr
    intro y hy
    change (ex ⟨y, ex.symm y (ex ⟨x, z⟩).2⟩).2 = (ex ⟨x, z⟩).2
    have hh := congrArg Prod.snd (ex.apply_mk_symm hy (ex ⟨x, z⟩).2)
    exact hh
  have hExtx (z : TangentSpace (𝓡 n) x) : ext z x = z :=
    FiberBundle.extend_apply_self _ _
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y => D.connection B y (A y)
  let Rf := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (Rf A B C) y - Rf (N P A) B C y -
      Rf A (N P B) C y - Rf A B (N P C) y
  let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (K Q A B C) y - K (N P Q) A B C y -
      K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
  have hK (Y : Fin 4 → (y : M) → TangentSpace (𝓡 n) y) :
      curvatureOnFields_iteratedCovariantDerivative D 1 Y =
        K (Y 0) (Y 1) (Y 2) (Y 3) := by
    funext y
    simp [curvatureOnFields_iteratedCovariantDerivative, Fin.sum_univ_succ,
      Fin.tail, K, N, Rf, sub_add_eq_sub_sub]
  have hH (Y : Fin 5 → (y : M) → TangentSpace (𝓡 n) y) :
      curvatureOnFields_iteratedCovariantDerivative D 2 Y =
        H (Y 0) (Y 1) (Y 2) (Y 3) (Y 4) := by
    funext y
    rw [curvatureOnFields_iteratedCovariantDerivative]
    simp only [hK]
    simp [Fin.sum_univ_succ, Fin.tail, H, N, sub_add_eq_sub_sub]
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D 2 x
  have hleft (r) :
      H (eb r) (eb r) (ext u) (ext v) (ext w) x = T ![b r, b r, u, v, w] := by
    have hh := hT ex.open_baseSet ![eb r, eb r, ext u, ext v, ext w]
      (by intro j; fin_cases j <;> exact hExt _) hxx
    rw [hH] at hh
    change T (fun j => ![eb r, eb r, ext u, ext v, ext w] j x) =
      H (eb r) (eb r) (ext u) (ext v) (ext w) x at hh
    rw [← hh]
    congr 1
    funext j
    fin_cases j <;> exact hExtx _
  have hright (i j : Fin n) :
      T ![E i x, E j x, u, v, w] =
        curvatureOnFields_iteratedCovariantDerivative D 2 (Fin.cons (E i) (Fin.cons (E j) X)) x := by
    have hh := hT e.open_baseSet (Fin.cons (E i) (Fin.cons (E j) X))
      (by intro r; refine Fin.cases (hE i) ?_ r
          intro r; refine Fin.cases (hE j) ?_ r
          exact hX) hx
    convert hh using 1
    congr 1
    ext r
    fin_cases r <;> rfl
  have hframe (z : TangentSpace (𝓡 n) x) :
      z = ∑ i : Fin n, theta i x z • E i x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V z) hx
  have hgram (i j : Fin n) :
      a i j = ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hsecond (p q : TangentSpace (𝓡 n) x) :
      T ![p, q, u, v, w] =
        ∑ j : Fin n, theta j x q • T ![p, E j x, u, v, w] := by
    change (T.curryLeft p).curryLeft q ![u, v, w] = _
    nth_rw 1 [hframe q]
    simp only [map_sum, map_smul, sum_apply, smul_apply, MultilinearMap.curryLeft_apply]
    rfl
  have hexpand (p q : TangentSpace (𝓡 n) x) :
      T ![p, q, u, v, w] =
        ∑ i : Fin n, ∑ j : Fin n,
          (theta i x p * theta j x q) • T ![E i x, E j x, u, v, w] := by
    change T.curryLeft p ![q, u, v, w] = _
    nth_rw 1 [hframe p]
    simp only [map_sum, map_smul, sum_apply, smul_apply, MultilinearMap.curryLeft_apply]
    change (∑ i, theta i x p • T ![E i x, q, u, v, w]) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [hsecond]
    simp only [Finset.smul_sum, smul_smul]
  have htrace :
      (∑ r, H (eb r) (eb r) (ext u) (ext v) (ext w) x) =
        ∑ i : Fin n, ∑ j : Fin n, a i j •
          curvatureOnFields_iteratedCovariantDerivative D 2
            (Fin.cons (E i) (Fin.cons (E j) X)) x := by
    have hs : (∑ r, H (eb r) (eb r) (ext u) (ext v) (ext w) x) =
        ∑ r, ∑ i : Fin n, ∑ j : Fin n,
          (theta i x (b r) * theta j x (b r)) • T ![E i x, E j x, u, v, w] := by
      apply Finset.sum_congr rfl
      intro r _
      exact (hleft r).trans (hexpand _ _)
    rw [hs]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_smul, ← hgram, hright]
  let R := D.curvature x
  let P := fun z : TangentSpace (𝓡 n) x => ∑ r, D.ricci x z (b r) • b r
  let Q := (∑ r, (R (R u v (b r)) (b r) w -
      (2 : ℝ) • R v (b r) (R (b r) u w) +
      (2 : ℝ) • R (b r) u (R v (b r) w))) +
    P (R u v w) - R (P u) v w - R u (P v) w - R u v (P w)
  let Z := fun r s : TangentSpace (𝓡 n) x =>
    R (R u v r) s w - (2 : ℝ) • R v r (R s u w) +
      (2 : ℝ) • R r u (R v s w) + R (R u v w) r s -
      R (R u r s) v w - R u (R v r s) w - R u v (R w r s)
  have hreact := curvature_reaction_eq_pure_inverse_frame_sum D x0 x hx u v w
  change Q = ∑ i : Fin n, ∑ j : Fin n, a i j • Z (E i x) (E j x) at hreact
  have htime := hasDerivAt_ricciFlow_curvature_diffusion_reaction F ht x u v w
  change HasDerivAt (fun s => (F.connection s).curvature x u v w)
    ((∑ r, H (eb r) (eb r) (ext u) (ext v) (ext w) x) + Q) t at htime
  rw [htrace, hreact] at htime
  apply htime.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun s =>
    (curvature_eq_curvatureOnFields (F.connection s) e.open_baseSet
      (X 0) (X 1) (X 2) (hX 0) (hX 1) (hX 2) hx).symm

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_connection_variation_pairing_eq_inverse_frame
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let g := F.metric t
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let K := curvatureOnFields_iteratedCovariantDerivative (F.connection t)
    let low := fun (Z : Fin 5 → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (K 1 (Fin.init Z) y) (Z (Fin.last 4) y)
    ∀ (X Y Z : (y : M) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% X) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Y) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Z) e.baseSet →
      ∀ {x : M}, x ∈ e.baseSet →
      g.inner x (deriv (fun s => (F.connection s).connection Y x (X x)) t) (Z x) =
        -(∑ i, ∑ j, a x i j * low ![X, E i, Y, Z, E j] x) -
          (∑ i, ∑ j, a x i j * low ![Y, E i, Z, X, E j] x) +
          ∑ i, ∑ j, a x i j * low ![Z, E i, X, Y, E j] x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let g := F.metric t
  let D := F.connection t
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
    x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let low := fun (Z : Fin 5 → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K 1 (Fin.init Z) y) (Z (Fin.last 4) y)
  intro X Y Z hX hY hZ x hx
  let b := g.orthonormalBasis x
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let eb := fun i : ι => FiberBundle.extend V (b i)
  let ex := trivializationAt V (TangentSpace (𝓡 n)) x
  let U := e.baseSet ∩ ex.baseSet
  have hU : IsOpen U := e.open_baseSet.inter ex.open_baseSet
  have hxU : x ∈ U := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let S := fun Q : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Q) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have heb (i : ι) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
      (T% (eb i)) U := by
    have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun _y : M => (ex ⟨x, b i⟩).2) ex.baseSet := contMDiffOn_const
    have hec : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (ex ⟨y, eb i y⟩).2) ex.baseSet := by
      apply hc.congr
      intro y hy
      change (ex ⟨y, ex.symm y (ex ⟨x, b i⟩).2⟩).2 = (ex ⟨x, b i⟩).2
      simpa only using congrArg Prod.snd (ex.apply_mk_symm hy (ex ⟨x, b i⟩).2)
    have hs : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (T% (eb i)) ex.baseSet := by
      intro y hy
      rw [ex.contMDiffWithinAt_section _ hy]
      exact hec y hy
    exact hs.mono inter_subset_right
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection B y (A y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let dR := fun (A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
    N A (R B C W) y - R (N A B) C W y -
      R B (N A C) W y - R B C (N A W) y
  have hK (Q : Fin 4 → (y : M) → TangentSpace (𝓡 n) y) :
      K 1 Q = dR (Q 0) (Q 1) (Q 2) (Q 3) := by
    funext y
    simp [K, curvatureOnFields_iteratedCovariantDerivative, Fin.sum_univ_succ,
      Fin.tail, dR, N, R, sub_add_eq_sub_sub]
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D x
  have hframe (v : TangentSpace (𝓡 n) x) :
      v = ∑ i : Fin n, theta i x v • E i x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V v) hx
  have hgram (i j : Fin n) :
      a x i j = ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have htrace (u v w : TangentSpace (𝓡 n) x) :
      (∑ i, ∑ j, a x i j * g.inner x (T u (E i x) v w) (E j x)) =
        ∑ r : ι, g.inner x (T u (b r) v w) (b r) := by
    have hterm (r : ι) : g.inner x (T u (b r) v w) (b r) =
        ∑ i, ∑ j, (theta i x (b r) * theta j x (b r)) *
          g.inner x (T u (E i x) v w) (E j x) := by
      calc
        _ = g.inner x (T u (∑ i, theta i x (b r) • E i x) v w)
            (∑ j, theta j x (b r) • E j x) :=
          congrArg₂ (fun A B => g.inner x (T u A v w) B) (hframe (b r)) (hframe (b r))
        _ = _ := by
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
            sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    simp only [hgram, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp only [hterm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
  have hlow (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (i j : Fin n) :
      low ![A, E i, B, C, E j] x =
        g.inner x (T (A x) (E i x) (B x) (C x)) (E j x) := by
    dsimp only [low]
    rw [hK]
    change g.inner x (dR A (E i) B C x) (E j x) = _
    exact congrArg (fun v => g.inner x v (E j x))
      (hT e.open_baseSet A (E i) B C hA (hE i) hB hC hx).symm
  have horth (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (r : ι) :
      dR A (eb r) B C x = T (A x) (b r) (B x) (C x) := by
    have hh := hT hU A (eb r) B C (hA.mono inter_subset_left) (heb r)
      (hB.mono inter_subset_left) (hC.mono inter_subset_left) hxU
    simpa only [eb, FiberBundle.extend_apply_self] using hh.symm
  have hh := ricciFlow_connection_variation_pairing_eq_curvature_derivative_trace
    F ht e.open_baseSet X Y Z hX hY hZ hx
  change g.inner x (deriv (fun s => (F.connection s).connection Y x (X x)) t) (Z x) =
    -(∑ r : ι, g.inner x (dR X (eb r) Y Z x) (b r)) -
      (∑ r : ι, g.inner x (dR Y (eb r) Z X x) (b r)) +
      ∑ r : ι, g.inner x (dR Z (eb r) X Y x) (b r) at hh
  simp only [horth X Y Z hX hY hZ, horth Y Z X hY hZ hX,
    horth Z X Y hZ hX hY] at hh
  change g.inner x (deriv (fun s => (F.connection s).connection Y x (X x)) t) (Z x) =
    -(∑ i, ∑ j, a x i j * low ![X, E i, Y, Z, E j] x) -
      (∑ i, ∑ j, a x i j * low ![Y, E i, Z, X, E j] x) +
      ∑ i, ∑ j, a x i j * low ![Z, E i, X, Y, E j] x
  simp only [hlow X Y Z hX hY hZ, hlow Y Z X hY hZ hX,
    hlow Z X Y hZ hX hY, htrace]
  exact hh

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_iteratedCurvature_lowered_residual_zero_patterns
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let g := F.metric t
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
    let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (K t r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
    ∀ (X : Fin 4 → (y : M) → TangentSpace (𝓡 n) y),
      (∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X j)) e.baseSet) →
      ∀ {x : M}, x ∈ e.baseSet →
      g.inner x (deriv (fun s => K s 0 (Fin.init X) x) t -
        ∑ i, ∑ j, a x i j • K t 2 (Fin.cons (E i) (Fin.cons (E j) (Fin.init X))) x)
          (X (Fin.last 3) x) =
        CurvatureResidualPattern.evaluate CurvatureResidualPattern.basePattern1
            (a x) (fun r Z => low r Z x) E X +
          CurvatureResidualPattern.evaluate CurvatureResidualPattern.basePattern2
            (a x) (fun r Z => low r Z x) E X +
          CurvatureResidualPattern.evaluate CurvatureResidualPattern.basePattern3
            (a x) (fun r Z => low r Z x) E X +
          CurvatureResidualPattern.evaluate CurvatureResidualPattern.basePattern4
            (a x) (fun r Z => low r Z x) E X +
          CurvatureResidualPattern.evaluate CurvatureResidualPattern.basePattern5
            (a x) (fun r Z => low r Z x) E X +
          CurvatureResidualPattern.evaluate CurvatureResidualPattern.basePattern6
            (a x) (fun r Z => low r Z x) E X +
          CurvatureResidualPattern.evaluate CurvatureResidualPattern.basePattern7
            (a x) (fun r Z => low r Z x) E X := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let g := F.metric t
  let D := F.connection t
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
    x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
  let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K t r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
  intro X hX x hx
  let R := D.curvature x
  let L := fun u v w z => g.inner x (R u v w) z
  let Z := fun r s : TangentSpace (𝓡 n) x =>
    R (R (X 0 x) (X 1 x) r) s (X 2 x) -
      (2 : ℝ) • R (X 1 x) r (R s (X 0 x) (X 2 x)) +
      (2 : ℝ) • R r (X 0 x) (R (X 1 x) s (X 2 x)) +
      R (R (X 0 x) (X 1 x) (X 2 x)) r s -
      R (R (X 0 x) r s) (X 1 x) (X 2 x) -
      R (X 0 x) (R (X 1 x) r s) (X 2 x) -
      R (X 0 x) (X 1 x) (R (X 2 x) r s)
  have hd := (hasDerivAt_ricciFlow_iteratedCurvature_zero F ht x0
    (Fin.init X) (fun j => hX j.castSucc) hx).deriv
  change deriv (fun s => K s 0 (Fin.init X) x) t =
    (∑ i, ∑ j, a x i j • K t 2 (Fin.cons (E i) (Fin.cons (E j) (Fin.init X))) x) +
      ∑ i, ∑ j, a x i j • Z (E i x) (E j x) at hd
  rw [CurvatureResidualPattern.basePatterns_evaluate, hd, add_sub_cancel_left]
  let S := fun Q : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Q) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ _ i
  let fill := fun (γ : Fin 4 → Fin n) => Sum.elim X (fun s => E (γ s))
  have hfill (γ : Fin 4 → Fin n) (s : Fin 4 ⊕ Fin 4) : S (fill γ s) := by
    cases s with
    | inl j => exact hX j
    | inr j => exact hE (γ j)
  have hlow (γ : Fin 4 → Fin n) (slots : Fin 4 → Fin 4 ⊕ Fin 4) :
      low 0 (fun j => fill γ (slots j)) x =
        L (fill γ (slots 0) x) (fill γ (slots 1) x)
          (fill γ (slots 2) x) (fill γ (slots 3) x) := by
    change g.inner x
      (D.curvatureOnFields (fill γ (slots 0)) (fill γ (slots 1)) (fill γ (slots 2)) x)
        (fill γ (slots 3) x) = _
    rw [← curvature_eq_curvatureOnFields D e.open_baseSet _ _ _
      (hfill γ _) (hfill γ _) (hfill γ _) hx]
  have hr := curvature_reaction_lowered_two_contractions D x0 x hx
    (X 0 x) (X 1 x) (X 2 x) (X (Fin.last 3) x)
  change g.inner x (∑ j0, ∑ j1, a x j0 j1 • Z (E j0 x) (E j1 x)) (X (Fin.last 3) x) =
    ∑ j0, ∑ j1, ∑ i0, ∑ i1, (a x i0 i1 * a x j0 j1) *
      (L (X 0 x) (X 1 x) (E j0 x) (E i1 x) *
        L (E i0 x) (E j1 x) (X 2 x) (X (Fin.last 3) x) -
      2 * (L (X 1 x) (E j0 x) (E i0 x) (X (Fin.last 3) x) *
        L (E j1 x) (X 0 x) (X 2 x) (E i1 x)) +
      2 * (L (E j0 x) (X 0 x) (E i0 x) (X (Fin.last 3) x) *
        L (X 1 x) (E j1 x) (X 2 x) (E i1 x)) +
      L (X 0 x) (X 1 x) (X 2 x) (E i1 x) *
        L (E i0 x) (E j0 x) (E j1 x) (X (Fin.last 3) x) -
      L (X 0 x) (E j0 x) (E j1 x) (E i1 x) *
        L (E i0 x) (X 1 x) (X 2 x) (X (Fin.last 3) x) -
      L (X 1 x) (E j0 x) (E j1 x) (E i1 x) *
        L (X 0 x) (E i0 x) (X 2 x) (X (Fin.last 3) x) -
      L (X 2 x) (E j0 x) (E j1 x) (E i1 x) *
        L (X 0 x) (X 1 x) (E i0 x) (X (Fin.last 3) x)) at hr
  rw [hr]
  change _ = CurvatureResidualPattern.baseReaction (a x) (fun r W => low r W x) E X
  dsimp only [CurvatureResidualPattern.baseReaction]
  rw [CurvatureResidualPattern.sum_fin_four]
  have hfour (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
      (∑ u, ∑ v, ∑ i, ∑ j, f i j u v) = ∑ i, ∑ j, ∑ u, ∑ v, f i j u v := by
    conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hfour]
  apply Finset.sum_congr rfl
  intro i0 _
  apply Finset.sum_congr rfl
  intro i1 _
  apply Finset.sum_congr rfl
  intro j0 _
  apply Finset.sum_congr rfl
  intro j1 _
  let poly := fun f : (Fin 4 → Fin 4 ⊕ Fin 4) → ℝ =>
    f ![.inl 0, .inl 1, .inr 2, .inr 1] * f ![.inr 0, .inr 3, .inl 2, .inl 3] -
      2 * (f ![.inl 1, .inr 2, .inr 0, .inl 3] * f ![.inr 3, .inl 0, .inl 2, .inr 1]) +
      2 * (f ![.inr 2, .inl 0, .inr 0, .inl 3] * f ![.inl 1, .inr 3, .inl 2, .inr 1]) +
      f ![.inl 0, .inl 1, .inl 2, .inr 1] * f ![.inr 0, .inr 2, .inr 3, .inl 3] -
      f ![.inl 0, .inr 2, .inr 3, .inr 1] * f ![.inr 0, .inl 1, .inl 2, .inl 3] -
      f ![.inl 1, .inr 2, .inr 3, .inr 1] * f ![.inl 0, .inr 0, .inl 2, .inl 3] -
      f ![.inl 2, .inr 2, .inr 3, .inr 1] * f ![.inl 0, .inl 1, .inr 0, .inl 3]
  exact (congrArg (fun f => (a x i0 i1 * a x j0 j1) * poly f)
    (funext (hlow ![i0, i1, j0, j1]))).symm

end PoincareConjecture.Proofs.M03
