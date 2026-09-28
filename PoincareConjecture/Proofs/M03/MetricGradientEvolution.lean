import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M03.ConnectionFamily
import PoincareConjecture.Proofs.M03.CurvatureHom
import PoincareConjecture.Proofs.M03.CurvatureRicciSecondDerivative


















set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_ricciFlow_metric_spatial_derivative
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (x₀ : M) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) x₀).target)
    (hyU : (extChartAt (𝓡 n) x₀).symm y ∈ U)
    (w : EuclideanSpace ℝ (Fin n)) :
    let c := extChartAt (𝓡 n) x₀
    let G := fun s z => (F.metric s).inner (c.symm z)
      (Y (c.symm z)) (Z (c.symm z))
    let Q := fun z => -2 * (F.connection t).ricci (c.symm z)
      (Y (c.symm z)) (Z (c.symm z))
    HasDerivAt (fun s => fderiv ℝ (G s) y w) (fderiv ℝ Q y w) t := by
  dsimp only
  let c := extChartAt (𝓡 n) x₀
  let H : ℝ × EuclideanSpace ℝ (Fin n) → ℝ := fun p =>
    (F.metric p.1).inner (c.symm p.2) (Y (c.symm p.2)) (Z (c.symm p.2))
  let Q := fun z => -2 * (F.connection t).ricci (c.symm z)
    (Y (c.symm z)) (Z (c.symm z))
  change HasDerivAt (fun s => fderiv ℝ (fun z => H (s, z)) y w)
    (fderiv ℝ Q y w) t
  have hpair := contMDiffOn_family_metric_pair F.smooth Y Z hY hZ
  have hpair' := hpair.mono (show interior J ×ˢ U ⊆ J ×ˢ U from
    fun _ hp => ⟨interior_subset hp.1, hp.2⟩)
  have hc (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x₀).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  have hH (s : ℝ) (hs : s ∈ interior J) (z : EuclideanSpace ℝ (Fin n))
      (hz : z ∈ c.target) (hzU : c.symm z ∈ U) : ContDiffAt ℝ ∞ H (s, z) := by
    have hp := (hpair' (s, c.symm z) ⟨hs, hzU⟩).contMDiffAt
      ((isOpen_interior.prod hU).mem_nhds ⟨hs, hzU⟩)
    have hh := hp.comp (s, z)
      (contMDiffAt_fst.prodMk ((hc z hz).comp (s, z) contMDiffAt_snd))
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact hh.contDiffAt
  have hHty := hH t ht y hy hyU
  have hD : DifferentiableAt ℝ (fderiv ℝ H) (t, y) :=
    (hHty.fderiv_right (m := 1)
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).differentiableAt (by norm_num)
  have htimeSlice (z : EuclideanSpace ℝ (Fin n)) :
      HasDerivAt (fun s : ℝ => (s, z)) (1, 0) t := by
    simpa using ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) z t)).hasDerivAt
  have hspace (s : ℝ) (hs : s ∈ interior J) :
      fderiv ℝ (fun z => H (s, z)) y w = fderiv ℝ H (s, y) (0, w) := by
    have hsH := (hH s hs y hy hyU).differentiableAt (by simp)
    have hd := hsH.hasFDerivAt.comp y
      ((hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id y))
    have hv := congrArg (fun L => L w) hd.fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply] using hv
  have htime : HasDerivAt (fun s => fderiv ℝ H (s, y) (0, w))
      (fderiv ℝ (fderiv ℝ H) (t, y) (1, 0) (0, w)) t := by
    have hd := hD.hasFDerivAt.comp_hasDerivAt t (htimeSlice y)
    simpa only [Function.comp_def, map_zero, add_zero] using
      hd.clm_apply (hasDerivAt_const t (0, w))
  have hspaceTime : fderiv ℝ (fun z => fderiv ℝ H (t, z) (1, 0)) y w =
      fderiv ℝ (fderiv ℝ H) (t, y) (0, w) (1, 0) := by
    have hd := hD.hasFDerivAt.comp y
      ((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id y))
    have ha := hd.clm_apply (hasFDerivAt_const (𝕜 := ℝ) (1, (0 : EuclideanSpace ℝ (Fin n))) y)
    have hv := congrArg (fun L => L w) ha.fderiv
    simpa only [Function.comp_def, add_apply, ContinuousLinearMap.comp_apply,
      zero_apply, map_zero, zero_add,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply] using hv
  have hyUnhds : c.symm ⁻¹' U ∈ 𝓝 y :=
    (hc y hy).continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
  have hQ : (fun z => fderiv ℝ H (t, z) (1, 0)) =ᶠ[𝓝 y] Q := by
    filter_upwards [extChartAt_target_mem_nhds' hy, hyUnhds] with z hz hzU
    have hd := ((hH t ht z hz hzU).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      (htimeSlice z)
    have he := (F.equation t (interior_subset ht) (c.symm z)
      (Y (c.symm z)) (Z (c.symm z))).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)
    exact hd.unique he
  have hslice : (fun s => fderiv ℝ (fun z => H (s, z)) y w) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ H (s, y) (0, w)) := by
    filter_upwards [isOpen_interior.mem_nhds ht] with s hs
    exact hspace s hs
  apply (htime.congr_of_eventuallyEq hslice).congr_deriv
  have hsymm := hHty.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [hsymm.eq (1, 0) (0, w), ← hspaceTime, hQ.fderiv_eq]

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000


theorem curvature_iterated_bochner_local_frame
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (k : ℕ) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let G := fun y : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
    let K := fun m => curvatureOnFields_iteratedCovariantDerivative D m
    let pair := fun (y : M) (S T : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) y) =>
      ∑ α : Fin (k + 3) → Fin n, ∑ β : Fin (k + 3) → Fin n,
        (∏ r, a y (α r) (β r)) * g.inner y (S α) (T β)
    let k0 := fun α : Fin (k + 3) → Fin n => K k (fun r => E (α r))
    let k1 := fun i (α : Fin (k + 3) → Fin n) =>
      K (k + 1) (Fin.cons (E i) (fun r => E (α r)))
    let k2 := fun i j (α : Fin (k + 3) → Fin n) =>
      K (k + 2) (Fin.cons (E i) (Fin.cons (E j) (fun r => E (α r))))
    let q := fun y => pair y (fun α => k0 α y) (fun α => k0 α y)
    let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
      mvfderiv (𝓡 n) f y (P y)
    ∀ {x : M}, x ∈ e.baseSet →
      (∑ i, ∑ j, a x i j * (d (E i) (d (E j) q) x - d (N (E i) (E j)) q x)) =
        2 * (∑ i, ∑ j, a x i j * pair x (fun α => k1 i α x) (fun α => k1 j α x)) +
        2 * (∑ i, ∑ j, a x i j * pair x (fun α => k2 i j α x) (fun α => k0 α x)) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
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
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let G := fun y : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
  let K := fun m => curvatureOnFields_iteratedCovariantDerivative D m
  let Gamma := fun y i j p => theta p y (N (E i) (E j) y)
  let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
    mvfderiv (𝓡 n) f y (P y)
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet
  let C := fun f : M → ℝ => ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet
  have hmd (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W)
      {y : M} (hy : y ∈ e.baseSet) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% W) y :=
    (hW.contMDiffAt (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
  have hcmd (f : M → ℝ) (hf : C f) {y : M} (hy : y ∈ e.baseSet) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y :=
    (hf.contMDiffAt (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hN (P Q : (y : M) → TangentSpace (𝓡 n) y) (hP : S P) (hQ : S Q) :
      S (N P Q) := D.contMDiffOn_connection_apply e.open_baseSet P Q hP hQ
  have hK (m : ℕ) (X : Fin (m + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hX : ∀ r, S (X r)) : S (K m X) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D e.open_baseSet m X hX
  have hinner (A B : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) (hB : S B) :
      C (fun y => g.inner y (A y) (B y)) := hA.inner_bundle hB
  have ha (i j : Fin n) : C (fun y => a y i j) := by
    have hf : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) univ :=
      (g.contMDiff.comp contMDiff_snd).contMDiffOn
    have hi := (contMDiffOn_family_metric_frame_inverse hf x0).2.2
    have hs := hi.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨mem_univ (0 : ℝ), hy⟩)
    exact (contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply
      (hs.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
  have hchart (f : M → ℝ) (hf : C f) {z : V} (hz : z ∈ c.target) (i : Fin n) :
      d (E i) f (c.symm z) =
        fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) := by
    let x := c.symm z
    have hx : x ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
    have hcs : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm z :=
      ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
        (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
    have he : e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm z := by
      have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
        (c.map_target hz)
      simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
        mfderivWithin_univ] at hh
      change e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (c x) at hh
      rwa [c.right_inv hz] at hh
    have hframe : E i x = e.symmL ℝ x (EuclideanSpace.single i 1) := by
      calc
        E i x = e.basisAt b hx i := e.localFrame_apply_of_mem_baseSet b hx
        _ = e.symm x (EuclideanSpace.single i 1) := by
          simp only [Trivialization.basisAt, Module.Basis.map_apply, b,
            OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
            Trivialization.linearEquivAt_symm_apply]
        _ = e.symmL ℝ x (EuclideanSpace.single i 1) := (e.symmL_apply hx _).symm
    have hfd : fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) =
        mvfderiv (𝓡 n) f x (e.symmL ℝ x (EuclideanSpace.single i 1)) := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z (EuclideanSpace.single i 1) = _
      erw [mvfderiv_comp_apply z (hcmd f hf hx) hcs (EuclideanSpace.single i 1), ← he]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) f x) hframe).trans hfd.symm
  have hda {x : M} (hx : x ∈ e.baseSet) (i j l : Fin n) :
      d (E i) (fun y => a y j l) x =
        -(∑ p, (Gamma x i p j * a x p l + Gamma x i p l * a x j p)) := by
    have hxc : x ∈ c.source := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hx
    have hh := metric_inverse_covariant_derivative_coordinates D x0 (c x) (c.map_source hxc) i j l
    have he := hchart (fun y => a y j l) (ha j l) (c.map_source hxc) i
    rw [c.left_inv hxc] at hh he
    exact he.trans hh
  have hasymm {x : M} (hx : x ∈ e.baseSet) (i j : Fin n) : a x i j = a x j i := by
    have hi := metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
    have hj := metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx j i
    change a x i j = _ at hi
    change a x j i = _ at hj
    rw [hi, hj]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hrec (W : (y : M) → TangentSpace (𝓡 n) y)
      {y : M} (hy : y ∈ e.baseSet) : W y = ∑ i, theta i y (W y) • E i y :=
    e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hy
  have hslot (m : ℕ) {x : M} (hx : x ∈ e.baseSet)
      (X : Fin (m + 3) → (y : M) → TangentSpace (𝓡 n) y) (hX : ∀ r, S (X r))
      (r : Fin (m + 3)) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      K m (Function.update X r W) x =
        ∑ p, theta p x (W x) • K m (Function.update X r (E p)) x := by
    obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D m x
    have hev (Z : (y : M) → TangentSpace (𝓡 n) y) (hZ : S Z) :
        T (Function.update (fun j => X j x) r (Z x)) = K m (Function.update X r Z) x := by
      have hz : ∀ j, S (Function.update X r Z j) := by
        intro j
        by_cases hj : j = r
        · subst j
          simpa only [Function.update_self] using hZ
        · simpa only [Function.update_of_ne hj] using hX j
      have he : (fun j => Function.update X r Z j x) =
          Function.update (fun j => X j x) r (Z x) := by
        funext j
        by_cases hj : j = r
        · subst j
          simp only [Function.update_self]
        · simp only [Function.update_of_ne hj]
      rw [← he]
      exact hT e.open_baseSet _ hz hx
    calc
      _ = T (Function.update (fun j => X j x) r (W x)) := (hev W hW).symm
      _ = T (Function.update (fun j => X j x) r (∑ p, theta p x (W x) • E p x)) :=
        congrArg (fun z => T (Function.update (fun j => X j x) r z)) (hrec W hx)
      _ = ∑ p, theta p x (W x) • T (Function.update (fun j => X j x) r (E p x)) := by
        rw [T.map_update_sum]
        simp only [T.map_update_smul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hev (E p) (hE p)]
  have hupdate (m : ℕ) (α : Fin (m + 3) → Fin n) (r : Fin (m + 3)) (p : Fin n) :
      Function.update (fun j => E (α j)) r (E p) =
        (fun j => E (Function.update α r p j)) := by
    funext j
    by_cases hj : j = r
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  have hcons (m : ℕ) (i : Fin n) (α : Fin (m + 3) → Fin n) :
      (fun r : Fin (m + 4) => E (Fin.cons (α := fun _ => Fin n) i α r)) =
        Fin.cons (E i) (fun r => E (α r)) :=
    Fin.comp_cons E i α
  have hk (m : ℕ) {x : M} (hx : x ∈ e.baseSet)
      (i : Fin n) (α : Fin (m + 3) → Fin n) :
      N (E i) (K m (fun r => E (α r))) x =
        K (m + 1) (Fin.cons (E i) (fun r => E (α r))) x +
          ∑ r, ∑ p, Gamma x i (α r) p • K m (fun j => E (Function.update α r p j)) x := by
    have hs (r : Fin (m + 3)) :
        K m (Function.update (fun j => E (α j)) r (N (E i) (E (α r)))) x =
          ∑ p, Gamma x i (α r) p • K m (fun j => E (Function.update α r p j)) x := by
      calc
        _ = ∑ p, theta p x (N (E i) (E (α r)) x) •
            K m (Function.update (fun j => E (α j)) r (E p)) x :=
          hslot m hx (fun j => E (α j)) (fun j => hE (α j)) r
            (N (E i) (E (α r))) (hN _ _ (hE i) (hE (α r)))
        _ = _ := Finset.sum_congr rfl fun p _ =>
          congrArg (fun Z => Gamma x i (α r) p • K m Z x) (hupdate m α r p)
    have he : K (m + 1) (Fin.cons (E i) (fun r => E (α r))) x =
        N (E i) (K m (fun r => E (α r))) x -
          ∑ r, K m (Function.update (fun j => E (α j)) r (N (E i) (E (α r)))) x := by
      rfl
    calc
      _ = K (m + 1) (Fin.cons (E i) (fun r => E (α r))) x +
          ∑ r, K m (Function.update (fun j => E (α j)) r (N (E i) (E (α r)))) x :=
        (eq_sub_iff_add_eq.mp he).symm
      _ = _ := congrArg
        (fun z => K (m + 1) (Fin.cons (E i) (fun r => E (α r))) x + z)
        (Finset.sum_congr rfl fun r _ => hs r)
  let k0 := fun α : Fin (k + 3) → Fin n => K k (fun r => E (α r))
  let k1 := fun i (α : Fin (k + 3) → Fin n) =>
    K (k + 1) (Fin.cons (E i) (fun r => E (α r)))
  let k2 := fun i j (α : Fin (k + 3) → Fin n) =>
    K (k + 2) (Fin.cons (E i) (Fin.cons (E j) (fun r => E (α r))))
  let act := fun (x : M) (i : Fin n)
      (U : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) x) (α : Fin (k + 3) → Fin n) =>
    ∑ r, ∑ p, Gamma x i (α r) p • U (Function.update α r p)
  have hk0 {x : M} (hx : x ∈ e.baseSet) (i : Fin n) (α : Fin (k + 3) → Fin n) :
      N (E i) (k0 α) x = k1 i α x + act x i (fun β => k0 β x) α :=
    hk k hx i α
  have hk1 {x : M} (hx : x ∈ e.baseSet) (i j : Fin n) (α : Fin (k + 3) → Fin n) :
      N (E i) (k1 j α) x = k2 i j α x +
        (∑ p, Gamma x i j p • k1 p α x) + act x i (fun β => k1 j β x) α := by
    have hh := hk (k + 1) hx i (Fin.cons j α)
    rw [Fin.sum_univ_succ] at hh
    simpa only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero,
      ← Fin.cons_update, hcons, k1, k2, act, add_assoc] using hh
  let w := fun (y : M) (α β : Fin (k + 3) → Fin n) => ∏ r, a y (α r) (β r)
  let pair := fun (y : M) (U W : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) y) =>
    ∑ α, ∑ β, w y α β * g.inner y (U α) (W β)
  have hw (α β : Fin (k + 3) → Fin n) : C (fun y => w y α β) :=
    contMDiffOn_finsetProd fun r _ => ha (α r) (β r)
  have hpair (U W : (Fin (k + 3) → Fin n) → (y : M) → TangentSpace (𝓡 n) y)
      (hU : ∀ α, S (U α)) (hW : ∀ α, S (W α)) :
      C (fun y => pair y (fun α => U α y) (fun α => W α y)) :=
    contMDiffOn_finsetSum fun α _ => contMDiffOn_finsetSum fun β _ =>
      (hw α β).mul (hinner (U α) (W β) (hU α) (hW β))
  have hdsum {ι : Type} [Fintype ι] {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (f : ι → M → ℝ) (hf : ∀ i, C (f i)) :
      d P (fun y => ∑ i, f i y) x = ∑ i, d P (f i) x := by
    have aux (s : Finset ι) :
        d P (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, d P (f i) x := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, d, mvfderiv_const, zero_apply]
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        dsimp only [d] at ih ⊢
        rw [mvfderiv_fun_add (hcmd _ (hf i) hx)
          (hcmd _ (contMDiffOn_finsetSum fun j _ => hf j) hx), add_apply, ih]
    exact aux Finset.univ
  have hdprod {x : M} (hx : x ∈ e.baseSet) (i : Fin n) (α β : Fin (k + 3) → Fin n) :
      d (E i) (fun y => w y α β) x =
        ∑ r : Fin (k + 3), (∏ s ∈ Finset.univ.erase r, a x (α s) (β s)) *
          d (E i) (fun y => a y (α r) (β r)) x := by
    have aux (s : Finset (Fin (k + 3))) :
        d (E i) (fun y => ∏ r ∈ s, a y (α r) (β r)) x =
          ∑ r ∈ s, (∏ t ∈ s.erase r, a x (α t) (β t)) *
            d (E i) (fun y => a y (α r) (β r)) x := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.prod_empty, Finset.sum_empty, d, mvfderiv_const, zero_apply]
      | @insert r s hr ih =>
        simp only [Finset.prod_insert hr, Finset.sum_insert hr, Finset.erase_insert hr]
        have hmul := congrArg (fun L => L (E i x)) (mvfderiv_fun_mul
          (hcmd _ (ha (α r) (β r)) hx)
          (hcmd _ (contMDiffOn_finsetProd (t := s) fun t _ => ha (α t) (β t)) hx))
        change d (E i) (fun y => a y (α r) (β r) * ∏ t ∈ s, a y (α t) (β t)) x = _
        simp only [add_apply, smul_apply, smul_eq_mul] at hmul
        change d (E i) (fun y => a y (α r) (β r) * ∏ t ∈ s, a y (α t) (β t)) x =
          a x (α r) (β r) * d (E i) (fun y => ∏ t ∈ s, a y (α t) (β t)) x +
            (∏ t ∈ s, a x (α t) (β t)) * d (E i) (fun y => a y (α r) (β r)) x at hmul
        rw [hmul, ih, add_comm, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem ht hr).symm,
          Finset.prod_insert (by simp [hr])]
        ring
    exact aux Finset.univ
  have hdpair {x : M} (hx : x ∈ e.baseSet) (i : Fin n)
      (U W : (Fin (k + 3) → Fin n) → (y : M) → TangentSpace (𝓡 n) y)
      (hU : ∀ α, S (U α)) (hW : ∀ α, S (W α)) :
      d (E i) (fun y => pair y (fun α => U α y) (fun α => W α y)) x =
        ∑ α, ∑ β, (
          w x α β * (g.inner x (N (E i) (U α) x) (W β x) +
            g.inner x (U α x) (N (E i) (W β) x)) +
          d (E i) (fun y => w y α β) x * g.inner x (U α x) (W β x)) := by
    dsimp only [pair]
    rw [hdsum hx (E i) (fun α y => ∑ β, w y α β * g.inner y (U α y) (W β y))
      (fun α => contMDiffOn_finsetSum (t := Finset.univ) fun β _ =>
      (hw α β).mul (hinner (U α) (W β) (hU α) (hW β)))]
    apply Finset.sum_congr rfl
    intro α _
    rw [hdsum hx (E i) (fun β y => w y α β * g.inner y (U α y) (W β y))
      (fun β => (hw α β).mul (hinner (U α) (W β) (hU α) (hW β)))]
    apply Finset.sum_congr rfl
    intro β _
    have hh := congrArg (fun L => L (E i x)) (mvfderiv_fun_mul
      (hcmd _ (hw α β) hx) (hcmd _ (hinner (U α) (W β) (hU α) (hW β)) hx))
    dsimp only [d, N]
    simpa only [add_apply, smul_apply, smul_eq_mul,
      D.mvfderiv_inner (E i) (U α) (W β) (hmd _ (hU α) hx) (hmd _ (hW β) hx),
      mul_comm] using hh
  have slotSwap (r : Fin (k + 3)) (f : (Fin (k + 3) → Fin n) → Fin n → ℝ) :
      (∑ α, ∑ p, f α p) = ∑ α, ∑ p, f (Function.update α r p) (α r) := by
    let swap := fun q : (Fin (k + 3) → Fin n) × Fin n => (Function.update q.1 r q.2, q.1 r)
    have hs : Function.Involutive swap := by
      intro q
      apply Prod.ext
      · funext j
        by_cases hj : j = r
        · subst j
          simp [swap]
        · simp [swap, Function.update_of_ne hj]
      · simp [swap]
    let eqv : ((Fin (k + 3) → Fin n) × Fin n) ≃ ((Fin (k + 3) → Fin n) × Fin n) :=
      { toFun := swap, invFun := swap, left_inv := hs, right_inv := hs }
    have hh := (eqv.sum_comp (fun q => f q.1 q.2)).symm
    change (∑ q : (Fin (k + 3) → Fin n) × Fin n, f q.1 q.2) =
      ∑ q : (Fin (k + 3) → Fin n) × Fin n, f (Function.update q.1 r q.2) (q.1 r) at hh
    simpa only [Fintype.sum_prod_type] using hh
  have weightCancellation (a G : Fin n → Fin n → ℝ)
      (F : (Fin (k + 3) → Fin n) → (Fin (k + 3) → Fin n) → ℝ) :
      let W := fun α β : Fin (k + 3) → Fin n => ∏ r, a (α r) (β r)
      let w := fun r (α β : Fin (k + 3) → Fin n) =>
        ∏ s ∈ Finset.univ.erase r, a (α s) (β s)
      (∑ α, ∑ β, ∑ r, w r α β *
        (∑ p, (G p (α r) * a p (β r) + G p (β r) * a (α r) p)) * F α β) =
        ∑ α, ∑ β, W α β *
          ((∑ r, ∑ p, G (α r) p * F (Function.update α r p) β) +
            ∑ r, ∑ p, G (β r) p * F α (Function.update β r p)) := by
    dsimp only
    let W := fun α β : Fin (k + 3) → Fin n => ∏ r, a (α r) (β r)
    let w := fun r (α β : Fin (k + 3) → Fin n) =>
      ∏ s ∈ Finset.univ.erase r, a (α s) (β s)
    have hWL (r : Fin (k + 3)) (α β : Fin (k + 3) → Fin n) (p : Fin n) :
        W (Function.update α r p) β = w r α β * a p (β r) := by
      dsimp only [W, w]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro s hs
      rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
    have hWR (r : Fin (k + 3)) (α β : Fin (k + 3) → Fin n) (p : Fin n) :
        W α (Function.update β r p) = w r α β * a (α r) p := by
      dsimp only [W, w]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro s hs
      rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
    have hL (r : Fin (k + 3)) (β : Fin (k + 3) → Fin n) :
        (∑ α, ∑ p, W α β * (G (α r) p * F (Function.update α r p) β)) =
          ∑ α, ∑ p, w r α β * (G p (α r) * a p (β r)) * F α β := by
      rw [slotSwap r]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro p _
      rw [hWL]
      simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      ring
    have hR (r : Fin (k + 3)) (α : Fin (k + 3) → Fin n) :
        (∑ β, ∑ p, W α β * (G (β r) p * F α (Function.update β r p))) =
          ∑ β, ∑ p, w r α β * (G p (β r) * a (α r) p) * F α β := by
      rw [slotSwap r]
      apply Finset.sum_congr rfl
      intro β _
      apply Finset.sum_congr rfl
      intro p _
      rw [hWR]
      simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      ring
    have reorder (f : (Fin (k + 3) → Fin n) → (Fin (k + 3) → Fin n) →
        Fin (k + 3) → Fin n → ℝ) :
        (∑ α, ∑ β, ∑ r, ∑ p, f α β r p) = ∑ r, ∑ β, ∑ α, ∑ p, f α β r p := by
      calc
        _ = ∑ β, ∑ α, ∑ r, ∑ p, f α β r p := Finset.sum_comm
        _ = ∑ β, ∑ r, ∑ α, ∑ p, f α β r p := by
          apply Finset.sum_congr rfl
          intro β _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    change (∑ α, ∑ β, ∑ r, w r α β *
        (∑ p, (G p (α r) * a p (β r) + G p (β r) * a (α r) p)) * F α β) =
      ∑ α, ∑ β, W α β *
        ((∑ r, ∑ p, G (α r) p * F (Function.update α r p) β) +
          ∑ r, ∑ p, G (β r) p * F α (Function.update β r p))
    simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · calc
        _ = ∑ r, ∑ β, ∑ α, ∑ p,
            w r α β * (G p (α r) * a p (β r)) * F α β := reorder _
        _ = ∑ r, ∑ β, ∑ α, ∑ p,
            W α β * (G (α r) p * F (Function.update α r p) β) := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro β _
          exact (hL r β).symm
        _ = _ := (reorder _).symm
    · calc
        _ = ∑ α, ∑ r, ∑ β, ∑ p,
            w r α β * (G p (β r) * a (α r) p) * F α β := by
          apply Finset.sum_congr rfl
          intro α _
          exact Finset.sum_comm
        _ = ∑ α, ∑ r, ∑ β, ∑ p,
            W α β * (G (β r) p * F α (Function.update β r p)) := by
          apply Finset.sum_congr rfl
          intro α _
          apply Finset.sum_congr rfl
          intro r _
          exact (hR r α).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro α _
          exact Finset.sum_comm
  have hpairD {x : M} (hx : x ∈ e.baseSet) (i : Fin n)
      (U W : (Fin (k + 3) → Fin n) → (y : M) → TangentSpace (𝓡 n) y)
      (U' W' : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) x)
      (hU : ∀ α, S (U α)) (hW : ∀ α, S (W α))
      (hNU : ∀ α, N (E i) (U α) x = U' α + act x i (fun β => U β x) α)
      (hNW : ∀ α, N (E i) (W α) x = W' α + act x i (fun β => W β x) α) :
      d (E i) (fun y => pair y (fun α => U α y) (fun α => W α y)) x =
        pair x U' (fun α => W α x) + pair x (fun α => U α x) W' := by
    have hweight := weightCancellation (a x) (Gamma x i)
      (fun α β => g.inner x (U α x) (W β x))
    have hcancel : (∑ α, ∑ β, d (E i) (fun y => w y α β) x *
        g.inner x (U α x) (W β x)) =
        -(pair x (act x i (fun α => U α x)) (fun α => W α x) +
          pair x (fun α => U α x) (act x i (fun α => W α x))) := by
      simp_rw [hdprod hx i, hda hx i]
      simp only [mul_neg, Finset.sum_neg_distrib, neg_mul, Finset.sum_mul]
      rw [hweight]
      simp only [pair, w, act, map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul,
        mul_add, Finset.sum_add_distrib]
    rw [hdpair hx i U W hU hW]
    simp only [Finset.sum_add_distrib]
    rw [hcancel]
    simp only [hNU, hNW, pair, map_add, add_apply, mul_add, Finset.sum_add_distrib]
    ring
  have hpairSym {x : M} (hx : x ∈ e.baseSet)
      (U W : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) x) :
      pair x U W = pair x W U := by
    dsimp only [pair]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    rw [g.symm]
    congr 1
    exact Finset.prod_congr rfl (fun r _ => hasymm hx _ _)
  have hpairAdd (x : M) (U V W : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) x) :
      pair x (fun α => U α + V α) W = pair x U W + pair x V W := by
    simp only [pair, map_add, add_apply, mul_add, Finset.sum_add_distrib]
  have hpairSum (x : M) (f : Fin n → ℝ)
      (U : Fin n → (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) x)
      (W : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) x) :
      pair x (fun α => ∑ p, f p • U p α) W = ∑ p, f p * pair x (U p) W := by
    simp only [pair, map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul,
      Finset.mul_sum]
    calc
      _ = ∑ α, ∑ p, ∑ β, w x α β * (f p * g.inner x (U p α) (W β)) := by
        apply Finset.sum_congr rfl
        intro α _
        exact Finset.sum_comm
      _ = ∑ p, ∑ α, ∑ β, w x α β * (f p * g.inner x (U p α) (W β)) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        ring
  have hS0 (α : Fin (k + 3) → Fin n) : S (k0 α) := hK k _ (fun r => hE (α r))
  have hS1 (i : Fin n) (α : Fin (k + 3) → Fin n) : S (k1 i α) := by
    have hs := hK (k + 1)
      (fun r => E (Fin.cons (α := fun _ => Fin n) i α r))
      (fun r => hE (Fin.cons (α := fun _ => Fin n) i α r))
    exact (congrArg S (congrArg (K (k + 1)) (hcons k i α))).mp hs
  let q := fun y => pair y (fun α => k0 α y) (fun α => k0 α y)
  have hfirst {x : M} (hx : x ∈ e.baseSet) (i : Fin n) :
      d (E i) q x = 2 * pair x (fun α => k1 i α x) (fun α => k0 α x) := by
    change d (E i) (fun y => pair y (fun α => k0 α y) (fun α => k0 α y)) x = _
    rw [hpairD hx i k0 k0 _ _ hS0 hS0 (hk0 hx i) (hk0 hx i),
      hpairSym hx (fun α => k0 α x) (fun α => k1 i α x)]
    ring
  have hsecond {x : M} (hx : x ∈ e.baseSet) (i j : Fin n) :
      d (E i) (fun y => pair y (fun α => k1 j α y) (fun α => k0 α y)) x =
        pair x (fun α => k2 i j α x) (fun α => k0 α x) +
          (∑ p, Gamma x i j p * pair x (fun α => k1 p α x) (fun α => k0 α x)) +
          pair x (fun α => k1 j α x) (fun α => k1 i α x) := by
    rw [hpairD hx i (k1 j) k0 _ _ (hS1 j) hS0 (hk1 hx i j) (hk0 hx i),
      hpairAdd, hpairSum]
  have htwice {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) (hf : C f) :
      d P (fun y => 2 * f y) x = 2 * d P f x := by
    have heq : (fun y => 2 * f y) = f + f := by
      funext y
      exact two_mul _
    rw [heq]
    dsimp only [d]
    rw [mvfderiv_add (hcmd f hf hx) (hcmd f hf hx)]
    simp only [add_apply, two_mul]
  have hhessian {x : M} (hx : x ∈ e.baseSet) (i j : Fin n) :
      d (E i) (d (E j) q) x - d (N (E i) (E j)) q x =
        2 * pair x (fun α => k1 i α x) (fun α => k1 j α x) +
          2 * pair x (fun α => k2 i j α x) (fun α => k0 α x) := by
    have heq : d (E j) q =ᶠ[𝓝 x]
        (fun y => 2 * pair y (fun α => k1 j α y) (fun α => k0 α y)) :=
      Filter.eventuallyEq_of_mem (e.open_baseSet.mem_nhds hx) (fun y hy => hfirst hy j)
    have hd : d (E i) (d (E j) q) x =
        d (E i) (fun y => 2 * pair y (fun α => k1 j α y) (fun α => k0 α y)) x := by
      change (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (d (E j) q) x) (E i x) =
        (mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
          (fun y => 2 * pair y (fun α => k1 j α y) (fun α => k0 α y)) x) (E i x)
      exact congrArg (fun L => L (E i x)) (heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))
    have hdir : d (N (E i) (E j)) q x =
        2 * ∑ p, Gamma x i j p * pair x (fun α => k1 p α x) (fun α => k0 α x) := by
      dsimp only [d]
      rw [hrec (N (E i) (E j)) hx, map_sum]
      simp only [map_smul, smul_eq_mul]
      change (∑ p, Gamma x i j p * d (E p) q x) = _
      simp_rw [hfirst hx]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [hd, htwice hx (E i) _ (hpair (k1 j) k0 (hS1 j) hS0), hsecond hx i j, hdir,
      hpairSym hx (fun α => k1 j α x) (fun α => k1 i α x)]
    ring
  change ∀ {x : M}, x ∈ e.baseSet →
    (∑ i, ∑ j, a x i j * (d (E i) (d (E j) q) x - d (N (E i) (E j)) q x)) =
      2 * (∑ i, ∑ j, a x i j * pair x (fun α => k1 i α x) (fun α => k1 j α x)) +
      2 * (∑ i, ∑ j, a x i j * pair x (fun α => k2 i j α x) (fun α => k0 α x))
  intro x hx
  simp_rw [hhessian hx]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring


theorem curvature_iterated_bochner_next_energy
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (k : ℕ) (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let K := curvatureOnFields_iteratedCovariantDerivative D (k + 1)
    let pair := fun (U W : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) x) =>
      ∑ α, ∑ β, (∏ r, a (α r) (β r)) * g.inner x (U α) (W β)
    let k1 := fun i (α : Fin (k + 3) → Fin n) =>
      K (Fin.cons (E i) (fun r => E (α r))) x
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend V (b i)
    let kb := fun γ : Fin (k + 4) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      K (fun r => ext (γ r)) x
    let pnext := ∑ i, ∑ j, a i j * pair (k1 i) (k1 j)
    pnext = (∑ γ, g.inner x (kb γ) (kb γ)) ∧ 0 ≤ pnext := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  let K := curvatureOnFields_iteratedCovariantDerivative D (k + 1)
  let pair := fun (U W : (Fin (k + 3) → Fin n) → TangentSpace (𝓡 n) x) =>
    ∑ α, ∑ β, (∏ r, a (α r) (β r)) * g.inner x (U α) (W β)
  let k1 := fun i (α : Fin (k + 3) → Fin n) =>
    K (Fin.cons (E i) (fun r => E (α r))) x
  let A := fun α : Fin (k + 4) → Fin n => K (fun r => E (α r)) x
  let b := g.orthonormalBasis x
  let ext := fun i => FiberBundle.extend V (b i)
  let kb := fun γ : Fin (k + 4) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
    K (fun r => ext (γ r)) x
  let pnext := ∑ i, ∑ j, a i j * pair (k1 i) (k1 j)
  let full := ∑ α : Fin (k + 4) → Fin n, ∑ β : Fin (k + 4) → Fin n,
    (∏ r, a (α r) (β r)) * g.inner x (A α) (A β)
  change pnext = (∑ γ, g.inner x (kb γ) (kb γ)) ∧ 0 ≤ pnext
  have sumCons (f : (Fin (k + 4) → Fin n) → ℝ) :
      (∑ α, f α) = ∑ i, ∑ α : Fin (k + 3) → Fin n, f (Fin.cons i α) := by
    have hh := (Fin.consEquiv (fun _ : Fin (k + 4) => Fin n)).sum_comp f
    change (∑ p : Fin n × (Fin (k + 3) → Fin n), f (Fin.cons p.1 p.2)) = ∑ α, f α at hh
    simpa only [Fintype.sum_prod_type] using hh.symm
  have hA (i : Fin n) (α : Fin (k + 3) → Fin n) : A (Fin.cons i α) = k1 i α := by
    exact congrArg (fun X => K X x) (Fin.comp_cons E i α)
  have hprod (i j : Fin n) (α β : Fin (k + 3) → Fin n) :
      (∏ r : Fin (k + 4), a (Fin.cons (α := fun _ => Fin n) i α r)
        (Fin.cons (α := fun _ => Fin n) j β r)) =
        a i j * ∏ r, a (α r) (β r) := by
    rw [Fin.prod_univ_succ]
    rfl
  have hsplit : full = pnext := by
    dsimp only [full, pnext]
    rw [sumCons]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [sumCons]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [pair]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    rw [hprod, hA, hA]
    ring
  have hframe : full = ∑ γ, g.inner x (kb γ) (kb γ) :=
    curvature_iterated_squared_norm_frame_eq_orthonormal D (k + 1) x0 hx
  have heq := hsplit.symm.trans hframe
  refine ⟨heq, ?_⟩
  rw [heq]
  apply Finset.sum_nonneg
  intro γ _
  by_cases hv : kb γ = 0
  · simp [hv]
  · exact le_of_lt (g.pos x (kb γ) hv)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_iterated_spatial_correction_two_contractions
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) (k : ℕ) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let K := curvatureOnFields_iteratedCovariantDerivative D
    let R := fun (P Q Z : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.curvatureOnFields P Q Z y
    let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
    let Co := fun (P A C : (y : M) → TangentSpace (𝓡 n) y)
      (Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
      R P A (K (k + 1) (Fin.cons C Y)) y -
      K (k + 1) (Fin.cons (R P A C) Y) y -
      (∑ l, K (k + 1) (Fin.cons C (Function.update Y l (R P A (Y l)))) y) +
      K 1 ![A, P, C, K k Y] y +
      R P C (K (k + 1) (Fin.cons A Y)) y -
      (∑ l, K (k + 1) (Fin.cons A (Function.update Y l (R P C (Y l)))) y) -
      ∑ l, K k (Function.update Y l (K 1 ![A, P, C, Y l])) y
    ∀ (P : (y : M) → TangentSpace (𝓡 n) y)
      (Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (z : (y : M) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet →
      (∀ l, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Y l)) e.baseSet) →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% z) e.baseSet →
      ∀ {x : M}, x ∈ e.baseSet →
      g.inner x (∑ i, ∑ j, a x i j • Co P (E i) (E j) Y x) (z x) =
        ∑ i, ∑ j, ∑ u, ∑ v, (a x i j * a x u v) *
          (low 0 ![P, E i, E u, z] x *
              low (k + 1) (Fin.snoc (Fin.cons (E j) Y) (E v)) x -
            low 0 ![P, E i, E j, E v] x *
              low (k + 1) (Fin.snoc (Fin.cons (E u) Y) z) x -
            (∑ l, low 0 ![P, E i, Y l, E v] x *
              low (k + 1) (Fin.snoc (Fin.cons (E j) (Function.update Y l (E u))) z) x) +
            low 1 ![E i, P, E j, E u, z] x * low k (Fin.snoc Y (E v)) x +
            low 0 ![P, E j, E u, z] x *
              low (k + 1) (Fin.snoc (Fin.cons (E i) Y) (E v)) x -
            (∑ l, low 0 ![P, E j, Y l, E v] x *
              low (k + 1) (Fin.snoc (Fin.cons (E i) (Function.update Y l (E u))) z) x) -
            ∑ l, low 1 ![E i, P, E j, Y l, E v] x *
              low k (Fin.snoc (Function.update Y l (E u)) z) x) := by
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun y : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
  intro P Y z hP hY hz x hx
  let S := fun Q : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Q) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ _ i
  have hcons {r : ℕ} (A : (y : M) → TangentSpace (𝓡 n) y)
      (Z : Fin r → (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hZ : ∀ j, S (Z j)) :
      ∀ j, S ((Fin.cons A Z : Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y) j) := by
    intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [Fin.cons_zero] using hA
    · simpa only [Fin.cons_succ] using hZ l
  have hsnoc {r : ℕ} (Z : Fin r → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) :
      ∀ j, S ((Fin.snoc Z z : Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y) j) := by
    intro j
    refine Fin.lastCases ?_ (fun l => ?_) j
    · simpa only [Fin.snoc_last] using hz
    · simpa only [Fin.snoc_castSucc] using hZ l
  have hthree (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : ∀ j, S (![A, B, C] j) := by
    intro j
    fin_cases j
    · exact hA
    · exact hB
    · exact hC
  have hfour (A B C W : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hW : S W) :
      ∀ j, S (![A, B, C, W] j) := by
    intro j
    fin_cases j
    · exact hA
    · exact hB
    · exact hC
    · exact hW
  have hup3 (A B C W : (y : M) → TangentSpace (𝓡 n) y) :
      Function.update (![A, B, C] : Fin 3 → (y : M) → TangentSpace (𝓡 n) y) 2 W =
        ![A, B, W] := by
    funext j
    fin_cases j <;> simp
  have hup4 (A B C Z W : (y : M) → TangentSpace (𝓡 n) y) :
      Function.update (![A, B, C, Z] : Fin 4 → (y : M) → TangentSpace (𝓡 n) y) 3 W =
        ![A, B, C, W] := by
    funext j
    fin_cases j <;> simp
  have hK0 (A B C : (y : M) → TangentSpace (𝓡 n) y) :
      K 0 ![A, B, C] = R A B C := rfl
  have hinsert (p q : ℕ)
      (Z : Fin (p + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (W : Fin (q + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (s : Fin (p + 3)) (hZ : ∀ j, S (Z j)) (hW : ∀ j, S (W j)) :
      g.inner x (K p (Function.update Z s (K q W)) x) (z x) =
        ∑ u, ∑ v, a x u v *
          (low q (Fin.snoc W (E v)) x *
            low p (Fin.snoc (Function.update Z s (E u)) z) x) := by
    have hh := curvature_iterated_insert_lowered_inverse_frame D p q x0
      (Fin.snoc Z z) W s (hsnoc Z hZ) hW hx
    simpa only [← Fin.snoc_update, low, Fin.init_snoc, Fin.snoc_last] using hh
  have hout (i j : Fin n) :
      g.inner x (R P (E i) (K (k + 1) (Fin.cons (E j) Y)) x) (z x) =
        ∑ u, ∑ v, a x u v *
          (low 0 ![P, E i, E u, z] x *
            low (k + 1) (Fin.snoc (Fin.cons (E j) Y) (E v)) x) := by
    have hh := hinsert 0 (k + 1) ![P, E i, P] (Fin.cons (E j) Y) 2
      (hthree P (E i) P hP (hE i) hP) (hcons (E j) Y (hE j) hY)
    simpa only [hup3, hK0, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, mul_comm] using hh
  have hinzero (i j : Fin n) :
      g.inner x (K (k + 1) (Fin.cons (R P (E i) (E j)) Y) x) (z x) =
        ∑ u, ∑ v, a x u v *
          (low 0 ![P, E i, E j, E v] x *
            low (k + 1) (Fin.snoc (Fin.cons (E u) Y) z) x) := by
    have hh := hinsert (k + 1) 0 (Fin.cons P Y) ![P, E i, E j] 0
      (hcons P Y hP hY) (hthree P (E i) (E j) hP (hE i) (hE j))
    simpa only [Fin.update_cons_zero, hK0, Matrix.Fin.snoc_vecCons,
      Matrix.Fin.snoc_vecEmpty] using hh
  have hin (i j : Fin n) (l : Fin (k + 3)) :
      g.inner x (K (k + 1)
          (Fin.cons (E j) (Function.update Y l (R P (E i) (Y l)))) x) (z x) =
        ∑ u, ∑ v, a x u v *
          (low 0 ![P, E i, Y l, E v] x *
            low (k + 1) (Fin.snoc (Fin.cons (E j) (Function.update Y l (E u))) z) x) := by
    have hh := hinsert (k + 1) 0 (Fin.cons (E j) Y) ![P, E i, Y l] l.succ
      (hcons (E j) Y (hE j) hY) (hthree P (E i) (Y l) hP (hE i) (hY l))
    simpa only [← Fin.cons_update, hK0, Matrix.Fin.snoc_vecCons,
      Matrix.Fin.snoc_vecEmpty] using hh
  have hdout (i j : Fin n) :
      g.inner x (K 1 ![E i, P, E j, K k Y] x) (z x) =
        ∑ u, ∑ v, a x u v *
          (low 1 ![E i, P, E j, E u, z] x * low k (Fin.snoc Y (E v)) x) := by
    have hh := hinsert 1 k ![E i, P, E j, P] Y 3
      (hfour (E i) P (E j) P (hE i) hP (hE j) hP) hY
    simpa only [hup4, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, mul_comm] using hh
  have hdin (i j : Fin n) (l : Fin (k + 3)) :
      g.inner x (K k (Function.update Y l (K 1 ![E i, P, E j, Y l])) x) (z x) =
        ∑ u, ∑ v, a x u v *
          (low 1 ![E i, P, E j, Y l, E v] x *
            low k (Fin.snoc (Function.update Y l (E u)) z) x) := by
    have hh := hinsert k 1 Y ![E i, P, E j, Y l] l hY
      (hfour (E i) P (E j) (Y l) (hE i) hP (hE j) (hY l))
    simpa only [Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty] using hh
  have hsum (f : Fin (k + 3) → Fin n → Fin n → ℝ) :
      (∑ l, ∑ u, ∑ v, f l u v) = ∑ u, ∑ v, ∑ l, f l u v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
  change g.inner x (∑ i, ∑ j, a x i j •
    (R P (E i) (K (k + 1) (Fin.cons (E j) Y)) x -
      K (k + 1) (Fin.cons (R P (E i) (E j)) Y) x -
      (∑ l, K (k + 1) (Fin.cons (E j) (Function.update Y l (R P (E i) (Y l)))) x) +
      K 1 ![E i, P, E j, K k Y] x +
      R P (E j) (K (k + 1) (Fin.cons (E i) Y)) x -
      (∑ l, K (k + 1) (Fin.cons (E i) (Function.update Y l (R P (E j) (Y l)))) x) -
      ∑ l, K k (Function.update Y l (K 1 ![E i, P, E j, Y l])) x)) (z x) = _
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_sub, map_add, map_sum, sub_apply, add_apply, sum_apply,
    hout, hinzero, hin, hdout, hdin]
  simp only [hsum, mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc]
  simp only [a, G, E, e, V, low, K]

end PoincareConjecture.Proofs.M03
