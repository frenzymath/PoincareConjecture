import PoincareConjecture.Proofs.M03.ConnectionFamily
import PoincareConjecture.Proofs.M03.MetricInverse
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv











set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u v

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_family_spatial_mvfderiv
    {f : ℝ → M → ℝ} {J : Set ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry f) (J ×ˢ U))
    {t : ℝ} (ht : t ∈ interior J) {x : M} (hx : x ∈ U)
    (a : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => mvfderiv (𝓡 n) (f s) x a)
      (mvfderiv (𝓡 n) (fun y => deriv (fun s => f s y) t) x a) t := by
  change EuclideanSpace ℝ (Fin n) at a
  let c := extChartAt (𝓡 n) x
  let H : ℝ × EuclideanSpace ℝ (Fin n) → ℝ := fun p => f p.1 (c.symm p.2)
  let Q : M → ℝ := fun y => deriv (fun s => f s y) t
  have hcx : c x ∈ c.target := mem_extChartAt_target x
  have hcsymm : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hxU : c.symm (c x) ∈ U := by rw [hcsymm]; exact hx
  have hf' := hf.mono (show interior J ×ˢ U ⊆ J ×ˢ U from
    fun _ hp => ⟨interior_subset hp.1, hp.2⟩)
  have hfm (s : ℝ) (hs : s ∈ interior J) (y : M) (hy : y ∈ U) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f s) y := by
    have hp := (hf' (s, y) ⟨hs, hy⟩).contMDiffAt
      ((isOpen_interior.prod hU).mem_nhds ⟨hs, hy⟩)
    exact hp.comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  have hc (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  have hH (s : ℝ) (hs : s ∈ interior J) (z : EuclideanSpace ℝ (Fin n))
      (hz : z ∈ c.target) (hzU : c.symm z ∈ U) : ContDiffAt ℝ ∞ H (s, z) := by
    have hp := (hf' (s, c.symm z) ⟨hs, hzU⟩).contMDiffAt
      ((isOpen_interior.prod hU).mem_nhds ⟨hs, hzU⟩)
    have hh := hp.comp (s, z)
      (contMDiffAt_fst.prodMk ((hc z hz).comp (s, z) contMDiffAt_snd))
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact hh.contDiffAt
  have hHtx := hH t ht (c x) hcx hxU
  have hD : DifferentiableAt ℝ (fderiv ℝ H) (t, c x) :=
    (hHtx.fderiv_right (m := 1)
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).differentiableAt (by norm_num)
  have htimeSlice (z : EuclideanSpace ℝ (Fin n)) :
      HasDerivAt (fun s : ℝ => (s, z)) (1, 0) t := by
    simpa using ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) z t)).hasDerivAt
  have hspace (s : ℝ) (hs : s ∈ interior J) :
      fderiv ℝ (fun z => H (s, z)) (c x) a =
        fderiv ℝ H (s, c x) (0, a) := by
    have hsH := (hH s hs (c x) hcx hxU).differentiableAt (by simp)
    have hd := hsH.hasFDerivAt.comp (c x)
      ((hasFDerivAt_const (𝕜 := ℝ) s (c x)).prodMk (hasFDerivAt_id (c x)))
    have hv := congrArg (fun L => L a) hd.fderiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply] using hv
  have htime : HasDerivAt (fun s => fderiv ℝ H (s, c x) (0, a))
      (fderiv ℝ (fderiv ℝ H) (t, c x) (1, 0) (0, a)) t := by
    have hd := hD.hasFDerivAt.comp_hasDerivAt t (htimeSlice (c x))
    simpa only [Function.comp_def, map_zero, add_zero] using
      hd.clm_apply (hasDerivAt_const t (0, a))
  have hspaceTime : fderiv ℝ (fun z => fderiv ℝ H (t, z) (1, 0)) (c x) a =
      fderiv ℝ (fderiv ℝ H) (t, c x) (0, a) (1, 0) := by
    have hd := hD.hasFDerivAt.comp (c x)
      ((hasFDerivAt_const (𝕜 := ℝ) t (c x)).prodMk (hasFDerivAt_id (c x)))
    have ha := hd.clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (1, (0 : EuclideanSpace ℝ (Fin n))) (c x))
    have hv := congrArg (fun L => L a) ha.fderiv
    simpa only [Function.comp_def, add_apply, ContinuousLinearMap.comp_apply,
      zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] using hv
  have hUnhds : c.symm ⁻¹' U ∈ 𝓝 (c x) :=
    (hc (c x) hcx).continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
  have hQchart : (Q ∘ c.symm) =ᶠ[𝓝 (c x)]
      (fun z => fderiv ℝ H (t, z) (1, 0)) := by
    filter_upwards [extChartAt_target_mem_nhds' hcx, hUnhds] with z hz hzU
    have hd := ((hH t ht z hz hzU).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      (htimeSlice z)
    exact hd.deriv
  have hQchartSmooth : ContDiffAt ℝ ∞ (Q ∘ c.symm) (c x) := by
    have hpartial := (hHtx.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := (1, (0 : EuclideanSpace ℝ (Fin n)))))
    have hs := hpartial.comp (c x) (contDiffAt_const.prodMk contDiffAt_id)
    exact hs.congr_of_eventuallyEq hQchart
  have hQ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ Q x := by
    have hs := hQchartSmooth.contMDiffAt.comp x
      (contMDiffAt_extChartAt (I := 𝓡 n) (x := x))
    apply hs.congr_of_eventuallyEq
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓡 n) x] with y hy
    change Q y = Q (c.symm (c y))
    rw [c.left_inv hy]
  have heid : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) c.symm (c x) =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) (c x)) := by
    simpa only [(𝓡 n).range_eq_univ, mfderivWithin_univ] using
      (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
  have hchart (q : M → ℝ) (hq : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ q x) :
      fderiv ℝ (q ∘ c.symm) (c x) a = mvfderiv (𝓡 n) q x a := by
    rw [← mfderiv_eq_fderiv]
    change mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (q ∘ c.symm) (c x) a = _
    rw [mvfderiv_comp_apply_of_eq (c x) (hq.mdifferentiableAt (by simp))
      ((hc (c x) hcx).mdifferentiableAt (by simp)) hcsymm a, heid]
    rfl
  have hslice : (fun s => mvfderiv (𝓡 n) (f s) x a) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ H (s, c x) (0, a)) := by
    filter_upwards [isOpen_interior.mem_nhds ht] with s hs
    rw [← hchart (f s) (hfm s hs x hx)]
    exact hspace s hs
  apply (htime.congr_of_eventuallyEq hslice).congr_deriv
  have hsymm := hHtx.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [hsymm.eq (1, 0) (0, a), ← hspaceTime, ← hQchart.fderiv_eq, hchart Q hQ]

open Bundle Manifold in
open scoped BigOperators in
set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem scalar_frame_laplacian_nonpos_of_isLocalMax
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet)
    (f : M → ℝ)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x0).baseSet)
    (hmax : IsLocalMax f x) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.connection Q y (P y)
    let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (q : M → ℝ) y =>
      mvfderiv (𝓡 n) q y (P y)
    (∑ i, ∑ j, a i j *
      (d (E i) (d (E j) f) x - d (N (E i) (E j)) f x)) ≤ 0 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection Q y (P y)
  let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (q : M → ℝ) y =>
    mvfderiv (𝓡 n) q y (P y)
  let C := fun q : M → ℝ => ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q e.baseSet
  let z := c x
  let F : V → ℝ := fun w => f (c.symm w)
  let H := fderiv ℝ (fderiv ℝ F) z
  have hxc : x ∈ c.source := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hx
  have hz : z ∈ c.target := c.map_source hxc
  have hbase {w : V} (hw : w ∈ c.target) : c.symm w ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hw
  have hcs {w : V} (hw : w ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, V) (𝓡 n) ∞ c.symm w :=
    (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
      (c.open_target.mem_nhds hw)
  have hF {w : V} (hw : w ∈ c.target) : ContDiffAt ℝ ∞ F w :=
    ((hf.contMDiffAt (e.open_baseSet.mem_nhds (hbase hw))).comp w (hcs hw)).contDiffAt
  have hFmax : IsLocalMax F z := by
    have hm : IsLocalMax f (c.symm z) := by
      simpa only [z, c.left_inv hxc] using hmax
    exact hm.comp_continuous (hcs hz).continuousAt
  have hD : DifferentiableAt ℝ (fderiv ℝ F) z :=
    ((hF hz).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hchart (q : M → ℝ) (hq : C q) {w : V} (hw : w ∈ c.target)
      (i : Fin n) : d (E i) q (c.symm w) =
        fderiv ℝ (fun u => q (c.symm u)) w (EuclideanSpace.single i 1) := by
    let y := c.symm w
    have hy : y ∈ e.baseSet := hbase hw
    have he : e.symmL ℝ y = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm w := by
      have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
        (c.map_target hw)
      simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
        mfderivWithin_univ] at hh
      change e.symmL ℝ y = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (c y) at hh
      rwa [c.right_inv hw] at hh
    have hframe : E i y = e.symmL ℝ y (EuclideanSpace.single i 1) := by
      calc
        E i y = e.basisAt cb hy i := e.localFrame_apply_of_mem_baseSet cb hy
        _ = e.symm y (EuclideanSpace.single i 1) := by
          simp only [Trivialization.basisAt, Module.Basis.map_apply, cb,
            OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
            Trivialization.linearEquivAt_symm_apply]
        _ = e.symmL ℝ y (EuclideanSpace.single i 1) := (e.symmL_apply hy _).symm
    have hfd : fderiv ℝ (fun u => q (c.symm u)) w (EuclideanSpace.single i 1) =
        mvfderiv (𝓡 n) q y (e.symmL ℝ y (EuclideanSpace.single i 1)) := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, V) (q ∘ c.symm) w (EuclideanSpace.single i 1) = _
      erw [mvfderiv_comp_apply w
        ((hq.contMDiffAt (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp))
        ((hcs hw).mdifferentiableAt (by simp)) (EuclideanSpace.single i 1), ← he]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) q y) hframe).trans hfd.symm
  have hdSmooth (j : Fin n) : C (d (E j) f) := by
    have hprod : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => f p.2) (univ ×ˢ e.baseSet) :=
      hf.comp contMDiffOn_snd (fun _ hp => hp.2)
    have hh := contMDiffOn_family_spatial_mvfderiv (f := fun _ : ℝ => f)
      e.open_baseSet hprod (E j)
      (e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb j)
    exact hh.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨mem_univ (0 : ℝ), hy⟩)
  have hfirst (i : Fin n) : mvfderiv (𝓡 n) f x (E i x) = 0 := by
    have hh := hchart f hf hz i
    rw [c.left_inv hxc] at hh
    change mvfderiv (𝓡 n) f x (E i x) = fderiv ℝ F z (EuclideanSpace.single i 1) at hh
    rw [hh, hFmax.fderiv_eq_zero]
    rfl
  have hzero (v : TangentSpace (𝓡 n) x) : mvfderiv (𝓡 n) f x v = 0 := by
    have hv := e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
      (s := FiberBundle.extend V v) hx
    rw [FiberBundle.extend_apply_self] at hv
    change v = ∑ i, theta i x v • E i x at hv
    rw [hv, map_sum]
    simp only [map_smul, smul_eq_mul, hfirst, mul_zero, Finset.sum_const_zero]
  have hsecond (i j : Fin n) : d (E i) (d (E j) f) x =
      H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    have hh := hchart (d (E j) f) (hdSmooth j) hz i
    rw [c.left_inv hxc] at hh
    have heq : (fun w => d (E j) f (c.symm w)) =ᶠ[𝓝 z]
        (fun w => fderiv ℝ F w (EuclideanSpace.single j 1)) :=
      Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hz)
        (fun w hw => hchart f hf hw j)
    rw [hh, heq.fderiv_eq]
    have heval := hD.hasFDerivAt.clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (EuclideanSpace.single j 1) z)
    have hv := congrArg (fun L => L (EuclideanSpace.single i 1)) heval.fderiv
    simpa only [H, add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero,
      zero_add, ContinuousLinearMap.flip_apply] using hv
  have hreal (phi : ℝ → ℝ) (hc : ContinuousAt phi 0) (hm : IsLocalMax phi 0) :
      deriv (deriv phi) 0 ≤ 0 := by
    by_contra hn
    have hp : 0 < deriv (deriv phi) 0 := lt_of_not_ge hn
    have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
    have heq : phi =ᶠ[𝓝 (0 : ℝ)] (fun _ => phi 0) :=
      eventuallyEq_of_isMinFilter_of_isMaxFilter hmin hm
    have hz0 : deriv (deriv phi) 0 = 0 := by
      rw [heq.deriv.deriv_eq]
      simp only [deriv_const']
    exact hp.ne' hz0
  have hdiag (v : V) : H v v ≤ 0 := by
    let line : ℝ → V := fun s => z + s • v
    have hl (s : ℝ) : HasDerivAt line v s := by
      simpa only [line, one_smul, id_eq] using!
        ((hasDerivAt_id s).smul_const v).const_add z
    have hlzero : line 0 = z := by simp only [line, zero_smul, add_zero]
    have hlmem : line 0 ∈ c.target := by rw [hlzero]; exact hz
    have hm : IsLocalMax (F ∘ line) 0 :=
      (show IsLocalMax F (line 0) by rw [hlzero]; exact hFmax).comp_continuous
        (hl 0).continuousAt
    have heq : deriv (F ∘ line) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => fderiv ℝ F (line s) v) := by
      filter_upwards [(hl 0).continuousAt.preimage_mem_nhds
        (c.open_target.mem_nhds hlmem)] with s hs
      exact (((hF hs).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (hl s)).deriv
    have hd : DifferentiableAt ℝ (fderiv ℝ F) (line 0) := by
      rw [hlzero]
      exact hD
    have heval := (hd.hasFDerivAt.comp_hasDerivAt 0 (hl 0)).clm_apply
      (hasDerivAt_const 0 v)
    have heval' : HasDerivAt (fun s => fderiv ℝ F (line s) v) (H v v) 0 := by
      simpa only [hlzero, H, map_zero, add_zero, Function.comp_def] using! heval
    have hsd : deriv (deriv (F ∘ line)) 0 = H v v :=
      heq.deriv_eq.trans heval'.deriv
    rw [← hsd]
    exact hreal (F ∘ line) ((hF hlmem).continuousAt.comp (hl 0).continuousAt) hm
  let b := g.orthonormalBasis x
  let w : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → V :=
    fun r => ∑ i : Fin n, theta i x (b r) • EuclideanSpace.single i 1
  have htrace (i j : Fin n) : a i j = ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hexpand (r : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      H (w r) (w r) = ∑ i : Fin n, ∑ j : Fin n,
        (theta i x (b r) * theta j x (b r)) *
          H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    dsimp only [w]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcontract : (∑ i, ∑ j, a i j *
      H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      ∑ r, H (w r) (w r) := by
    simp only [htrace, Finset.sum_mul, hexpand]
    calc
      _ = ∑ i : Fin n, ∑ r, ∑ j : Fin n,
          (theta i x (b r) * theta j x (b r)) *
            H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  change (∑ i, ∑ j, a i j *
    (d (E i) (d (E j) f) x - d (N (E i) (E j)) f x)) ≤ 0
  have hcorrection (i j : Fin n) : d (N (E i) (E j)) f x = 0 := hzero _
  simp only [hsecond, hcorrection, sub_zero]
  rw [hcontract]
  exact Finset.sum_nonpos (fun r _ => hdiag (w r))

theorem scalar_shifted_exp_bound_of_max_deriv
    {N : Type*} [TopologicalSpace N] [CompactSpace N]
    (q : ℝ → N → ℝ) {a b A L : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun p : ℝ × N => q p.1 p.2)
      (Icc a b ×ˢ univ))
    (hdiff : ∀ s ∈ Ioc a b, ∀ x : N,
      DifferentiableAt ℝ (fun r => q r x) s)
    (hmaxrate : ∀ s ∈ Ioc a b, ∀ x : N,
      IsLocalMax (q s) x →
        deriv (fun r => q r x) s ≤ L * (q s x + 1))
    (hinitial : ∀ x : N, q a x ≤ A) :
    ∀ x : N, q b x + 1 ≤ (A + 1) * Real.exp (L * (b - a)) := by
  classical
  intro x
  rcases eq_or_lt_of_le hab with heq | hab
  · subst b
    simpa only [sub_self, mul_zero, Real.exp_zero, mul_one] using
      add_le_add (hinitial x) (le_refl (1 : ℝ))
  let v := fun (s : ℝ) (y : N) => Real.exp (-L * (s - a)) * (q s y + 1)
  have hv : v b x ≤ A + 1 := by
    by_contra hnot
    have hgap : A + 1 < v b x := lt_of_not_ge hnot
    let eps := (v b x - (A + 1)) / (2 * (b - a))
    have heps : 0 < eps := div_pos (sub_pos.mpr hgap) (by linarith)
    have hepsmul : 2 * (eps * (b - a)) = v b x - (A + 1) := by
      dsimp only [eps]
      field_simp [ne_of_gt (sub_pos.mpr hab)]
    let w := fun p : ℝ × N => v p.1 p.2 - eps * (p.1 - a)
    let slab := Icc a b ×ˢ (univ : Set N)
    have hwgt : A + 1 < w (b, x) := by
      change A + 1 < v b x - eps * (b - a)
      linarith only [hepsmul, hgap]
    have hecont : Continuous (fun p : ℝ × N => Real.exp (-L * (p.1 - a))) := by
      fun_prop
    have helin : Continuous (fun p : ℝ × N => eps * (p.1 - a)) := by fun_prop
    have hwcont : ContinuousOn w slab :=
      (hecont.continuousOn.mul (hcont.add continuousOn_const)).sub helin.continuousOn
    have hslab : IsCompact slab := isCompact_Icc.prod isCompact_univ
    have hbx : (b, x) ∈ slab := ⟨⟨hab.le, le_rfl⟩, mem_univ x⟩
    obtain ⟨p, hp, hmax⟩ := hslab.exists_isMaxOn ⟨(b, x), hbx⟩ hwcont
    have hpgt : A + 1 < w p := hwgt.trans_le (isMaxOn_iff.mp hmax (b, x) hbx)
    have hpa : a < p.1 := by
      apply lt_of_le_of_ne hp.1.1
      intro heq
      have hwa : w p = q a p.2 + 1 := by
        dsimp only [w, v]
        rw [← heq]
        simp only [sub_self, mul_zero, Real.exp_zero, one_mul, sub_zero]
      rw [hwa] at hpgt
      exact (not_lt_of_ge (add_le_add (hinitial p.2) (le_refl (1 : ℝ)))) hpgt
    have hpt : p.1 ∈ Ioc a b := ⟨hpa, hp.1.2⟩
    have hqmax : IsLocalMax (q p.1) p.2 := by
      apply Filter.Eventually.of_forall
      intro y
      have hh := isMaxOn_iff.mp hmax (p.1, y) ⟨hp.1, mem_univ y⟩
      change Real.exp (-L * (p.1 - a)) * (q p.1 y + 1) - eps * (p.1 - a) ≤
        Real.exp (-L * (p.1 - a)) * (q p.1 p.2 + 1) - eps * (p.1 - a) at hh
      exact (add_le_add_iff_right 1).mp
        ((mul_le_mul_iff_right₀ (Real.exp_pos _)).mp ((sub_le_sub_iff_right _).mp hh))
    let rate := Real.exp (-L * (p.1 - a)) *
      (deriv (fun r => q r p.2) p.1 - L * (q p.1 p.2 + 1)) - eps
    have hwd : HasDerivAt (fun r => w (r, p.2)) rate p.1 := by
      have he := (((hasDerivAt_id p.1).sub_const a).const_mul (-L)).exp
      have hl := ((hasDerivAt_id p.1).sub_const a).const_mul eps
      convert (he.mul ((hdiff p.1 hpt p.2).hasDerivAt.add_const 1)).sub hl using 1
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
      have hh := hmaxrate p.1 hpt p.2 hqmax
      have hm := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-L * (p.1 - a))).le
        (sub_nonpos.mpr hh)
      dsimp only [rate]
      linarith only [hm, heps]
    exact (not_lt_of_ge hrateNonneg) hrateNeg
  calc
    q b x + 1 = Real.exp (L * (b - a)) * v b x := by
      dsimp only [v]
      rw [← mul_assoc, ← Real.exp_add]
      have he : L * (b - a) + -L * (b - a) = 0 := by ring
      rw [he, Real.exp_zero, one_mul]
    _ ≤ Real.exp (L * (b - a)) * (A + 1) :=
      mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
    _ = (A + 1) * Real.exp (L * (b - a)) := mul_comm _ _

theorem contDiffOn_fderiv_family
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set ℝ} {U : Set E} (hJ : IsOpen J) (hU : IsOpen U)
    (f : ℝ → E → F)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (J ×ˢ U) := by
  have hD := hf.fderiv_of_isOpen (hJ.prod hU) (m := ∞) (by simp)
  apply (hD.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ E))).congr
  intro p hp
  have hd := ((hf.contDiffAt ((hJ.prod hU).mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp p.2
      ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2))
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq,
    ContinuousLinearMap.inr] using hd.fderiv

theorem hasDerivAt_fderiv_family
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set ℝ} {U : Set E} (hJ : IsOpen J) (hU : IsOpen U)
    (f : ℝ → E → F)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ U))
    {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ U) :
    HasDerivAt (fun s => fderiv ℝ (f s) x)
      (fderiv ℝ (fun y => deriv (fun s => f s y) t) x) t := by
  let H := Function.uncurry f
  have hH (s : ℝ) (hs : s ∈ J) (y : E) (hy : y ∈ U) :
      ContDiffAt ℝ ∞ H (s, y) :=
    hf.contDiffAt ((hJ.prod hU).mem_nhds ⟨hs, hy⟩)
  have hD : DifferentiableAt ℝ (fderiv ℝ H) (t, x) :=
    ((hH t ht x hx).fderiv_right (m := 1)
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).differentiableAt (by norm_num)
  have htimeSlice (y : E) : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) t := by
    simpa using ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) y t)).hasDerivAt
  have hspace (s : ℝ) (hs : s ∈ J) :
      fderiv ℝ (f s) x = (fderiv ℝ H (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hd := ((hH s hs x hx).differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x))
    simpa only [H, Function.comp_def, Function.uncurry_apply_pair, id_eq,
      ContinuousLinearMap.inr] using hd.fderiv
  have htime : HasDerivAt
      (fun s => (fderiv ℝ H (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      ((fderiv ℝ (fderiv ℝ H) (t, x) (1, 0)).comp (ContinuousLinearMap.inr ℝ ℝ E)) t := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_zero, add_zero] using
      (hD.hasFDerivAt.comp_hasDerivAt t (htimeSlice x)).clm_comp
        (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ E))
  have hspaceTime (w : E) :
      fderiv ℝ (fun y => fderiv ℝ H (t, y) (1, 0)) x w =
        fderiv ℝ (fderiv ℝ H) (t, x) (0, w) (1, 0) := by
    have hd := hD.hasFDerivAt.comp x
      ((hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x))
    have ha := hd.clm_apply (hasFDerivAt_const (𝕜 := ℝ) (1, (0 : E)) x)
    have hv := congrArg (fun L => L w) ha.fderiv
    simpa only [Function.comp_def, add_apply, ContinuousLinearMap.comp_apply,
      zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] using hv
  have hQ : (fun y => deriv (fun s => f s y) t) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ H (t, y) (1, 0)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (((hH t ht y hy).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      (htimeSlice y)).deriv
  have hslice : (fun s => fderiv ℝ (f s) x) =ᶠ[𝓝 t]
      (fun s => (fderiv ℝ H (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact hspace s hs
  apply (htime.congr_of_eventuallyEq hslice).congr_deriv
  ext w
  change fderiv ℝ (fderiv ℝ H) (t, x) (1, 0) (0, w) = _
  have hsymm := (hH t ht x hx).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [hsymm.eq (1, 0) (0, w), ← hspaceTime, ← hQ.fderiv_eq]

theorem hasDerivAt_iteratedFDeriv_family
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set ℝ} {U : Set E} (hJ : IsOpen J) (hU : IsOpen U)
    (f : ℝ → E → F)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ U))
    (k : ℕ) {t : ℝ} (ht : t ∈ J) {x : E} (hx : x ∈ U) :
    HasDerivAt (fun s => iteratedFDeriv ℝ k (f s) x)
      (iteratedFDeriv ℝ k (fun y => deriv (fun s => f s y) t) x) t := by
  induction k generalizing F with
  | zero =>
    have hs : DifferentiableAt ℝ (fun s => f s x) t :=
      ((hf.contDiffAt ((hJ.prod hU).mem_nhds ⟨ht, hx⟩)).comp t
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
      |>.hasFDerivAt.comp_hasDerivAt t hs.hasDerivAt
  | succ k ih =>
    have hg := contDiffOn_fderiv_family hJ hU f hf
    have hd := ih (fun s => fderiv ℝ (f s)) hg
    have he : (fun y => deriv (fun s => fderiv ℝ (f s) y) t) =ᶠ[𝓝 x]
        (fun y => fderiv ℝ (fun z => deriv (fun s => f s z) t) y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hasDerivAt_fderiv_family hJ hU f hf ht hy).deriv
    have heq := (he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds
    have hc := (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.toContinuousLinearEquiv
      |>.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd
    simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      Function.comp_def, heq, iteratedFDeriv_succ_eq_comp_right] using hc

open Filter


theorem exists_contDiffOn_limit_of_iteratedFDeriv_time_lipschitz
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {a T : ℝ} (haT : a < T)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ s ∈ Ico a T, ContDiffOn ℝ ∞ (f s) U)
    (hjet : ∀ q : ℕ, ∀ K : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact K → K ⊆ U → ∃ L : ℝ, 0 ≤ L ∧
        ∀ s ∈ Ico a T, ∀ t ∈ Ico a T, ∀ x ∈ K,
          ‖iteratedFDeriv ℝ q (f t) x - iteratedFDeriv ℝ q (f s) x‖ ≤
            L * |t - s|) :
    ∃ fT : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ fT U ∧
      ∀ q : ℕ, ∀ K : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact K → K ⊆ U →
          (∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Ico a T, ∀ x ∈ K,
            ‖iteratedFDeriv ℝ q (f s) x - iteratedFDeriv ℝ q fT x‖ ≤
              L * (T - s)) ∧
          TendstoUniformlyOn (fun s x => iteratedFDeriv ℝ q (f s) x)
            (iteratedFDeriv ℝ q fT) (𝓝[<] T) K := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let l : Filter ℝ := 𝓝[<] T
  let Jq := fun (q : ℕ) (s : ℝ) (x : V) => iteratedFDeriv ℝ q (f s) x
  have hdom : ∀ᶠ s in l, s ∈ Ico a T := Ico_mem_nhdsLT haT
  have hid : Tendsto (fun s : ℝ => s) l (𝓝 T) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim (q : ℕ) (x : V) (hx : x ∈ U) :
      ∃ p : ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℝ,
        Tendsto (fun s => Jq q s x) l (𝓝 p) := by
    obtain ⟨L, hL, hb⟩ := hjet q {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    apply cauchy_map_iff_exists_tendsto.mp
    refine Metric.cauchy_iff.mpr ⟨inferInstance, ?_⟩
    intro ε hε
    let δ := ε / (2 * (L + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hc : max a (T - δ) < T := max_lt haT (by linarith)
    have hS : Ioo (max a (T - δ)) T ∈ l := Ioo_mem_nhdsLT hc
    refine ⟨(fun s => Jq q s x) '' Ioo (max a (T - δ)) T, image_mem_map hS, ?_⟩
    rintro v ⟨s, hs, rfl⟩ w ⟨t, ht, rfl⟩
    have hsJ : s ∈ Ico a T := ⟨(le_max_left _ _).trans hs.1.le, hs.2⟩
    have htJ : t ∈ Ico a T := ⟨(le_max_left _ _).trans ht.1.le, ht.2⟩
    have hsδ : T - s < δ := by have := (le_max_right a (T - δ)).trans_lt hs.1; linarith
    have htδ : T - t < δ := by have := (le_max_right a (T - δ)).trans_lt ht.1; linarith
    have habs : |s - t| ≤ (T - s) + (T - t) :=
      abs_le.mpr ⟨by linarith [ht.2], by linarith [hs.2]⟩
    calc
      dist (Jq q s x) (Jq q t x) = ‖Jq q s x - Jq q t x‖ := dist_eq_norm _ _
      _ ≤ L * |s - t| := hb t htJ s hsJ x (mem_singleton x)
      _ ≤ (L + 1) * |s - t| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (L + 1) * ((T - s) + (T - t)) := mul_le_mul_of_nonneg_left habs (by positivity)
      _ < (L + 1) * (2 * δ) := mul_lt_mul_of_pos_left (by linarith) (by positivity)
      _ = ε := by dsimp only [δ]; field_simp
  let P := fun (q : ℕ) (x : V) => if hx : x ∈ U then (hlim q x hx).choose else 0
  have hP (q : ℕ) (x : V) (hx : x ∈ U) :
      Tendsto (fun s => Jq q s x) l (𝓝 (P q x)) := by
    simpa only [P, dif_pos hx] using (hlim q x hx).choose_spec
  have hcontrol (q : ℕ) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ U) :
      (∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Ico a T, ∀ x ∈ K,
        ‖Jq q s x - P q x‖ ≤ L * (T - s)) ∧
      TendstoUniformlyOn (fun s x => Jq q s x) (P q) l K := by
    obtain ⟨L, hL, hb⟩ := hjet q K hK hKU
    have hbound (s : ℝ) (hs : s ∈ Ico a T) (x : V) (hx : x ∈ K) :
        ‖Jq q s x - P q x‖ ≤ L * (T - s) := by
      have hn : Tendsto (fun t => ‖Jq q s x - Jq q t x‖) l
          (𝓝 ‖Jq q s x - P q x‖) :=
        (tendsto_const_nhds.sub (hP q x (hKU hx))).norm
      have hr : Tendsto (fun t => L * |t - s|) l (𝓝 (L * |T - s|)) :=
        tendsto_const_nhds.mul ((hid.sub tendsto_const_nhds).abs)
      have hh : ‖Jq q s x - P q x‖ ≤ L * |T - s| :=
        le_of_tendsto_of_tendsto hn hr (by
          filter_upwards [hdom] with t ht
          simpa only [norm_sub_rev] using hb s hs t ht x hx)
      simpa only [abs_of_nonneg (sub_nonneg.mpr hs.2.le)] using hh
    refine ⟨⟨L, hL, hbound⟩, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let δ := ε / (L + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    filter_upwards [hdom, Ioo_mem_nhdsLT (show T - δ < T by linarith)] with s hs hsδ
    intro x hx
    have hnear : T - s < δ := by linarith [hsδ.1]
    calc
      dist (P q x) (Jq q s x) = ‖Jq q s x - P q x‖ := by rw [dist_eq_norm, norm_sub_rev]
      _ ≤ L * (T - s) := hbound s hs x hx
      _ ≤ (L + 1) * (T - s) := mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr hs.2.le)
      _ < (L + 1) * δ := mul_lt_mul_of_pos_left hnear (by positivity)
      _ = ε := by dsimp only [δ]; field_simp
  have hlocal (q : ℕ) : TendstoLocallyUniformlyOn (fun s x => Jq q s x) (P q) l U :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
      (fun K hKU hK => (hcontrol q K hK hKU).2)
  have hderiv (q : ℕ) (x : V) (hx : x ∈ U) :
      HasFDerivAt (P q) (P (q + 1) x).curryLeft x := by
    let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q + 1) => V) ℝ
    have hu := (tendstoLocallyUniformlyOn_iff_filter.mp (hlocal (q + 1))) x hx
    rw [hU.nhdsWithin_eq hx] at hu
    have hdu : TendstoUniformlyOnFilter
        (fun s y => (Jq (q + 1) s y).curryLeft)
        (fun y => (P (q + 1) y).curryLeft) l (𝓝 x) := by
      exact curry.toContinuousLinearEquiv.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformlyOnFilter hu
    apply hasFDerivAt_of_tendstoUniformlyOnFilter (f := fun s => Jq q s) hdu
    · filter_upwards [hdom.prod_mk (hU.mem_nhds hx)] with p hp
      have hd := ((hf p.1 hp.1).contDiffAt (hU.mem_nhds hp.2)).differentiableAt_iteratedFDeriv
        (show (q : ℕ∞ω) < ∞ from WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top q))
      have hd' := hd.hasFDerivAt
      rw [fderiv_iteratedFDeriv] at hd'
      exact hd'
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact hP q y hy
  let fT := fun x : V => (P 0 x).curry0
  have htaylor : HasFTaylorSeriesUpToOn (∞ : ℕ∞ω) fT (fun x q => P q x) U := by
    refine ⟨fun _ _ => rfl, ?_, ?_⟩
    · intro q _ x hx
      exact (hderiv q x hx).hasFDerivWithinAt
    · intro q _ x hx
      exact (hderiv q x hx).continuousAt.continuousWithinAt
  have hpeq (q : ℕ) (x : V) (hx : x ∈ U) : P q x = iteratedFDeriv ℝ q fT x := by
    have hh := htaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn
      (show (q : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top) hU.uniqueDiffOn hx
    simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using hh
  refine ⟨fT, htaylor.contDiffOn, ?_⟩
  intro q K hK hKU
  obtain ⟨⟨L, hL, hb⟩, hu⟩ := hcontrol q K hK hKU
  constructor
  · refine ⟨L, hL, ?_⟩
    intro s hs x hx
    simpa only [hpeq q x (hKU hx)] using hb s hs x hx
  · apply hu.congr_right
    intro x hx
    exact hpeq q x (hKU hx)

set_option synthInstance.maxHeartbeats 200000 in

theorem contDiffOn_of_spatial_jet_evolution
    {E F : Type u} {ι : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {a T b : ℝ}
    (haT : a < T) (hTb : T < b)
    (f r : ι → ℝ → E → F)
    (hspatial : ∀ i t, t ∈ Ioo a b → ContDiffOn ℝ ∞ (f i t) U)
    (hjets : ∀ i q, ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ q (f i p.1) p.2)
      (Ioo a b ×ˢ U))
    (htime : ∀ i q t, t ∈ Ioo a b → t ≠ T → ∀ x ∈ U,
      HasDerivAt (fun s => iteratedFDeriv ℝ q (f i s) x)
        (iteratedFDeriv ℝ q (r i t) x) t)
    (hr : ∀ k : ℕ,
      (∀ i q, ContDiffOn ℝ k
        (fun p : ℝ × E => iteratedFDeriv ℝ q (f i p.1) p.2)
        (Ioo a b ×ˢ U)) →
      ∀ i q, ContDiffOn ℝ k
        (fun p : ℝ × E => iteratedFDeriv ℝ q (r i p.1) p.2)
        (Ioo a b ×ˢ U)) :
    (∀ i q, ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedFDeriv ℝ q (f i p.1) p.2)
      (Ioo a b ×ˢ U)) ∧
    (∀ i, ContDiffOn ℝ ∞ (Function.uncurry (f i)) (Ioo a b ×ˢ U)) ∧
    (∀ i x, x ∈ U → HasDerivAt (fun s => f i s x) (r i T x) T) := by
  let W : Set (ℝ × E) := Ioo a b ×ˢ U
  let J := fun (i : ι) (q : ℕ) (p : ℝ × E) => iteratedFDeriv ℝ q (f i p.1) p.2
  let Q := fun (i : ι) (q : ℕ) (p : ℝ × E) => iteratedFDeriv ℝ q (r i p.1) p.2
  have hW : IsOpen W := isOpen_Ioo.prod hU
  have hQT (i : ι) (q : ℕ) : ContinuousOn (Q i q) W :=
    (hr 0 (fun i q => contDiffOn_zero.mpr (hjets i q)) i q).continuousOn
  have htimeFull (i : ι) (q : ℕ) (t : ℝ) (ht : t ∈ Ioo a b)
      (x : E) (hx : x ∈ U) :
      HasDerivAt (fun s => J i q (s, x)) (Q i q (t, x)) t := by
    by_cases htT : t = T
    · subst t
      have hc : ContinuousAt (fun s => J i q (s, x)) T :=
        ((hjets i q).continuousAt (hW.mem_nhds ⟨⟨haT, hTb⟩, hx⟩)).comp
          (continuousAt_id.prodMk continuousAt_const)
      have hqc : ContinuousAt (fun s => Q i q (s, x)) T :=
        ((hQT i q).continuousAt (hW.mem_nhds ⟨⟨haT, hTb⟩, hx⟩)).comp
          (continuousAt_id.prodMk continuousAt_const)
      have hl : HasDerivWithinAt (fun s => J i q (s, x)) (Q i q (T, x)) (Iic T) T := by
        apply hasDerivWithinAt_Iic_of_tendsto_deriv
          (s := Ioo a T)
          (fun s hs => (htime i q s ⟨hs.1, hs.2.trans hTb⟩ hs.2.ne x hx).differentiableAt.differentiableWithinAt)
          hc.continuousWithinAt (Ioo_mem_nhdsLT haT)
        apply (hqc.tendsto.mono_left nhdsWithin_le_nhds).congr'
        filter_upwards [Ioo_mem_nhdsLT haT] with s hs
        exact (htime i q s ⟨hs.1, hs.2.trans hTb⟩ hs.2.ne x hx).deriv.symm
      have hh : HasDerivWithinAt (fun s => J i q (s, x)) (Q i q (T, x)) (Ici T) T := by
        apply hasDerivWithinAt_Ici_of_tendsto_deriv
          (s := Ioo T b)
          (fun s hs => (htime i q s ⟨haT.trans hs.1, hs.2⟩ hs.1.ne' x hx).differentiableAt.differentiableWithinAt)
          hc.continuousWithinAt (Ioo_mem_nhdsGT hTb)
        apply (hqc.tendsto.mono_left nhdsWithin_le_nhds).congr'
        filter_upwards [Ioo_mem_nhdsGT hTb] with s hs
        exact (htime i q s ⟨haT.trans hs.1, hs.2⟩ hs.1.ne' x hx).deriv.symm
      simpa using hl.union hh
    · exact htime i q t ht htT x hx
  let timeMap (q : ℕ) : (E [×q]→L[ℝ] F) →L[ℝ] (ℝ →L[ℝ] (E [×q]→L[ℝ] F)) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (E [×q]→L[ℝ] F))
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  let spaceMap (q : ℕ) : (E [×(q + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] (E [×q]→L[ℝ] F)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q + 1) => E) F)
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  let D := fun (i : ι) (q : ℕ) (p : ℝ × E) =>
    (timeMap q (Q i q p)).coprod (spaceMap q (J i (q + 1) p))
  have hspace (i : ι) (q : ℕ) (t : ℝ) (ht : t ∈ Ioo a b)
      (x : E) (hx : x ∈ U) :
      HasFDerivAt (fun y => J i q (t, y)) (spaceMap q (J i (q + 1) (t, x))) x := by
    have hd := ((hspatial i t ht).contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (show (q : ℕ∞ω) < ∞ from WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top q))
    have hh := hd.hasFDerivAt
    rw [fderiv_iteratedFDeriv] at hh
    exact hh
  have htimeCont (i : ι) (q : ℕ) : ContinuousOn (fun p => timeMap q (Q i q p)) W :=
    (timeMap q).continuous.comp_continuousOn (hQT i q)
  have hspaceCont (i : ι) (q : ℕ) :
      ContinuousOn (fun p => spaceMap q (J i (q + 1) p)) W :=
    (spaceMap q).continuous.comp_continuousOn (hjets i (q + 1))
  have hfull (i : ι) (q : ℕ) {p : ℝ × E} (hp : p ∈ W) :
      HasFDerivAt (J i q) (D i q p) p := by
    exact (hasStrictFDerivAt_uncurry_coprod
      (f := fun t x => J i q (t, x))
      (f₁ := fun t x => timeMap q (Q i q (t, x)))
      (f₂ := fun t x => spaceMap q (J i (q + 1) (t, x)))
      (by
        filter_upwards [hW.mem_nhds hp] with z hz
        exact (htimeFull i q z.1 hz.1 z.2 hz.2).hasFDerivAt)
      (by
        filter_upwards [hW.mem_nhds hp] with z hz
        exact hspace i q z.1 hz.1 z.2 hz.2)
      ((htimeCont i q).continuousAt (hW.mem_nhds hp))
      ((hspaceCont i q).continuousAt (hW.mem_nhds hp))).hasFDerivAt
  have hfinite (k : ℕ) : ∀ i q, ContDiffOn ℝ k (J i q) W := by
    induction k with
    | zero => exact fun i q => contDiffOn_zero.mpr (hjets i q)
    | succ k ih =>
      have hQk := hr k ih
      intro i q
      have htk : ContDiffOn ℝ k (fun p => timeMap q (Q i q p)) W := by
        have hmap : ContDiff ℝ (k : ℕ∞ω) (timeMap q) :=
          ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E [×q]→L[ℝ] F)
            (F := ℝ →L[ℝ] (E [×q]→L[ℝ] F)) (timeMap q)
        have hq : ContDiffOn ℝ k (Q i q) W := hQk i q
        simpa only [Function.comp_def] using hmap.comp_contDiffOn hq
      have hxk : ContDiffOn ℝ k (fun p => spaceMap q (J i (q + 1) p)) W := by
        have hmap : ContDiff ℝ (k : ℕ∞ω) (spaceMap q) :=
          ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E [×(q + 1)]→L[ℝ] F)
            (F := E →L[ℝ] (E [×q]→L[ℝ] F)) (spaceMap q)
        simpa only [Function.comp_def] using hmap.comp_contDiffOn (ih i (q + 1))
      have hdk : ContDiffOn ℝ k (D i q) W := by
        have hh := (htk.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ ℝ E))).add
          (hxk.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ ℝ E)))
        simpa only [ContinuousLinearMap.comp_fst_add_comp_snd] using hh
      have hs : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (J i q) W := by
        apply (contDiffOn_succ_iff_fderiv_of_isOpen hW).mpr
        refine ⟨fun p hp => (hfull i q hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
        exact hdk.congr (fun p hp => (hfull i q hp).fderiv)
      simpa only [Nat.cast_add, Nat.cast_one] using hs
  have hinfty (i : ι) (q : ℕ) : ContDiffOn ℝ ∞ (J i q) W :=
    contDiffOn_infty.mpr (fun k => hfinite k i q)
  refine ⟨hinfty, ?_, ?_⟩
  · intro i
    have hh := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
      |>.contDiff.comp_contDiffOn (hinfty i 0)
    simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      Function.comp_def, continuousMultilinearCurryFin0_apply, J, iteratedFDeriv_zero_apply,
      Function.uncurry_def, W] using hh
  · intro i x hx
    have hh := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
      |>.hasFDerivAt.comp_hasDerivAt T (htimeFull i 0 T ⟨haT, hTb⟩ x hx)
    simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      Function.comp_def, continuousMultilinearCurryFin0_apply, J, Q, iteratedFDeriv_zero_apply] using hh

theorem contDiffOn_fderiv_family_of_isOpen_spatial
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set ℝ} {U : Set E} (hU : IsOpen U)
    (f : ℝ → E → F)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ U)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (J ×ˢ U) := by
  have haux : ContDiffOn ℝ ∞
      (Function.uncurry (fun (p : ℝ × E) (y : E) => f p.1 y))
      ((J ×ˢ U) ×ˢ U) :=
    hf.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
      (fun p hp => ⟨hp.1.1, hp.2⟩)
  have hd : ContDiffOn ℝ ∞
      (fun p : ℝ × E => fderivWithin ℝ (f p.1) U p.2) (J ×ˢ U) := by
    intro p hp
    exact (haux (p, p.2) ⟨hp, hp.2⟩).fderivWithin
      (g := fun p : ℝ × E => p.2) contDiffWithinAt_snd hU.uniqueDiffOn
      (by simp) hp (fun p hp => hp.2)
  exact hd.congr (fun p hp => (fderivWithin_of_isOpen hU hp.2).symm)

set_option synthInstance.maxHeartbeats 200000 in
theorem contDiffOn_iteratedFDeriv_family_of_isOpen_spatial
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set ℝ} {U : Set E} (hU : IsOpen U)
    (f : ℝ → E → F)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedFDeriv ℝ q (f p.1) p.2) (J ×ˢ U) := by
  intro q
  induction q with
  | zero =>
    let L : F →L[ℝ] (E [×0]→L[ℝ] F) :=
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    change ContDiffOn ℝ ∞ (fun p : ℝ × E => L (f p.1 p.2)) (J ×ˢ U)
    exact L.contDiff.comp_contDiffOn hf
  | succ q ih =>
    have hd := contDiffOn_fderiv_family_of_isOpen_spatial hU
      (fun t x => iteratedFDeriv ℝ q (f t) x) ih
    let L : (E →L[ℝ] (E [×q]→L[ℝ] F)) →L[ℝ] (E [×(q + 1)]→L[ℝ] F) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q + 1) => E) F).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap
    change ContDiffOn ℝ ∞
      (fun p : ℝ × E => L (fderiv ℝ (iteratedFDeriv ℝ q (f p.1)) p.2)) (J ×ˢ U)
    exact L.contDiff.comp_contDiffOn hd

end PoincareConjecture.Proofs.M03
