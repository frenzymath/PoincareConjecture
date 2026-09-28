import PoincareConjecture.Proofs.M03.FamilyTangentTimeDerivative
import PoincareConjecture.Proofs.M03.ScalarMixedDerivative
import PoincareConjecture.Proofs.M03.MetricPairRegularity
import PoincareConjecture.Proofs.M03.CurvatureVectorTime










set_option autoImplicit false
set_option maxHeartbeats 2400000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_ricciFlow_connection_moving_field
    {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (X : (x : M) → TangentSpace (𝓡 n) x)
    (V : ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hV : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) p.2 (V p.1 p.2)) (J ×ˢ U))
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let dotV := fun y => deriv (fun s => V s y) t
    let C := fun s => (F.connection s).connection (V s) x (X x)
    let C0 := fun s => (F.connection s).connection (V t) x (X x)
    HasDerivAt C
      (deriv C0 t + (F.connection t).connection dotV x (X x)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let dotV := fun y => deriv (fun s => V s y) t
  let C := fun s => (F.connection s).connection (V s) x (X x)
  let C0 := fun s => (F.connection s).connection (V t) x (X x)
  have htJ : J ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  have hVs (s : ℝ) (hs : s ∈ J) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (V s)) U :=
    hV.comp (contMDiffOn_const.prodMk contMDiffOn_id) (fun _ hy => ⟨hs, hy⟩)
  have hpair {S : Set M}
      (A B : (p : ℝ × M) → TangentSpace (𝓡 n) p.2)
      (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (A p))
        (J ×ˢ S))
      (hB : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (B p))
        (J ×ˢ S)) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p => (F.metric p.1).inner p.2 (A p) (B p)) (J ×ˢ S) := by
    have hp := ContMDiffOn.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
      (E₁ := fun y : M => TangentSpace (𝓡 n) y)
      (E₂ := fun y : M => TangentSpace (𝓡 n) y) (E₃ := fun _ : M => ℝ)
      (ψ := fun p : ℝ × M => (F.metric p.1).inner p.2) (b := Prod.snd)
      (F.smooth.mono (Set.prod_mono subset_rfl (subset_univ S))) hA hB
    intro p hpS
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (hp p hpS)).2
  have hC : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        ((F.connection p.1).connection (V p.1) p.2 (X p.2))) (J ×ˢ U) := by
    apply contMDiffOn_family_vector_of_metric_pair F.smooth hU
    intro S hS hSU W hW
    have hVS := hV.mono (Set.prod_mono subset_rfl hSU)
    have hWS := hW.comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
      (fun (p : ℝ × M) (hp : p ∈ J ×ˢ S) => hp.2)
    have hAS := contMDiffOn_connection_family_apply F.smooth F.connection
      hS W X hW (hX.mono hSU)
    have hp := hpair _ _ hVS hWS
    have hd := contMDiffOn_family_spatial_mvfderiv
      (f := fun s y => (F.metric s).inner y (V s y) (W y)) hS hp X (hX.mono hSU)
    apply (hd.sub (hpair _ _ hVS hAS)).congr
    intro p hpS
    have hVp := ((hVs p.1 hpS.1).contMDiffAt
      (hU.mem_nhds (hSU hpS.2))).mdifferentiableAt (by simp)
    have hWp := (hW.contMDiffAt (hS.mem_nhds hpS.2)).mdifferentiableAt (by simp)
    rw [(F.connection p.1).mvfderiv_inner X (V p.1) W hVp hWp]
    ring
  have hC0 := contMDiffOn_connection_family_apply F.smooth F.connection
    hU (V t) X (hVs t (interior_subset ht)) hX
  have hdot := family_tangent_time_derivative (F.metric 0) hU V hV ht
  have hCd : HasDerivAt C (deriv C t) t :=
    (family_tangent_time_derivative (F.metric 0) hU
      (fun s y => (F.connection s).connection (V s) y (X y)) hC ht).1 x hx
  have hC0d : HasDerivAt C0 (deriv C0 t) t :=
    (family_tangent_time_derivative (F.metric 0) hU
      (fun s y => (F.connection s).connection (V t) y (X y)) hC0 ht).1 x hx
  have htest (z : TangentSpace (𝓡 n) x) :
      (F.metric t).inner x (deriv C t - deriv C0 t) z =
        (F.metric t).inner x ((F.connection t).connection dotV x (X x)) z := by
    obtain ⟨Sz, hSz, hz⟩ := FiberBundle.exists_contMDiffOn_extend
      (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) z
    obtain ⟨S, hSsub, hS, hxS⟩ := mem_nhds_iff.mp
      (Filter.inter_mem (hU.mem_nhds hx) hSz)
    have hSU : S ⊆ U := fun _ hy => (hSsub hy).1
    let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z
    have hW : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) S :=
      hz.mono (fun _ hy => (hSsub hy).2)
    have hWx : W x = z := FiberBundle.extend_apply_self (EuclideanSpace ℝ (Fin n)) z
    let L := fun s y => V s y - V t y
    let A := fun s y => (F.connection s).connection W y (X y)
    let f := fun s y => (F.metric s).inner y (L s y) (W y)
    have hVS := hV.mono (Set.prod_mono subset_rfl hSU)
    have hVtS := ((hVs t (interior_subset ht)).mono hSU).comp
      (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
      (fun (p : ℝ × M) (hp : p ∈ J ×ˢ S) => hp.2)
    have hWS := hW.comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
      (fun (p : ℝ × M) (hp : p ∈ J ×ˢ S) => hp.2)
    have hp := hpair _ _ hVS hWS
    have hp0 := hpair _ _ hVtS hWS
    have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (Function.uncurry f) (J ×ˢ S) := by
      apply (hp.sub hp0).congr
      intro p _hp
      change (F.metric p.1).inner p.2 (V p.1 p.2 - V t p.2) (W p.2) = _
      rw [map_sub ((F.metric p.1).inner p.2), sub_apply]
    have hAd := (family_tangent_time_derivative (F.metric 0) hS A
      (contMDiffOn_connection_family_apply F.smooth F.connection
        hS W X hW (hX.mono hSU)) ht).1 x hxS
    have hfderiv (y : M) (hy : y ∈ S) :
        HasDerivAt (fun s => f s y) ((F.metric t).inner y (dotV y) (W y)) t := by
      let : NormedAddCommGroup (TangentSpace (𝓡 n) y →L[ℝ] ℝ) := inferInstance
      let : NormedSpace ℝ (TangentSpace (𝓡 n) y →L[ℝ] ℝ) := inferInstance
      let G := fun s => (F.metric s).inner y
      have hG : HasDerivAt G (deriv G t) t :=
        (((contDiffOn_family_metric_inner_time F.smooth y).contDiffAt htJ).differentiableAt
          (by simp)).hasDerivAt
      have hL := (hdot.1 y (hSU hy)).sub (hasDerivAt_const t (V t y))
      have hd := (hG.clm_apply hL).clm_apply (hasDerivAt_const t (W y))
      simpa only [f, L, G, dotV, Pi.sub_apply, sub_self, sub_zero, map_zero, add_zero, zero_add,
        add_apply, zero_apply] using hd
    have hspaceEq : (fun y => deriv (fun s => f s y) t) =ᶠ[𝓝 x]
        (fun y => (F.metric t).inner y (dotV y) (W y)) := by
      filter_upwards [hS.mem_nhds hxS] with y hy
      exact (hfderiv y hy).deriv
    have hdf := hasDerivAt_family_spatial_mvfderiv hS hf ht hxS (X x)
    have hderivEq :
        mvfderiv (𝓡 n) (fun y => deriv (fun s => f s y) t) x (X x) =
          mvfderiv (𝓡 n) (fun y => (F.metric t).inner y (dotV y) (W y)) x (X x) := by
      simp only [mvfderiv, hspaceEq.mfderiv_eq]
      rw [(hfderiv x hxS).deriv]
      rfl
    rw [hderivEq] at hdf
    have hdotx := (hdot.2.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hWx' := (hW.contMDiffAt (hS.mem_nhds hxS)).mdifferentiableAt (by simp)
    rw [(F.connection t).mvfderiv_inner X dotV W hdotx hWx'] at hdf
    let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
    let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
    let G := fun s => (F.metric s).inner x
    have hG : HasDerivAt G (deriv G t) t :=
      (((contDiffOn_family_metric_inner_time F.smooth x).contDiffAt htJ).differentiableAt
        (by simp)).hasDerivAt
    have hL := (hdot.1 x hx).sub (hasDerivAt_const t (V t x))
    have hq : HasDerivAt (fun s => G s (L s x) (A s x))
        (G t (dotV x) (A t x)) t := by
      have hd := (hG.clm_apply hL).clm_apply hAd
      simpa only [L, dotV, Pi.sub_apply, sub_self, sub_zero, map_zero, add_zero, zero_add,
        add_apply, zero_apply] using hd
    have hzero : C t - C0 t = 0 := sub_self _
    have hleft : HasDerivAt (fun s => G s (C s - C0 s) (W x))
        (G t (deriv C t - deriv C0 t) (W x)) t := by
      have hd := (hG.clm_apply (hCd.sub hC0d)).clm_apply (hasDerivAt_const t (W x))
      simpa only [Pi.sub_apply, hzero, map_zero, add_zero, zero_add, add_apply, zero_apply] using hd
    have heq : (fun s => G s (C s - C0 s) (W x)) =ᶠ[𝓝 t]
        (fun s => mvfderiv (𝓡 n) (f s) x (X x) - G s (L s x) (A s x)) := by
      filter_upwards [htJ] with s hs
      have hsp := hp.comp (contMDiffOn_const.prodMk contMDiffOn_id)
        (fun _ hy => ⟨hs, hy⟩)
      have hsp0 := hp0.comp (contMDiffOn_const.prodMk contMDiffOn_id)
        (fun _ hy => ⟨hs, hy⟩)
      have hspx := (hsp.contMDiffAt (hS.mem_nhds hxS)).mdifferentiableAt (by simp)
      have hsp0x := (hsp0.contMDiffAt (hS.mem_nhds hxS)).mdifferentiableAt (by simp)
      dsimp only [Function.comp_def, id_eq] at hspx hsp0x
      have hVx := ((hVs s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
      have hVtx := ((hVs t (interior_subset ht)).contMDiffAt
        (hU.mem_nhds hx)).mdifferentiableAt (by simp)
      have hfeq : f s = fun y => (F.metric s).inner y (V s y) (W y) -
          (F.metric s).inner y (V t y) (W y) := by
        funext y
        simp only [f, L, map_sub, sub_apply]
      rw [hfeq, mvfderiv_fun_sub hspx hsp0x, sub_apply,
        (F.connection s).mvfderiv_inner X (V s) W hVx hWx',
        (F.connection s).mvfderiv_inner X (V t) W hVtx hWx']
      dsimp only [G, C, C0, L, A]
      simp only [map_sub, sub_apply]
      ring
    have hh := hleft.unique ((hdf.sub hq).congr_of_eventuallyEq heq)
    dsimp only [G, A] at hh
    rw [hWx] at hh
    linarith only [hh]
  have heq : deriv C t - deriv C0 t =
      (F.connection t).connection dotV x (X x) := by
    apply sub_eq_zero.mp
    by_contra hne
    have hz := htest (deriv C t - deriv C0 t -
      (F.connection t).connection dotV x (X x))
    have hzero : (F.metric t).inner x
        (deriv C t - deriv C0 t - (F.connection t).connection dotV x (X x))
        (deriv C t - deriv C0 t - (F.connection t).connection dotV x (X x)) = 0 := by
      rw [map_sub ((F.metric t).inner x), sub_apply, hz, sub_self]
    exact ((F.metric t).pos x _ hne).ne' hzero
  apply hCd.congr_deriv
  exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)

end PoincareConjecture.Proofs.M03
