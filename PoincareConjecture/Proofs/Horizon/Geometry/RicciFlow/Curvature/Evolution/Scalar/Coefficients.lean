import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.SpatialCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.RicciRegularity
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter Function

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {U : Set M}

set_option backward.isDefEq.respectTransparency false in
private theorem contMDiffOn_flow_metric_pairing (F : RicciFlow n M J)
    {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (F.metric p.1).inner p.2 (X p.2) (Y p.2)) (J ×ˢ U) := by
  have hX' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.2))
      (J ×ˢ U) := hX.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
  have hY' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.2))
      (J ×ˢ U) := hY.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
  intro p hp
  have hm := (F.smooth p ⟨hp.1, mem_univ p.2⟩).mono
    (show J ×ˢ U ⊆ J ×ˢ univ from fun q hq ↦ ⟨hq.1, mem_univ q.2⟩)
  have he : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun q ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
        ((F.metric q.1).inner q.2 (X q.2) (Y q.2))) (J ×ˢ U) p :=
    hm.clm_bundle_apply₂ (hX' p hp) (hY' p hp)
  simp only [Bundle.contMDiffWithinAt_totalSpace] at he
  exact he.2

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem continuousOn_timeDependent_hessianOnFields (F : RicciFlow n M J)
    {q : ℝ × M → ℝ} {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hU : IsOpen U)
    (hq : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ q (J ×ˢ U))
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContinuousOn
      (fun p : ℝ × M ↦
        (F.connection p.1).hessianOnFields (fun y ↦ q (p.1, y)) X Y p.2) (J ×ˢ U) := by
  have hfirst := (contMDiffOn_mvfderiv_spatial hU
    (contMDiffOn_mvfderiv_spatial hU hq hY) hX).continuousOn
  intro p0 hp0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric p0.1).toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let t := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p0.2
  let O := U ∩ t.baseSet
  have hO : IsOpen O := hU.inter t.open_baseSet
  have hxT : p0.2 ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' p0.2
  have hpO : p0 ∈ J ×ˢ O := ⟨hp0.1, hp0.2, hxT⟩
  let S := fun y ↦ t.symmL ℝ y
  have hSext (v : E) {y : M} (hy : y ∈ t.baseSet) :
      FiberBundle.extend E (S p0.2 v) y = S y v := by
    change t.symm y (t ⟨p0.2, t.symmL ℝ p0.2 v⟩).2 = t.symmL ℝ y v
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) t hxT,
      t.continuousLinearMapAt_symmL hxT, t.symmL_apply hy]
  have hS (v : E) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (fun y ↦ S y v)) O := by
    apply ((contMDiffOn_extend_baseSet (S p0.2 v)).mono inter_subset_right).congr
    intro y hy
    exact congrArg (Bundle.TotalSpace.mk y) (hSext v hy.2).symm
  let Z := fun p : ℝ × M ↦ (F.connection p.1).connection Y p.2 (X p.2)
  let B : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    ((F.metric p.1).inner p.2).bilinearComp (S p.2) (S p.2)
  let P : ℝ × M → E →L[ℝ] ℝ := fun p ↦
    ((F.metric p.1).inner p.2 (Z p)).comp (S p.2)
  let D : ℝ × M → E →L[ℝ] ℝ := fun p ↦
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ q (p.1, y)) p.2).comp (S p.2)
  have hB : ContinuousOn B (J ×ˢ O) := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro w
    exact (contMDiffOn_flow_metric_pairing F (hS v) (hS w)).continuousOn
  have hP : ContinuousOn P (J ×ˢ O) := by
    apply continuousOn_clm_apply.mpr
    intro v
    exact (contMDiffOn_flow_connection_pairing F hO
      (hX.mono inter_subset_left) (hY.mono inter_subset_left) (hS v)).continuousOn
  have hD : ContinuousOn D (J ×ˢ O) := by
    apply continuousOn_clm_apply.mpr
    intro v
    exact (contMDiffOn_mvfderiv_spatial hO
      (hq.mono (prod_mono Subset.rfl inter_subset_left))
      (hS v)).continuousOn
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let A : ℝ × M → E →L[ℝ] E := fun p ↦ Q.toContinuousLinearMap.comp (B p)
  have hA : ContinuousOn A (J ×ˢ O) := continuousOn_const.clm_comp hB
  have hInv {p : ℝ × M} (hp : p.2 ∈ t.baseSet) : (A p).IsInvertible := by
    have hz (v : E) (hv : A p v = 0) : v = 0 := by
      have hBv : B p v = 0 := Q.injective (by simpa [A] using hv)
      have hi : (F.metric p.1).inner p.2 (S p.2 v) (S p.2 v) = 0 := by
        simpa [B] using congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hBv
      have hSv : S p.2 v = 0 := by
        by_contra hne
        exact (ne_of_gt ((F.metric p.1).pos p.2 _ hne)) hi
      have hv' := congrArg (t.continuousLinearMapAt ℝ p.2) hSv
      simpa only [S, t.continuousLinearMapAt_symmL hp, map_zero] using hv'
    have hinj : Function.Injective (A p) := by
      intro v w h
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub, h, sub_self]
    have hsurj : Function.Surjective (A p) := (LinearMap.injective_iff_surjective).mp hinj
    exact ⟨(LinearEquiv.ofBijective (A p).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      by ext v; rfl⟩
  have hInvDiff : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (A p0) :=
    (hInv hxT).contDiffAt_map_inverse
  have hAi : ContinuousWithinAt (fun p ↦ (A p).inverse) (J ×ˢ O) p0 :=
    hInvDiff.continuousAt.comp_continuousWithinAt (hA p0 hpO)
  have hrec : ContinuousWithinAt (fun p ↦ (A p).inverse (Q (P p))) (J ×ˢ O) p0 :=
    hAi.clm_apply (Q.continuous.continuousAt.comp_continuousWithinAt (hP p0 hpO))
  have hsecond : ContinuousWithinAt (fun p : ℝ × M ↦ mvfderiv (𝓡 n) (fun y ↦ q (p.1, y)) p.2 (Z p))
      (J ×ˢ O) p0 := by
    apply ((hD p0 hpO).clm_apply hrec).congr_of_mem ?_ hpO
    intro p hp
    have he : (A p).inverse (Q (P p)) = t.continuousLinearMapAt ℝ p.2 (Z p) := by
      apply (hInv hp.2.2).inverse_apply_eq.mpr
      change Q (P p) = Q (B p (t.continuousLinearMapAt ℝ p.2 (Z p)))
      apply congrArg Q
      ext v
      change (F.metric p.1).inner p.2 (Z p) (S p.2 v) =
        (F.metric p.1).inner p.2 (S p.2 (t.continuousLinearMapAt ℝ p.2 (Z p))) (S p.2 v)
      rw [t.symmL_continuousLinearMapAt hp.2.2]
    change mvfderiv (𝓡 n) (fun y ↦ q (p.1, y)) p.2 (Z p) = D p ((A p).inverse (Q (P p)))
    rw [he]
    change mvfderiv (𝓡 n) (fun y ↦ q (p.1, y)) p.2 (Z p) =
      mvfderiv (𝓡 n) (fun y ↦ q (p.1, y)) p.2 (S p.2 (t.continuousLinearMapAt ℝ p.2 (Z p)))
    rw [t.symmL_continuousLinearMapAt hp.2.2]
  have hH : ContinuousWithinAt
      (fun p : ℝ × M ↦
        (F.connection p.1).hessianOnFields (fun y ↦ q (p.1, y)) X Y p.2) (J ×ˢ O) p0 :=
    ((hfirst p0 hp0).mono (prod_mono Subset.rfl inter_subset_left)).sub hsecond
  apply hH.mono_of_mem_nhdsWithin
  have hn : (Prod.snd ⁻¹' t.baseSet : Set (ℝ × M)) ∈ 𝓝 p0 :=
    continuous_snd.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hxT)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with p hp hpt
  exact ⟨hp.1, hp.2, hpt⟩

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_flow_timeDependentLaplacian (F : RicciFlow n M J)
    {q : ℝ × M → ℝ}
    (hq : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ q (J ×ˢ univ)) :
    ContinuousOn
      (fun p : ℝ × M ↦ (F.connection p.1).laplacian (fun y ↦ q (p.1, y)) p.2)
      (J ×ˢ univ) := by
  classical
  have hslice (s : ℝ) (hs : s ∈ J) :
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ q (s, y)) := by
    have hmap : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M ↦ (s, y)) := contMDiff_const.prodMk contMDiff_id
    exact ContMDiffOn.comp_contMDiff (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ).prod (𝓡 n))
      (I'' := 𝓘(ℝ, ℝ)) (f := fun y : M ↦ (s, y)) (g := q)
      hq hmap (fun y ↦ ⟨hs, mem_univ y⟩)
  let T : (p : ℝ × M) → MultilinearMap ℝ (fun _ : Fin 2 ↦ TangentSpace (𝓡 n) p.2) ℝ :=
    fun p ↦ if hp : p.1 ∈ J then
      Classical.choose ((isSmoothCovariantTensor_hessian (F.connection p.1)
        (hslice p.1 hp)).1 p.2)
      else 0
  have hT (p : ℝ × M) (hp : p.1 ∈ J) (v : Fin 2 → TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).hessian (fun y ↦ q (p.1, y)) p.2 (v 0) (v 1) = T p v := by
    simp only [T, dif_pos hp]
    exact Classical.choose_spec ((isSmoothCovariantTensor_hessian (F.connection p.1)
      (hslice p.1 hp)).1 p.2) v
  have htrace := continuousOn_flow_tensorTrace F isOpen_univ T (by
    intro V hV hVU X Y hX hY
    apply (continuousOn_timeDependent_hessianOnFields F hV
      (hq.mono (prod_mono Subset.rfl hVU)) hX hY).congr
    intro p hp
    change T p ![X p.2, Y p.2] =
      (F.connection p.1).hessianOnFields (fun y ↦ q (p.1, y)) X Y p.2
    calc
      T p ![X p.2, Y p.2] =
          (F.connection p.1).hessian (fun y ↦ q (p.1, y)) p.2 (X p.2) (Y p.2) :=
        (hT p hp.1 ![X p.2, Y p.2]).symm
      _ = _ := (hessianOnFields_eq_hessian_of_contMDiff (F.connection p.1)
        (hslice p.1 hp.1) hV hX hY hp.2).symm)
  apply htrace.congr
  intro p hp
  apply Finset.sum_congr rfl
  intro i _
  exact hT p hp.1
    ![(F.metric p.1).orthonormalBasis p.2 i, (F.metric p.1).orthonormalBasis p.2 i]

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_flow_ricciNormSq (F : RicciFlow n M J) :
    ContinuousOn (fun p : ℝ × M ↦ (F.connection p.1).ricciNormSq p.2)
      (J ×ˢ Set.univ) := by
  classical
  let I := 𝓘(ℝ, ℝ).prod (𝓡 n)
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex F.interval.convex
    (F.interval.convex.nontrivial_iff_nonempty_interior.mp F.nontrivial)
  have hclm {E' G : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
      [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
      {L : ℝ × M → E' →L[ℝ] G} {V : Set (ℝ × M)} {p : ℝ × M}
      (hL : ∀ v : E', ContMDiffWithinAt I 𝓘(ℝ, G) ∞ (fun q ↦ L q v) V p) :
      ContMDiffWithinAt I 𝓘(ℝ, E' →L[ℝ] G) ∞ L V p := by
    let d := Module.finrank ℝ E'
    have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
    let e1 := ContinuousLinearEquiv.ofFinrankEq hd
    let e2 := (e1.arrowCongr (1 : G ≃L[ℝ] G)).trans (ContinuousLinearEquiv.piRing (Fin d))
    have hc : ContMDiffWithinAt I 𝓘(ℝ, Fin d → G) ∞ (fun q ↦ e2 (L q)) V p := by
      apply contMDiffWithinAt_pi_space.mpr
      intro i
      exact hL _
    have h := e2.symm.toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt p hc
    have heq : (fun q ↦ e2.symm (e2 (L q))) = L := by
      funext q
      exact e2.symm_apply_apply (L q)
    have h' : ContMDiffWithinAt I 𝓘(ℝ, E' →L[ℝ] G) ∞
        (fun q ↦ e2.symm (e2 (L q))) V p := by
      simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe] using! h
    rwa [heq] at h'
  intro p0 hp0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric p0.1).toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let t := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p0.2
  let V := J ×ˢ t.baseSet
  have hxT : p0.2 ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' p0.2
  have hpV : p0 ∈ V := ⟨hp0.1, hxT⟩
  let S := fun y ↦ t.symmL ℝ y
  have hSext (v : E) {y : M} (hy : y ∈ t.baseSet) :
      FiberBundle.extend E (S p0.2 v) y = S y v := by
    change t.symm y (t ⟨p0.2, t.symmL ℝ p0.2 v⟩).2 = t.symmL ℝ y v
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) t hxT,
      t.continuousLinearMapAt_symmL hxT, t.symmL_apply hy]
  have hS (v : E) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (fun y ↦ S y v)) t.baseSet := by
    apply (contMDiffOn_extend_baseSet (S p0.2 v)).congr
    intro y hy
    exact congrArg (Bundle.TotalSpace.mk y) (hSext v hy).symm
  have hSP (v : E) : ContMDiffOn I ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' E p.2 (S p.2 v)) V :=
    (hS v).comp contMDiffOn_snd (fun _ h ↦ h.2)
  let B : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    ((F.metric p.1).inner p.2).bilinearComp (S p.2) (S p.2)
  have hBs (v w : E) : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun p ↦ B p v w) V := by
    intro p hp
    have hg := (F.smooth p ⟨hp.1, Set.mem_univ p.2⟩).mono
      (show V ⊆ J ×ˢ Set.univ from fun q hq ↦ ⟨hq.1, Set.mem_univ q.2⟩)
    have happ : ContMDiffWithinAt I ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun q ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          q.2 (B q v w)) V p := by
      exact hg.clm_bundle_apply₂ (hSP v p hp) (hSP w p hp)
    simp only [Bundle.contMDiffWithinAt_totalSpace] at happ
    exact happ.2
  have hPartial {f : ℝ × M → ℝ} (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V) :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun p ↦ derivWithin (fun τ ↦ f (τ, p.2)) J p.1) V := by
    intro p hp
    have hmap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : (ℝ × M) × ℝ ↦ (q.2, q.1.2)) :=
      contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)
    have hc : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : (ℝ × M) × ℝ ↦ f (q.2, q.1.2)) (V ×ˢ J) (p, p.1) :=
      (hf p hp).comp (p, p.1) (hmap (p, p.1)).contMDiffWithinAt
        (show Set.MapsTo (fun q : (ℝ × M) × ℝ ↦ (q.2, q.1.2)) (V ×ˢ J) V from
          fun _ hq ↦ ⟨hq.2, hq.1.2⟩)
    have hd := ContMDiffWithinAt.mfderivWithin
      (f := fun (q : ℝ × M) (τ : ℝ) ↦ f (τ, q.2)) (g := Prod.fst)
      hc contMDiffWithinAt_fst hp (fun q hq ↦ hq.1) (m := ∞) (by simp)
      hJ.uniqueMDiffOn
    have ha := hd.clm_apply (contMDiffWithinAt_const (c := (1 : ℝ)))
    simpa only [inTangentCoordinates_model_space, mfderivWithin_eq_fderivWithin,
      derivWithin] using! ha
  choose R hR using fun p : ℝ × M ↦
    (isSmoothCovariantTensor_ricciEvaluation (F.connection p.1)).1 p.2
  have hRC (p : ℝ × M) (a b : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 a b = R p ![a, b] := hR p ![a, b]
  have hu0 {p : ℝ × M} (a b z : TangentSpace (𝓡 n) p.2) :
      Function.update ![a, b] 0 z = ![z, b] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hu1 {p : ℝ × M} (a b z : TangentSpace (𝓡 n) p.2) :
      Function.update ![a, b] 1 z = ![a, z] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have ha1 (p : ℝ × M) (a b z : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 (a + b) z =
        (F.connection p.1).ricci p.2 a z + (F.connection p.1).ricci p.2 b z := by
    simp only [hRC]
    simpa only [hu0] using (R p).map_update_add ![a, z] 0 a b
  have ha2 (p : ℝ × M) (a b z : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 z (a + b) =
        (F.connection p.1).ricci p.2 z a + (F.connection p.1).ricci p.2 z b := by
    simp only [hRC]
    simpa only [hu1] using (R p).map_update_add ![z, a] 1 a b
  have hs1 (p : ℝ × M) (c : ℝ) (a b : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 (c • a) b =
        c • (F.connection p.1).ricci p.2 a b := by
    simp only [hRC]
    simpa only [hu0] using (R p).map_update_smul ![a, b] 0 c a
  have hs2 (p : ℝ × M) (c : ℝ) (a b : TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).ricci p.2 a (c • b) =
        c • (F.connection p.1).ricci p.2 a b := by
    simp only [hRC]
    simpa only [hu1] using (R p).map_update_smul ![a, b] 1 c b
  let C : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ LinearMap.toContinuousLinearMap
          { toFun := fun w ↦ (F.connection p.1).ricci p.2 (S p.2 v) (S p.2 w)
            map_add' := by intro a b; rw [map_add, ha2]
            map_smul' := by intro c a; rw [map_smul, hs2]; rfl }
        map_add' := by
          intro a b
          ext w
          change (F.connection p.1).ricci p.2 (S p.2 (a + b)) (S p.2 w) = _
          rw [map_add, ha1]
          rfl
        map_smul' := by
          intro c a
          ext w
          change (F.connection p.1).ricci p.2 (S p.2 (c • a)) (S p.2 w) = _
          rw [map_smul, hs1]
          rfl }
  have hCs (v w : E) : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun p ↦ C p v w) V := by
    apply ((hPartial (hBs v w)).mul (contMDiffOn_const (c := (-1 / 2 : ℝ)))).congr
    intro p hp
    have he := (F.equation p.1 hp.1 p.2 (S p.2 v) (S p.2 w)).derivWithin (hJ p.1 hp.1)
    change (F.connection p.1).ricci p.2 (S p.2 v) (S p.2 w) =
      derivWithin (fun τ ↦ (F.metric τ).inner p.2 (S p.2 v) (S p.2 w)) J p.1 * (-1 / 2)
    rw [he]
    ring
  have hB : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B V p0 :=
    hclm fun v ↦ hclm fun w ↦ hBs v w p0 hpV
  have hC : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ C V p0 :=
    hclm fun v ↦ hclm fun w ↦ hCs v w p0 hpV
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let A : ℝ × M → E →L[ℝ] E := fun p ↦ Q.toContinuousLinearMap.comp (B p)
  let H : ℝ × M → E →L[ℝ] E := fun p ↦ Q.toContinuousLinearMap.comp (C p)
  have hA : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) ∞ A V p0 :=
    contMDiffWithinAt_const.clm_comp hB
  have hH : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) ∞ H V p0 :=
    contMDiffWithinAt_const.clm_comp hC
  have hInv {p : ℝ × M} (hp : p.2 ∈ t.baseSet) : (A p).IsInvertible := by
    have hz (v : E) (hv : A p v = 0) : v = 0 := by
      have hBv : B p v = 0 := Q.injective (by simpa [A] using hv)
      have hi : (F.metric p.1).inner p.2 (S p.2 v) (S p.2 v) = 0 := by
        simpa [B] using congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hBv
      have hSv : S p.2 v = 0 := by
        by_contra hne
        exact (ne_of_gt ((F.metric p.1).pos p.2 _ hne)) hi
      have hv' := congrArg (t.continuousLinearMapAt ℝ p.2) hSv
      simpa only [S, t.continuousLinearMapAt_symmL hp, map_zero] using hv'
    have hinj : Function.Injective (A p) := by
      intro v w h
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub, h, sub_self]
    have hsurj : Function.Surjective (A p) := (LinearMap.injective_iff_surjective).mp hinj
    exact ⟨(LinearEquiv.ofBijective (A p).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      by ext v; rfl⟩
  let L := fun p ↦ (A p).inverse.comp (H p)
  have hL : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) ∞ L V p0 :=
    ((hInv hxT).contDiffAt_map_inverse.contMDiffAt.comp_contMDiffWithinAt p0 hA).clm_comp hH
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let tr := fun p ↦ ∑ i, b.repr ((L p).comp (L p) (b i)) i
  have htr : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ tr V p0 := by
    apply ContMDiffWithinAt.sum
    intro i _
    exact (b.coord i).toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt p0
      ((hL.clm_comp hL).clm_apply contMDiffWithinAt_const)
  have htr_eq (p : ℝ × M) : LinearMap.trace ℝ E ((L p).comp (L p)).toLinearMap = tr p := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, tr]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have heq {p : ℝ × M} (hp : p.2 ∈ t.baseSet) :
      tr p = (F.connection p.1).ricciNormSq p.2 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric p.1).toRiemannianMetric⟩
    let e := (t.continuousLinearEquivAt ℝ p.2 hp).symm
    let K := e.toLinearEquiv.conj (L p).toLinearMap
    have hrec (v : E) : B p (L p v) = C p v := by
      apply Q.injective
      change A p ((A p).inverse (H p v)) = H p v
      exact (hInv hp).self_apply_inverse _
    have hK (a b : TangentSpace (𝓡 n) p.2) :
        (F.metric p.1).inner p.2 (K a) b = (F.connection p.1).ricci p.2 a b := by
      have h := congrArg (fun f : E →L[ℝ] ℝ ↦ f (e.symm b)) (hrec (e.symm a))
      have hSe (v : E) : S p.2 v = e v :=
        (congrFun (t.symm_continuousLinearEquivAt_eq hp) v).symm
      change (F.metric p.1).inner p.2 (S p.2 (L p (e.symm a))) (S p.2 (e.symm b)) =
        (F.connection p.1).ricci p.2 (S p.2 (e.symm a)) (S p.2 (e.symm b)) at h
      simp only [hSe, e.apply_symm_apply] at h
      exact h
    have hconj : e.toLinearEquiv.conj ((L p).comp (L p)).toLinearMap = K.comp K := by
      ext a
      change e (L p (L p (e.symm a))) = e (L p (e.symm (e (L p (e.symm a)))))
      rw [e.symm_apply_apply]
    have hSq : (∑ i, inner ℝ ((F.metric p.1).orthonormalBasis p.2 i)
        (K (K ((F.metric p.1).orthonormalBasis p.2 i)))) =
        (F.connection p.1).ricciNormSq p.2 := by
      let b0 := (F.metric p.1).orthonormalBasis p.2
      have hExpand (a : TangentSpace (𝓡 n) p.2) :
          K a = ∑ j, (F.connection p.1).ricci p.2 a (b0 j) • b0 j := by
        calc
          _ = ∑ j, inner ℝ (b0 j) (K a) • b0 j := (b0.sum_repr' (K a)).symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j _
            change (F.metric p.1).inner p.2 (b0 j) (K a) • b0 j = _
            rw [(F.metric p.1).symm, hK]
      apply Finset.sum_congr rfl
      intro i _
      change inner ℝ (b0 i) (K (K (b0 i))) = _
      rw [hExpand (b0 i), map_sum, inner_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [map_smul, inner_smul_right]
      change (F.connection p.1).ricci p.2 (b0 i) (b0 j) *
        (F.metric p.1).inner p.2 (b0 i) (K (b0 j)) =
          (F.connection p.1).ricci p.2 (b0 i) (b0 j) ^ 2
      rw [(F.metric p.1).symm, hK, ricci_symm (F.connection p.1) p.2 (b0 j) (b0 i)]
      ring
    calc
      tr p = LinearMap.trace ℝ E ((L p).comp (L p)).toLinearMap := (htr_eq p).symm
      _ = LinearMap.trace ℝ (TangentSpace (𝓡 n) p.2) (K.comp K) := by
        rw [← hconj]
        exact (LinearMap.trace_conj' ((L p).comp (L p)).toLinearMap e.toLinearEquiv).symm
      _ = ∑ i, inner ℝ ((F.metric p.1).orthonormalBasis p.2 i)
          (K (K ((F.metric p.1).orthonormalBasis p.2 i))) := by
        rw [LinearMap.trace_eq_matrix_trace ℝ ((F.metric p.1).orthonormalBasis p.2).toBasis]
        simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply, LinearMap.comp_apply]
      _ = _ := hSq
  have hScalar : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (F.connection p.1).ricciNormSq p.2) V p0 := by
    apply htr.congr_of_eventuallyEq_of_mem ?_ hpV
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (heq hp.2).symm
  apply hScalar.continuousWithinAt.mono_of_mem_nhdsWithin
  have hO : (Prod.snd ⁻¹' t.baseSet : Set (ℝ × M)) ∈ 𝓝 p0 :=
    continuous_snd.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hxT)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with p hp hpt
  exact ⟨hp.1, hpt⟩

end PoincareConjecture.RicciFlowAnalysis
