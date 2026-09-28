import PoincareConjecture.Proofs.M04.ScalarHessian
import PoincareConjecture.Proofs.M04.ScalarChainRule
import PoincareConjecture.Proofs.M04.SpacetimePairings
import PoincareConjecture.Proofs.M04.MetricPairings
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter Function

universe u

namespace PoincareConjecture.M04

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
theorem continuousOn_flow_hessianOnFields (F : RicciFlow n M J)
    {q : M → ℝ} {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hU : IsOpen U) (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContinuousOn
      (fun p : ℝ × M ↦ (F.connection p.1).hessianOnFields q X Y p.2) (J ×ˢ U) := by
  have hqP : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ q p.2) (J ×ˢ U) :=
    hq.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
  have hfirst := (contMDiffOn_mvfderiv_spatial hU
    (contMDiffOn_mvfderiv_spatial hU hqP hY) hX).continuousOn
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
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) q p.2).comp (S p.2)
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
      ((hq.mono inter_subset_left).comp contMDiffOn_snd (fun _ hp ↦ hp.2))
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
  have hsecond : ContinuousWithinAt (fun p : ℝ × M ↦ mvfderiv (𝓡 n) q p.2 (Z p))
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
    change mvfderiv (𝓡 n) q p.2 (Z p) = D p ((A p).inverse (Q (P p)))
    rw [he]
    change mvfderiv (𝓡 n) q p.2 (Z p) =
      mvfderiv (𝓡 n) q p.2 (S p.2 (t.continuousLinearMapAt ℝ p.2 (Z p)))
    rw [t.symmL_continuousLinearMapAt hp.2.2]
  have hH : ContinuousWithinAt
      (fun p : ℝ × M ↦ (F.connection p.1).hessianOnFields q X Y p.2) (J ×ˢ O) p0 :=
    ((hfirst p0 hp0).mono (prod_mono Subset.rfl inter_subset_left)).sub hsecond
  apply hH.mono_of_mem_nhdsWithin
  have hn : (Prod.snd ⁻¹' t.baseSet : Set (ℝ × M)) ∈ 𝓝 p0 :=
    continuous_snd.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hxT)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with p hp hpt
  exact ⟨hp.1, hp.2, hpt⟩

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem continuousOn_flow_trace (F : RicciFlow n M J) (hU : IsOpen U)
    (T : (p : ℝ × M) → MultilinearMap ℝ (fun _ : Fin 2 ↦ TangentSpace (𝓡 n) p.2) ℝ)
    (hT : ∀ (V : Set M), IsOpen V → V ⊆ U →
      ∀ (X Y : (y : M) → TangentSpace (𝓡 n) y),
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) V →
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) V →
        ContinuousOn (fun p : ℝ × M ↦ T p ![X p.2, Y p.2]) (J ×ˢ V)) :
    ContinuousOn (fun p : ℝ × M ↦ ∑ i, T p
      ![(F.metric p.1).orthonormalBasis p.2 i, (F.metric p.1).orthonormalBasis p.2 i])
      (J ×ˢ U) := by
  classical
  let R := fun (p : ℝ × M) (a b : TangentSpace (𝓡 n) p.2) ↦ T p ![a, b]
  have hu0 {p : ℝ × M} (a b z : TangentSpace (𝓡 n) p.2) :
      Function.update ![a, b] 0 z = ![z, b] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hu1 {p : ℝ × M} (a b z : TangentSpace (𝓡 n) p.2) :
      Function.update ![a, b] 1 z = ![a, z] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have ha1 (p : ℝ × M) (a b z : TangentSpace (𝓡 n) p.2) :
      R p (a + b) z = R p a z + R p b z := by
    simpa only [R, hu0] using (T p).map_update_add ![a, z] 0 a b
  have ha2 (p : ℝ × M) (a b z : TangentSpace (𝓡 n) p.2) :
      R p z (a + b) = R p z a + R p z b := by
    simpa only [R, hu1] using (T p).map_update_add ![z, a] 1 a b
  have hs1 (p : ℝ × M) (c : ℝ) (a b : TangentSpace (𝓡 n) p.2) :
      R p (c • a) b = c • R p a b := by
    simpa only [R, hu0] using (T p).map_update_smul ![a, b] 0 c a
  have hs2 (p : ℝ × M) (c : ℝ) (a b : TangentSpace (𝓡 n) p.2) :
      R p a (c • b) = c • R p a b := by
    simpa only [R, hu1] using (T p).map_update_smul ![a, b] 1 c b
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
  let B : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    ((F.metric p.1).inner p.2).bilinearComp (S p.2) (S p.2)
  let C : ℝ × M → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ LinearMap.toContinuousLinearMap
          { toFun := fun w ↦ R p (S p.2 v) (S p.2 w)
            map_add' := by intro a b; rw [map_add, ha2]
            map_smul' := by intro c a; rw [map_smul, hs2]; rfl }
        map_add' := by
          intro a b
          ext w
          change R p (S p.2 (a + b)) (S p.2 w) = _
          rw [map_add, ha1]
          rfl
        map_smul' := by
          intro c a
          ext w
          change R p (S p.2 (c • a)) (S p.2 w) = _
          rw [map_smul, hs1]
          rfl }
  have hB : ContinuousOn B (J ×ˢ O) := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro w
    exact (contMDiffOn_flow_metric_pairing F (hS v) (hS w)).continuousOn
  have hC : ContinuousOn C (J ×ˢ O) := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro w
    exact hT O hO inter_subset_left (fun y ↦ S y v) (fun y ↦ S y w) (hS v) (hS w)
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let A : ℝ × M → E →L[ℝ] E := fun p ↦ Q.toContinuousLinearMap.comp (B p)
  let H : ℝ × M → E →L[ℝ] E := fun p ↦ Q.toContinuousLinearMap.comp (C p)
  have hA : ContinuousOn A (J ×ˢ O) := continuousOn_const.clm_comp hB
  have hH : ContinuousOn H (J ×ˢ O) := continuousOn_const.clm_comp hC
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
  have hInvDiff : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (A p0) :=
    (hInv hxT).contDiffAt_map_inverse
  have hL : ContinuousWithinAt L (J ×ˢ O) p0 :=
    (hInvDiff.continuousAt.comp_continuousWithinAt (hA p0 hpO)).clm_comp (hH p0 hpO)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let tr := fun p ↦ ∑ i, b.repr (L p (b i)) i
  have htr : ContinuousWithinAt tr (J ×ˢ O) p0 := by
    rw [ContinuousWithinAt]
    apply tendsto_finsetSum
    intro i _
    exact (b.coord i).toContinuousLinearMap.continuous.continuousAt.comp_continuousWithinAt
      (hL.clm_apply continuousWithinAt_const)
  have htr_eq (p : ℝ × M) : LinearMap.trace ℝ E (L p).toLinearMap = tr p := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, tr]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have heq {p : ℝ × M} (hp : p.2 ∈ t.baseSet) : tr p = ∑ i, T p
      ![(F.metric p.1).orthonormalBasis p.2 i, (F.metric p.1).orthonormalBasis p.2 i] := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric p.1).toRiemannianMetric⟩
    let e := (t.continuousLinearEquivAt ℝ p.2 hp).symm
    let K := e.toLinearEquiv.conj (L p).toLinearMap
    have hrec (v : E) : B p (L p v) = C p v := by
      apply Q.injective
      change A p ((A p).inverse (H p v)) = H p v
      exact (hInv hp).self_apply_inverse _
    have hK (a b : TangentSpace (𝓡 n) p.2) : (F.metric p.1).inner p.2 (K a) b = R p a b := by
      have h := congrArg (fun f : E →L[ℝ] ℝ ↦ f (e.symm b)) (hrec (e.symm a))
      have hSe (v : E) : S p.2 v = e v :=
        (congrFun (t.symm_continuousLinearEquivAt_eq hp) v).symm
      change (F.metric p.1).inner p.2 (S p.2 (L p (e.symm a))) (S p.2 (e.symm b)) =
        R p (S p.2 (e.symm a)) (S p.2 (e.symm b)) at h
      simp only [hSe, e.apply_symm_apply] at h
      exact h
    calc
      tr p = LinearMap.trace ℝ E (L p).toLinearMap := (htr_eq p).symm
      _ = LinearMap.trace ℝ (TangentSpace (𝓡 n) p.2) K :=
        (LinearMap.trace_conj' (L p).toLinearMap e.toLinearEquiv).symm
      _ = ∑ i, inner ℝ ((F.metric p.1).orthonormalBasis p.2 i)
          (K ((F.metric p.1).orthonormalBasis p.2 i)) := by
        rw [LinearMap.trace_eq_matrix_trace ℝ ((F.metric p.1).orthonormalBasis p.2).toBasis]
        simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        change (F.metric p.1).inner p.2 ((F.metric p.1).orthonormalBasis p.2 i)
          (K ((F.metric p.1).orthonormalBasis p.2 i)) =
            R p ((F.metric p.1).orthonormalBasis p.2 i) ((F.metric p.1).orthonormalBasis p.2 i)
        rw [(F.metric p.1).symm, hK]
  have htrace : ContinuousWithinAt (fun p : ℝ × M ↦ ∑ i, T p
      ![(F.metric p.1).orthonormalBasis p.2 i, (F.metric p.1).orthonormalBasis p.2 i])
      (J ×ˢ O) p0 := by
    apply htr.congr_of_mem ?_ hpO
    intro p hp
    exact (heq hp.2.2).symm
  apply htrace.mono_of_mem_nhdsWithin
  have hn : (Prod.snd ⁻¹' t.baseSet : Set (ℝ × M)) ∈ 𝓝 p0 :=
    continuous_snd.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hxT)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with p hp hpt
  exact ⟨hp.1, hp.2, hpt⟩

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_flow_laplacian [T2Space M] (F : RicciFlow n M J)
    {q : M → ℝ} (hU : IsOpen U) (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U) :
    ContinuousOn (fun p : ℝ × M ↦ (F.connection p.1).laplacian q p.2) (J ×ˢ U) := by
  classical
  let T : (p : ℝ × M) → MultilinearMap ℝ (fun _ : Fin 2 ↦ TangentSpace (𝓡 n) p.2) ℝ :=
    fun p ↦ if hp : p.2 ∈ U then
      Classical.choose (exists_hessian_bilinear_of_contMDiffOn (F.connection p.1) hU hq hp)
      else 0
  have hT (p : ℝ × M) (hp : p.2 ∈ U) (v : Fin 2 → TangentSpace (𝓡 n) p.2) :
      (F.connection p.1).hessian q p.2 (v 0) (v 1) = T p v := by
    simp only [T, dif_pos hp]
    exact Classical.choose_spec
      (exists_hessian_bilinear_of_contMDiffOn (F.connection p.1) hU hq hp) v
  have htrace := continuousOn_flow_trace F hU T (by
    intro V hV hVU X Y hX hY
    apply (continuousOn_flow_hessianOnFields F hV (hq.mono hVU) hX hY).congr
    intro p hp
    change T p ![X p.2, Y p.2] =
      (F.connection p.1).hessianOnFields q X Y p.2
    calc
      T p ![X p.2, Y p.2] = (F.connection p.1).hessian q p.2 (X p.2) (Y p.2) :=
        (hT p (hVU hp.2) ![X p.2, Y p.2]).symm
      _ = (F.connection p.1).hessianOnFields q X Y p.2 :=
        (hessianOnFields_eq_hessian_of_contMDiffOn (F.connection p.1)
          hV (hq.mono hVU) hX hY hp.2).symm)
  apply htrace.congr
  intro p hp
  apply Finset.sum_congr rfl
  intro i _
  exact hT p hp.2 ![(F.metric p.1).orthonormalBasis p.2 i, (F.metric p.1).orthonormalBasis p.2 i]

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_flow_scalarGradientSq (F : RicciFlow n M J)
    {q : M → ℝ} (hU : IsOpen U) (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U) :
    ContinuousOn (fun p : ℝ × M ↦ scalarGradientSq (F.metric p.1) q p.2) (J ×ˢ U) := by
  classical
  let T : (p : ℝ × M) → MultilinearMap ℝ (fun _ : Fin 2 ↦ TangentSpace (𝓡 n) p.2) ℝ :=
    fun p ↦ MultilinearMap.mk' (R := ℝ)
      (fun v ↦ mvfderiv (𝓡 n) q p.2 (v 0) * mvfderiv (𝓡 n) q p.2 (v 1))
      (by
        intro v i a b
        fin_cases i <;> simp [Function.update, map_add, add_mul, mul_add])
      (by
        intro v i c a
        fin_cases i <;> simp [Function.update, map_smul, smul_eq_mul, mul_assoc, mul_left_comm])
  have htrace := continuousOn_flow_trace F hU T (by
    intro V hV hVU X Y hX hY
    exact ((contMDiffOn_directional_derivative hV (hq.mono hVU) hX).mul
      (contMDiffOn_directional_derivative hV (hq.mono hVU) hY)).continuousOn.comp
        continuousOn_snd (fun _ hp ↦ hp.2))
  simpa only [scalarGradientSq, T, MultilinearMap.mk'_apply, pow_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using htrace

theorem continuousOn_flow_tensorTrace (F : RicciFlow n M J) (hU : IsOpen U)
    (T : (p : ℝ × M) → MultilinearMap ℝ (fun _ : Fin 2 ↦ TangentSpace (𝓡 n) p.2) ℝ)
    (hT : ∀ (V : Set M), IsOpen V → V ⊆ U →
      ∀ (X Y : (y : M) → TangentSpace (𝓡 n) y),
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) V →
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) V →
        ContinuousOn (fun p : ℝ × M ↦ T p ![X p.2, Y p.2]) (J ×ˢ V)) :
    ContinuousOn (fun p : ℝ × M ↦ ∑ i, T p
      ![(F.metric p.1).orthonormalBasis p.2 i, (F.metric p.1).orthonormalBasis p.2 i])
      (J ×ˢ U) :=
  continuousOn_flow_trace F hU T hT

end PoincareConjecture.M04
