import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Connection.SpacetimePairings
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorDerivativeClosure
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
private theorem contMDiffWithinAt_clm_of_apply
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {L : ℝ × M → E →L[ℝ] G} {V : Set (ℝ × M)} {p : ℝ × M}
    (hL : ∀ v : E, ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, G) ∞
      (fun q ↦ L q v) V p) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E →L[ℝ] G) ∞ L V p := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e1 := ContinuousLinearEquiv.ofFinrankEq hd
  let e2 := (e1.arrowCongr (1 : G ≃L[ℝ] G)).trans (ContinuousLinearEquiv.piRing (Fin d))
  have hc : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, Fin d → G) ∞
      (fun q ↦ e2 (L q)) V p := by
    apply contMDiffWithinAt_pi_space.mpr
    intro i
    exact hL _
  have h := e2.symm.toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt p hc
  have heq : (fun q ↦ e2.symm (e2 (L q))) = L := by
    funext q
    exact e2.symm_apply_apply (L q)
  have h' : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E →L[ℝ] G) ∞
      (fun q ↦ e2.symm (e2 (L q))) V p := by
    simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe] using! h
  rwa [heq] at h'

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

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_flow_linear_connection (F : RicciFlow n M J) (hU : IsOpen U)
    (L : (p : ℝ × M) → TangentSpace (𝓡 n) p.2 →L[ℝ] ℝ)
    (hL : ∀ (V : Set M), IsOpen V → V ⊆ U →
      ∀ (Z : (y : M) → TangentSpace (𝓡 n) y),
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) V →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ L p (Z p.2)) (J ×ˢ V))
    {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ L p ((F.connection p.1).connection Y p.2 (X p.2))) (J ×ˢ U) := by
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
  let D : ℝ × M → E →L[ℝ] ℝ := fun p ↦ (L p).comp (S p.2)
  have hB : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      B (J ×ˢ O) := by
    intro p hp
    apply contMDiffWithinAt_clm_of_apply
    intro v
    apply contMDiffWithinAt_clm_of_apply
    intro w
    exact contMDiffOn_flow_metric_pairing F (hS v) (hS w) p hp
  have hP : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E →L[ℝ] ℝ) ∞ P (J ×ˢ O) := by
    intro p hp
    apply contMDiffWithinAt_clm_of_apply
    intro v
    exact contMDiffOn_flow_connection_pairing F hO
      (hX.mono inter_subset_left) (hY.mono inter_subset_left) (hS v) p hp
  have hD : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E →L[ℝ] ℝ) ∞ D (J ×ˢ O) := by
    intro p hp
    apply contMDiffWithinAt_clm_of_apply
    intro v
    exact hL O hO inter_subset_left (fun y ↦ S y v) (hS v) p hp
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let A : ℝ × M → E →L[ℝ] E := fun p ↦ Q.toContinuousLinearMap.comp (B p)
  have hA : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E →L[ℝ] E) ∞ A (J ×ˢ O) :=
    contMDiffOn_const.clm_comp hB
  have hInv {p : ℝ × M} (hp : p.2 ∈ t.baseSet) : (A p).IsInvertible := by
    have hz (v : E) (hv : A p v = 0) : v = 0 := by
      have hBv : B p v = 0 := Q.injective (by simpa [A] using hv)
      have hi : (F.metric p.1).inner p.2 (S p.2 v) (S p.2 v) = 0 := by
        simpa [B] using congrArg (fun K : E →L[ℝ] ℝ ↦ K v) hBv
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
  have hAi : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun p ↦ (A p).inverse) (J ×ˢ O) p0 :=
    (hInv hxT).contDiffAt_map_inverse.contMDiffAt.comp_contMDiffWithinAt p0 (hA p0 hpO)
  have hrec : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) ∞
      (fun p ↦ (A p).inverse (Q (P p))) (J ×ˢ O) p0 :=
    hAi.clm_apply (Q.toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt p0 (hP p0 hpO))
  have hvalue : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ L p (Z p)) (J ×ˢ O) p0 := by
    apply ((hD p0 hpO).clm_apply hrec).congr_of_eventuallyEq_of_mem ?_ hpO
    filter_upwards [self_mem_nhdsWithin] with p hp
    have he : (A p).inverse (Q (P p)) = t.continuousLinearMapAt ℝ p.2 (Z p) := by
      apply (hInv hp.2.2).inverse_apply_eq.mpr
      change Q (P p) = Q (B p (t.continuousLinearMapAt ℝ p.2 (Z p)))
      apply congrArg Q
      ext v
      change (F.metric p.1).inner p.2 (Z p) (S p.2 v) =
        (F.metric p.1).inner p.2 (S p.2 (t.continuousLinearMapAt ℝ p.2 (Z p))) (S p.2 v)
      rw [t.symmL_continuousLinearMapAt hp.2.2]
    change L p (Z p) = D p ((A p).inverse (Q (P p)))
    rw [he]
    change L p (Z p) = L p (S p.2 (t.continuousLinearMapAt ℝ p.2 (Z p)))
    rw [t.symmL_continuousLinearMapAt hp.2.2]
  apply hvalue.mono_of_mem_nhdsWithin
  have hn : (Prod.snd ⁻¹' t.baseSet : Set (ℝ × M)) ∈ 𝓝 p0 :=
    continuous_snd.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hxT)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with p hp hpt
  exact ⟨hp.1, hp.2, hpt⟩

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_flow_covariantTensorDerivative (F : RicciFlow n M J) {k : ℕ}
    {T : ℝ → CovariantTensorEvaluation n M k}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hTime : ∀ (V : Set M), IsOpen V →
      ∀ (Y : Fin k → (y : M) → TangentSpace (𝓡 n) y),
        (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (Y i)) V) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ T p.1 p.2 (fun i ↦ Y i p.2)) (J ×ˢ V))
    (hU : IsOpen U) {X : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (F.connection p.1).covariantTensorDerivative (T p.1) p.2
        (fun i ↦ X i p.2)) (J ×ˢ U) := by
  classical
  have hfirst := contMDiffOn_mvfderiv_spatial hU
    (hTime U hU (fun i ↦ X i.succ) (fun i ↦ hX i.succ)) (hX 0)
  choose A hA using fun p : ℝ × M ↦ (hT p.1).1 p.2
  have hcorrection (i : Fin k) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ T p.1 p.2 (Function.update (fun j ↦ X j.succ p.2) i
          ((F.connection p.1).connection (X i.succ) p.2 (X 0 p.2)))) (J ×ˢ U) := by
    let L : (p : ℝ × M) → TangentSpace (𝓡 n) p.2 →L[ℝ] ℝ := fun p ↦
      letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p.2) :=
        VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) p.2
      ((A p).toLinearMap (fun j ↦ X j.succ p.2) i).toContinuousLinearMap
    have hLeval (p : ℝ × M) (v : TangentSpace (𝓡 n) p.2) :
        L p v = T p.1 p.2 (Function.update (fun j ↦ X j.succ p.2) i v) :=
      (hA p _).symm
    have hL : ∀ (V : Set M), IsOpen V → V ⊆ U →
        ∀ (Z : (y : M) → TangentSpace (𝓡 n) y),
          ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) V →
          ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M ↦ L p (Z p.2)) (J ×ˢ V) := by
      intro V hV hVU Z hZ
      have hY (j : Fin k) :
          ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
            ∞ (T% (Function.update (fun l ↦ X l.succ) i Z j)) V := by
        by_cases hj : j = i
        · subst j
          simpa only [Function.update_self] using hZ
        · simpa only [Function.update_of_ne hj] using (hX j.succ).mono hVU
      apply (hTime V hV (Function.update (fun j ↦ X j.succ) i Z) hY).congr
      intro p hp
      rw [hLeval]
      congr 1
      funext j
      by_cases hj : j = i <;> simp [hj]
    apply (contMDiffOn_flow_linear_connection F hU L hL (hX 0) (hX i.succ)).congr
    intro p hp
    exact (hLeval p _).symm
  have hsum := contMDiffOn_finsetSum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) ↦ hcorrection i)
  apply (hfirst.sub hsum).congr
  intro p hp
  exact (covariantTensorDerivativeOnFields_eq (F.connection p.1) (hT p.1) hU hX hp.2).symm

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_flow_iteratedCovariantTensorDerivative (F : RicciFlow n M J) {k : ℕ}
    {T : ℝ → CovariantTensorEvaluation n M k}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hTime : ∀ (V : Set M), IsOpen V →
      ∀ (Y : Fin k → (y : M) → TangentSpace (𝓡 n) y),
        (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (Y i)) V) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ T p.1 p.2 (fun i ↦ Y i p.2)) (J ×ˢ V))
    (m : ℕ) (hU : IsOpen U) {X : Fin (k + m) → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (F.connection p.1).iteratedCovariantTensorDerivative (T p.1) m p.2
        (fun i ↦ X i p.2)) (J ×ˢ U) := by
  have hsmooth (m : ℕ) (s : ℝ) :
      IsSmoothCovariantTensor ((F.connection s).iteratedCovariantTensorDerivative (T s) m) := by
    induction m with
    | zero => exact hT s
    | succ m ih => exact isSmoothCovariantTensor_covariantTensorDerivative (F.connection s) ih
  induction m generalizing U with
  | zero => exact hTime U hU X hX
  | succ m ih =>
    exact contMDiffOn_flow_covariantTensorDerivative F (hsmooth m)
      (fun V hV Y hY ↦ ih hV hY) hU hX

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
private theorem contMDiffOn_timePartial (F : RicciFlow n M J)
    {f : ℝ × M → ℝ}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (J ×ˢ U)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p ↦ derivWithin (fun τ ↦ f (τ, p.2)) J p.1) (J ×ˢ U) := by
  let I := 𝓘(ℝ, ℝ).prod (𝓡 n)
  let V := J ×ˢ U
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex F.interval.convex
    (F.interval.convex.nontrivial_iff_nonempty_interior.mp F.nontrivial)
  intro p hp
  have hmap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : (ℝ × M) × ℝ ↦ (q.2, q.1.2)) :=
    contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)
  have hc : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : (ℝ × M) × ℝ ↦ f (q.2, q.1.2)) (V ×ˢ J) (p, p.1) :=
    (hf p hp).comp (p, p.1) (hmap (p, p.1)).contMDiffWithinAt
      (show MapsTo (fun q : (ℝ × M) × ℝ ↦ (q.2, q.1.2)) (V ×ˢ J) V from
        fun _ hq ↦ ⟨hq.2, hq.1.2⟩)
  have hd := ContMDiffWithinAt.mfderivWithin
    (f := fun (q : ℝ × M) (τ : ℝ) ↦ f (τ, q.2)) (g := Prod.fst)
    hc contMDiffWithinAt_fst hp (fun q hq ↦ hq.1) (m := ∞) (by simp)
    hJ.uniqueMDiffOn
  have ha := hd.clm_apply (contMDiffWithinAt_const (c := (1 : ℝ)))
  simpa only [inTangentCoordinates_model_space, mfderivWithin_eq_fderivWithin,
    derivWithin] using! ha

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_flow_ricciEvaluation (F : RicciFlow n M J) (hU : IsOpen U)
    {X : Fin 2 → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (F.connection p.1).ricciEvaluation p.2 (fun i ↦ X i p.2))
      (J ×ˢ U) := by
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex F.interval.convex
    (F.interval.convex.nontrivial_iff_nonempty_interior.mp F.nontrivial)
  have hmetric := contMDiffOn_flow_metric_pairing F (hX 0) (hX 1)
  have hpartial := contMDiffOn_timePartial F hmetric
  apply (hpartial.mul (contMDiffOn_const (c := (-1 / 2 : ℝ)))).congr
  intro p hp
  have he := (F.equation p.1 hp.1 p.2 (X 0 p.2) (X 1 p.2)).derivWithin (hJ p.1 hp.1)
  change (F.connection p.1).ricci p.2 (X 0 p.2) (X 1 p.2) =
    derivWithin (fun τ ↦ (F.metric τ).inner p.2 (X 0 p.2) (X 1 p.2)) J p.1 * (-1 / 2)
  rw [he]
  ring

end PoincareConjecture.RicciFlowAnalysis
