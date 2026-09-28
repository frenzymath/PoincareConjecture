import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.NullConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.NullSections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem covariantRicciDerivative_eq_zero_of_terminal_null_vector
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ x y, ricciNullity (F.connection b) x = ricciNullity (F.connection b) y)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (hv : (F.connection b).ricci x v v = 0)
    (u w : TangentSpace (𝓡 n) x) :
    (F.connection b).covariantTensorDerivative (F.connection b).ricciEvaluation
      x ![u, v, w] = 0 := by
  have hD := hC.tensor_calculus n M (F.metric b) (F.connection b)
  have hRic (z : TangentSpace (𝓡 n) x) : 0 ≤ (F.connection b).ricci x z z :=
    Finset.sum_nonneg fun i _ => hsec b ⟨hab.le, le_rfl⟩ x z
      ((F.metric b).orthonormalBasis x i)
  obtain ⟨U, V, hU, hxU, hV, hVx, hnull⟩ :=
    exists_local_smooth_ricci_null_section (F.connection b) hD
      (Eventually.of_forall fun y => hdim y x) v
      (ricci_eq_zero_of_nonneg_of_self_eq_zero _ hD x hRic hv)
  have hn : ∀ᶠ y in 𝓝 x, (F.connection b).ricci y (V y) (V y) = 0 :=
    Filter.mem_of_superset (hU.mem_nhds hxU) fun y hy => hnull y hy (V y)
  simpa only [hVx] using
    (covariantRicciDerivative_all_slots_eq_zero_of_terminal_null hC hab F hsec V
      ((hV x hxU).contMDiffAt (hU.mem_nhds hxU)) hn u w).1

theorem tensorLaplacian_ricci_eq_zero_of_terminal_null_vector
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ x y, ricciNullity (F.connection b) x = ricciNullity (F.connection b) y)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (hv : (F.connection b).ricci x v v = 0) (w : TangentSpace (𝓡 n) x) :
    (F.connection b).tensorLaplacian (F.connection b).ricciEvaluation x ![v, w] = 0 := by
  have hD := hC.tensor_calculus n M (F.metric b) (F.connection b)
  have hRic (z : TangentSpace (𝓡 n) x) : 0 ≤ (F.connection b).ricci x z z :=
    Finset.sum_nonneg fun i _ => hsec b ⟨hab.le, le_rfl⟩ x z
      ((F.metric b).orthonormalBasis x i)
  obtain ⟨U, V, hU, hxU, hV, hVx, hnull⟩ :=
    exists_local_smooth_ricci_null_section (F.connection b) hD
      (Eventually.of_forall fun y => hdim y x) v
      (ricci_eq_zero_of_nonneg_of_self_eq_zero _ hD x hRic hv)
  have hV' := (hV x hxU).contMDiffAt (hU.mem_nhds hxU)
  have hn : ∀ᶠ y in 𝓝 x, (F.connection b).ricci y (V y) (V y) = 0 :=
    Filter.mem_of_superset (hU.mem_nhds hxU) fun y hy => hnull y hy (V y)
  have hDV (u : TangentSpace (𝓡 n) x) :
      (F.connection b).ricci x ((F.connection b).connection V x u)
        ((F.connection b).connection V x u) = 0 :=
    ricci_connection_eq_zero_of_terminal_null hC hab F hsec V hV' hn u _
  have hfirst : ∀ᶠ y in 𝓝 x, ∀ z : TangentSpace (𝓡 n) y,
      (F.connection b).ricci y z z = 0 → ∀ u w,
        (F.connection b).covariantTensorDerivative (F.connection b).ricciEvaluation
          y ![u, z, w] = 0 :=
    Eventually.of_forall fun y z hz u w =>
      covariantRicciDerivative_eq_zero_of_terminal_null_vector hC hab F hsec hdim y z hz u w
  unfold LeviCivitaData.tensorLaplacian
  apply Finset.sum_eq_zero
  intro i _
  change (F.connection b).covariantTensorDerivative
    ((F.connection b).covariantTensorDerivative (F.connection b).ricciEvaluation) x
    ![(F.metric b).orthonormalBasis x i, (F.metric b).orthonormalBasis x i, v, w] = 0
  simpa only [hVx] using secondCovariantRicciDerivative_eq_zero_of_null_section
    (F.connection b) hD V hV' hn hDV hfirst
    ((F.metric b).orthonormalBasis x i) ((F.metric b).orthonormalBasis x i) w

theorem ricci_hasDerivWithinAt_zero_of_null_vector
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ}
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ t ∈ Ioc a b, ∀ x y,
      ricciNullity (F.connection t) x = ricciNullity (F.connection t) y)
    {t : ℝ} (ht : t ∈ Ioc a b) (x : M) (v : TangentSpace (𝓡 n) x)
    (hv : (F.connection t).ricci x v v = 0) (w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s => (F.connection s).ricci x v w) 0 (Icc a b) t := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub ordConnected_Icc
    ⟨a, left_mem_Icc.mpr ht.1.le, t, right_mem_Icc.mpr ht.1.le, ht.1.ne⟩
  have hLap := tensorLaplacian_ricci_eq_zero_of_terminal_null_vector hC ht.1 G
    (fun r hr => hsec r (hsub hr)) (hdim t ht) x v hv w
  have hreact := ricciReaction_eq_zero_of_ricci_self_eq_zero (F.connection t)
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) x
    (hsec t ⟨ht.1.le, ht.2⟩ x) hv w
  have h := hC.ricci_evolution n M (Icc a b) F t ⟨ht.1.le, ht.2⟩ x v w
  change (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![v, w] = 0 at hLap
  simpa only [hLap, hreact, add_zero] using h

end PoincareConjecture.RicciFlow.Splitting
