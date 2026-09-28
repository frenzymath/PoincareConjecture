import PoincareConjecture.Proofs.M35.Thm12_28.MetricConnectionJets









set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation:max "E" n:max => EuclideanSpace ℝ (Fin n)
local notation:max "G" n:max => E n →L[ℝ] E n →L[ℝ] ℝ

private noncomputable def connectionRightFormula {n : ℕ} (u : E n)
    (z : (G n × (E n →L[ℝ] G n)) × E n) : E n :=
  z.1.1.inverse (metricKoszulCovector z.1.2 u z.2)

private theorem connectionRightFormula_smooth {n : ℕ}
    (A : G n) (B : E n →L[ℝ] G n) (u v : E n) (hA : A.IsInvertible) :
    ContDiffAt ℝ ∞ (connectionRightFormula u) ((A, B), v) := by
  have hf : ContDiff ℝ ∞ (fun C : G n => C.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).contDiff
  have hf' : ContDiff ℝ ∞ (fun C : E n →L[ℝ] G n => C.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) (E n →L[ℝ] ℝ)).contDiff
  have hK : ContDiff ℝ ∞ (fun z : (G n × (E n →L[ℝ] G n)) × E n =>
      metricKoszulCovector z.1.2 u z.2) := by
    unfold metricKoszulCovector
    fun_prop
  have hI := hA.contDiffAt_map_inverse (n := ∞) |>.comp ((A, B), v)
    (show ContDiffAt ℝ ∞ (fun z : (G n × (E n →L[ℝ] G n)) × E n => z.1.1)
      ((A, B), v) by fun_prop)
  exact hI.clm_apply hK.contDiffAt



theorem euclideanConnection_field_contDiffAt {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g)
    (x u : E n) {Y : E n → E n} (hY : ContDiffAt ℝ ∞ Y x) :
    ContDiffAt ℝ ∞ (fun y => D.euclideanConnection u (Y y) y) x := by
  have hA : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have h := (connectionRightFormula_smooth _ _ u (Y x) hA).comp x
    (((g.contDiffAt_euclideanCoefficients x).prodMk
      ((g.contDiffAt_euclideanCoefficients x).fderiv_right (by simp))).prodMk hY)
  convert h using 1
  funext y
  exact D.connection_const_eq_inverse y u (Y y)



theorem euclideanConnection_field_jets_tendsto {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p u : E n) (r : ℕ)
    {Yseq : ℕ → E n → E n} {Y : E n → E n}
    (hY : ContDiffAt ℝ ∞ Y p) (hYs : ∀ k, ContDiffAt ℝ ∞ (Yseq k) (pseq k))
    (hjet : ∀ m ≤ r + 1, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p)))
    (hYjet : ∀ m ≤ r, Tendsto (fun k => iteratedFDeriv ℝ m (Yseq k) (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m Y p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => (Dseq k).euclideanConnection u (Yseq k y) y) (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun y => D.euclideanConnection u (Y y) y) p)) := by
  let jet (g' : RiemannianMetric n (E n)) (Z : E n → E n) (y : E n) :=
    ((g'.euclideanCoefficients y, fderiv ℝ g'.euclideanCoefficients y), Z y)
  have hs (g' : RiemannianMetric n (E n)) (Z : E n → E n) (y : E n)
      (hZ : ContDiffAt ℝ ∞ Z y) : ContDiffAt ℝ ∞ (jet g' Z) y :=
    ((g'.contDiffAt_euclideanCoefficients y).prodMk
      ((g'.contDiffAt_euclideanCoefficients y).fderiv_right (by simp))).prodMk hZ
  have hPhi (g' : RiemannianMetric n (E n)) (Z : E n → E n) (y : E n) :
      ContDiffAt ℝ ∞ (connectionRightFormula u) (jet g' Z y) := by
    apply connectionRightFormula_smooth
    convert! g'.inner_isInvertible y
  have hderiv (m : ℕ) (hm : m ≤ r) :
      Tendsto (fun k => iteratedFDeriv ℝ m (fderiv ℝ (gseq k).euclideanCoefficients)
        (pseq k)) atTop (𝓝 (iteratedFDeriv ℝ m (fderiv ℝ g.euclideanCoefficients) p)) := by
    let C := continuousMultilinearCurryRightEquiv' ℝ m (E n) (G n)
    have heq (f : E n → G n) (y : E n) :
        iteratedFDeriv ℝ m (fderiv ℝ f) y = C (iteratedFDeriv ℝ (m + 1) f y) := by
      rw [iteratedFDeriv_succ_eq_comp_right]
      exact (C.apply_symm_apply _).symm
    simp_rw [heq]
    exact (C.continuous.tendsto _).comp (hjet (m + 1) (by omega))
  have hpairs (m : ℕ) (hm : m ≤ r) := tendsto_iteratedFDeriv_prodMk_of_jets m
    (g.contDiffAt_euclideanCoefficients p)
    ((g.contDiffAt_euclideanCoefficients p).fderiv_right (by simp))
    (Eventually.of_forall fun k => (gseq k).contDiffAt_euclideanCoefficients (pseq k))
    (Eventually.of_forall fun k =>
      ((gseq k).contDiffAt_euclideanCoefficients (pseq k)).fderiv_right (by simp))
    (hjet m (by omega)) (hderiv m hm)
  have hall (m : ℕ) (hm : m ≤ r) := tendsto_iteratedFDeriv_prodMk_of_jets m
    ((g.contDiffAt_euclideanCoefficients p).prodMk
      ((g.contDiffAt_euclideanCoefficients p).fderiv_right (by simp))) hY
    (Eventually.of_forall fun k => ((gseq k).contDiffAt_euclideanCoefficients (pseq k)).prodMk
      (((gseq k).contDiffAt_euclideanCoefficients (pseq k)).fderiv_right (by simp)))
    (Eventually.of_forall hYs) (hpairs m hm) (hYjet m hm)
  have h := tendsto_iteratedFDeriv_smooth_comp_of_jets r (hs g Y p hY)
    (fun k => hs (gseq k) (Yseq k) (pseq k) (hYs k)) (hPhi g Y p)
    (fun k => hPhi (gseq k) (Yseq k) (pseq k)) hall
  have heq (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g') (Z : E n → E n) :
      connectionRightFormula u ∘ jet g' Z = fun y => D'.euclideanConnection u (Z y) y :=
    funext fun y => (D'.connection_const_eq_inverse y u (Z y)).symm
  rw [heq g D Y] at h
  exact h.congr' (Eventually.of_forall fun k => congrArg
    (fun f => iteratedFDeriv ℝ r f (pseq k)) (heq (gseq k) (Dseq k) (Yseq k)))


theorem curvature_contDiffAt_euclidean {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x u v w : E n) :
    ContDiffAt ℝ ∞ (fun y => D.curvature y u v w) x := by
  simp_rw [D.curvature_eq_euclideanConnection]
  have hd (a b c : E n) :=
    ((D.contDiffAt_euclideanConnection x a b).fderiv_right
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply
      (contDiffAt_const (c := c))
  have hc (a b c : E n) := euclideanConnection_field_contDiffAt D x a
    (D.contDiffAt_euclideanConnection x b c)
  exact ((hd v w u).add (hc u v w)).sub ((hd u w v).add (hc v u w))



theorem curvature_jets_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p u v w : E n) (r : ℕ)
    (hjet : ∀ m ≤ r + 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (Dseq k).curvature y u v w) (pseq k))
      atTop (𝓝 (iteratedFDeriv ℝ r (fun y => D.curvature y u v w) p)) := by
  have hc (a b : E n) (m : ℕ) (hm : m ≤ r + 1) :=
    euclideanConnection_jets_tendsto_of_metric_jets Dseq D pseq p a b m
      (fun l hl => hjet l (by omega))
  have hd (a b c : E n) := tendsto_iteratedFDeriv_fderiv_apply_of_jet r c
    (D.contDiffAt_euclideanConnection p a b)
    (Eventually.of_forall fun k => (Dseq k).contDiffAt_euclideanConnection (pseq k) a b)
    (hc a b (r + 1) le_rfl)
  have hn (a b c : E n) := euclideanConnection_field_jets_tendsto Dseq D pseq p a r
    (D.contDiffAt_euclideanConnection p b c)
    (fun k => (Dseq k).contDiffAt_euclideanConnection (pseq k) b c)
    (fun m hm => hjet m (by omega)) (fun m hm => hc b c m (by omega))
  have heq (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g') (y : E n) :
      iteratedFDeriv ℝ r (fun z => D'.curvature z u v w) y =
      (iteratedFDeriv ℝ r (fun z => fderiv ℝ (D'.euclideanConnection v w) z u) y +
        iteratedFDeriv ℝ r (fun z => D'.euclideanConnection u
          (D'.euclideanConnection v w z) z) y) -
      (iteratedFDeriv ℝ r (fun z => fderiv ℝ (D'.euclideanConnection u w) z v) y +
        iteratedFDeriv ℝ r (fun z => D'.euclideanConnection v
          (D'.euclideanConnection u w z) z) y) := by
    have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
    have hds (a b c : E n) :=
      ((D'.contDiffAt_euclideanConnection y a b).fderiv_right
        (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply
        (contDiffAt_const (c := c))
    have hns (a b c : E n) := euclideanConnection_field_contDiffAt D' y a
      (D'.contDiffAt_euclideanConnection y b c)
    simp_rw [D'.curvature_eq_euclideanConnection]
    rw [fun_iteratedFDeriv_sub_apply (((hds v w u).add (hns u v w)).of_le hr)
      (((hds u w v).add (hns v u w)).of_le hr),
      fun_iteratedFDeriv_add_apply ((hds v w u).of_le hr) ((hns u v w).of_le hr),
      fun_iteratedFDeriv_add_apply ((hds u w v).of_le hr) ((hns v u w).of_le hr)]
  simp_rw [heq]
  exact ((hd v w u).add (hn u v w)).sub ((hd u w v).add (hn v u w))


theorem curvatureTensor_contDiffAt_euclidean {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x u v w z : E n) :
    ContDiffAt ℝ ∞ (fun y => D.curvatureTensor y u v w z) x :=
  ((g.contDiffAt_euclideanCoefficients x).clm_apply
    (curvature_contDiffAt_euclidean D x u v z)).clm_apply contDiffAt_const



theorem curvatureTensor_jets_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p u v w z : E n) (r : ℕ)
    (hjet : ∀ m ≤ r + 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => (Dseq k).curvatureTensor y u v w z) (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun y => D.curvatureTensor y u v w z) p)) := by
  let Phi : G n × E n → ℝ := fun a => a.1 a.2 w
  have hPhi : ContDiff ℝ ∞ Phi := by fun_prop
  have hpairs (m : ℕ) (hm : m ≤ r) := tendsto_iteratedFDeriv_prodMk_of_jets m
    (g.contDiffAt_euclideanCoefficients p) (curvature_contDiffAt_euclidean D p u v z)
    (Eventually.of_forall fun k => (gseq k).contDiffAt_euclideanCoefficients (pseq k))
    (Eventually.of_forall fun k => curvature_contDiffAt_euclidean (Dseq k) (pseq k) u v z)
    (hjet m (by omega))
    (curvature_jets_tendsto_of_metric_jets Dseq D pseq p u v z m
      (fun l hl => hjet l (by omega)))
  exact tendsto_iteratedFDeriv_smooth_comp_of_jets r
    ((g.contDiffAt_euclideanCoefficients p).prodMk (curvature_contDiffAt_euclidean D p u v z))
    (fun k => ((gseq k).contDiffAt_euclideanCoefficients (pseq k)).prodMk
      (curvature_contDiffAt_euclidean (Dseq k) (pseq k) u v z))
    hPhi.contDiffAt (fun _ => hPhi.contDiffAt) hpairs

end PoincareConjecture.M35
