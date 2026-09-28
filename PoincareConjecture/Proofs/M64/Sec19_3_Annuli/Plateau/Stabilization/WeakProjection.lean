import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.RetainedObservation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityCharts












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "H" => EuclideanSpace ℝ (Fin k)



theorem auxiliaryCircle_retained_observation_mfderiv
    (P : M62.CircleProductData F circumference)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (o : P.charts.Point → H) (ho : ContMDiff (𝓡 (n + 1)) (𝓡 k) 1 o)
    (L : H →L[ℝ] E) (hL : ∀ q : P.charts.Point, L (o q) = e q.1)
    (q : P.charts.Point) (v : TangentSpace (𝓡 (n + 1)) q) :
    mfderiv (𝓡 n) (𝓡 m) e q.1 (P.charts.split q v).1 =
      L (mfderiv (𝓡 (n + 1)) (𝓡 k) o q v) := by
  let := P.charts.chartedSpace
  rw [P.charts.split_space]
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) 1
      (Prod.fst : P.charts.Point → M) :=
    (contMDiff_fst.comp P.charts.to_product_smooth).of_le (by simp)
  have hright := mfderiv_comp_apply (f := (Prod.fst : P.charts.Point → M))
    (g := e) q (he.mdifferentiableAt (by simp)) (hfst.mdifferentiableAt (by simp)) v
  have hLsmooth : ContMDiff (𝓡 k) (𝓡 m) 1 L := L.contDiff.contMDiff
  have hleft := mfderiv_comp_apply (f := o) (g := L) q
    (hLsmooth.mdifferentiableAt (by simp)) (ho.mdifferentiableAt (by simp)) v
  have hderiv : mfderiv (𝓡 k) (𝓡 m) L (o q) = L := by
    rw [mfderiv_eq_fderiv]
    exact L.fderiv
  rw [hderiv] at hleft
  have hmaps : L ∘ o = e ∘ (Prod.fst : P.charts.Point → M) := funext hL
  rw [hmaps] at hleft
  exact hright.symm.trans hleft



theorem auxiliaryCircle_projected_weak_annulus
    (P : M62.CircleProductData F circumference)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (o : P.charts.Point → H) (ho : ContMDiff (𝓡 (n + 1)) (𝓡 k) 1 o)
    (L : H →L[ℝ] E) (hL : ∀ q : P.charts.Point, L (o q) = e q.1)
    {c0 c1 : ℝ → P.charts.Point} (hc0 : Continuous c0) (hc1 : Continuous c1)
    (A : M64ObservedWeakAnnulus (n := n + 1) o c0 c1) :
    ∃ D : M64ObservedWeakAnnulus (n := n) e (fun x => (c0 x).1) (fun x => (c1 x).1),
      D.map = (fun p => (A.map p).1) ∧
        ∀ i, ∀ᵐ p ∂mu, D.column i p = L (A.column i p) := by
  let column : Fin 2 → Lp E 2 mu := fun i => L.compLp (A.column i)
  have hcolumn (i : Fin 2) : (column i : LoopPlane → E) =ᵐ[mu]
      (fun p => L (A.column i p)) :=
    L.coeFn_compLp (A.column i)
  have hobs : MemLp (fun p => e (A.map p).1) 2 mu := by
    apply (L.comp_memLp' A.observed_memLp).ae_eq
    exact Eventually.of_forall (fun p => hL (A.map p))
  have hint (i : Fin 2) (phi : LoopPlane → ℝ) :
      (∫ p in S, phi p • column i p) = ∫ p in S, phi p • L (A.column i p) :=
    integral_congr_ae ((hcolumn i).mono fun p hp => congrArg (phi p • ·) hp)
  let D : M64ObservedWeakAnnulus (n := n) e (fun x => (c0 x).1) (fun x => (c1 x).1) := {
    map := fun p => (A.map p).1
    observed_memLp := hobs
    column := column
    tangent := fun i => by
      filter_upwards [hcolumn i, A.tangent i] with p hp ht
      obtain ⟨v, hv⟩ := ht
      refine ⟨(P.charts.split (A.map p) v).1, ?_⟩
      rw [hp, ← hv]
      exact auxiliaryCircle_retained_observation_mfderiv P e he o ho L hL _ _
    weak_partial := fun i b => by
      apply m64WeakPartialDeriv_ae_congr
        (Eventually.of_forall fun p => congrArg (fun x : E => x b) (hL (A.map p)))
        ((hcolumn i).symm.mono fun p hp => congrArg (fun x : E => x b) hp)
      exact m64WeakPartial_comp_linear A.observed_memLp (Lp.memLp (A.column i))
        (A.weak_partial i) L b
    boundary := fun phi hphi => by
      let dphi := fun p => fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1)
      have hp := m64Annulus_continuous_memLp_two hphi.continuous
      have hdc : Continuous dphi :=
        (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
      have hdp := m64Annulus_continuous_memLp_two hdc
      have hIc := m64L2_test_integrable (Lp.memLp (A.column 1)) hp
      have hIv : Integrable (fun p =>
          fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • o (A.map p)) mu :=
        m64L2_test_integrable A.observed_memLp hdp
      have hoc := ho.continuous
      have hline (s : ℝ) : Continuous (fun x : ℝ => annulusPoint x s) := by
        unfold annulusPoint
        fun_prop
      have hbc : Continuous (fun x : ℝ =>
          phi (annulusPoint x 1) • o (c1 x) - phi (annulusPoint x 0) • o (c0 x)) := by
        exact ((hphi.continuous.comp (hline 1)).smul (hoc.comp hc1)).sub
          ((hphi.continuous.comp (hline 0)).smul (hoc.comp hc0))
      have hIb : IntegrableOn (fun x : ℝ =>
          phi (annulusPoint x 1) • o (c1 x) - phi (annulusPoint x 0) • o (c0 x))
          (Icc (0 : ℝ) curvePeriod) volume :=
        hbc.continuousOn.integrableOn_compact isCompact_Icc
      have h := congrArg L (A.boundary phi hphi)
      rw [map_add, ← L.integral_comp_comm hIc, ← L.integral_comp_comm hIv,
        ← L.integral_comp_comm hIb] at h
      simp only [map_smul, map_sub, hL] at h
      rw [hint]
      exact h
    seam := fun phi hphi hs => by
      let dphi := fun p => fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1)
      have hp := m64Annulus_continuous_memLp_two hphi.continuous
      have hdc : Continuous dphi :=
        (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
      have hdp := m64Annulus_continuous_memLp_two hdc
      have hIc := m64L2_test_integrable (Lp.memLp (A.column 0)) hp
      have hIv : Integrable (fun p =>
          fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) • o (A.map p)) mu :=
        m64L2_test_integrable A.observed_memLp hdp
      have h := congrArg L (A.seam phi hphi hs)
      rw [map_add, map_zero, ← L.integral_comp_comm hIc, ← L.integral_comp_comm hIv] at h
      simp only [map_smul, hL] at h
      rw [hint]
      exact h }
  exact ⟨D, rfl, hcolumn⟩

end PoincareConjecture.M64
