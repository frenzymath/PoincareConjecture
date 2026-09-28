import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.PartialTraceEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.Positive










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RicciFlow.Splitting

open Poincare.RicciFlow.Splitting MaximumPrinciple

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


def ricciKernel (D : LeviCivitaData g) (x : M) :
    Submodule ℝ (TangentSpace (𝓡 n) x) := (ricciBilinear D x).ker


def ricciNullity (D : LeviCivitaData g) (x : M) : ℕ :=
  Module.finrank ℝ (ricciKernel D x)

@[simp] theorem mem_ricciKernel (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    v ∈ ricciKernel D x ↔ ∀ w : TangentSpace (𝓡 n) x, D.ricci x v w = 0 := by
  change ricciBilinear D x v = 0 ↔ _
  constructor
  · intro h w
    simpa only [ricciBilinear_apply, LinearMap.zero_apply] using congrArg (fun A => A w) h
  · intro h
    ext w
    simpa only [ricciBilinear_apply, LinearMap.zero_apply] using h w

theorem metricRicciOperator_ker (D : LeviCivitaData g) (x : M) :
    (metricRicciOperator D x).ker = ricciKernel D x := by
  ext v
  rw [mem_ricciKernel]
  change metricRicciOperator D x v = 0 ↔ _
  constructor
  · intro hv w
    rw [← metricRicciOperator_inner, hv, map_zero, zero_apply]
  · intro hv
    apply (g.inner_isInvertible x).injective
    ext w
    rw [map_zero, zero_apply, metricRicciOperator_inner]
    exact hv w

theorem ricciNullity_le (D : LeviCivitaData g) (x : M) : ricciNullity D x ≤ n := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
  exact (Submodule.finrank_le (ricciKernel D x)).trans_eq hdim

theorem ricciPartialTrace_eq_zero_iff_nullity (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    {k : ℕ} (hk : k ≤ n) : ricciPartialTrace D k x = 0 ↔ k ≤ ricciNullity D x := by
  rw [ricciPartialTrace_eq_zero_iff D hD x hk hRic]
  rw [metricRicciOperator_ker]
  rfl

variable [T2Space M]



theorem ricciNullity_eq_of_heatLowerContacts
    {U : Set M} (hU : IsOpen U) (hconn : IsConnected U)
    {g : ℝ → RiemannianMetric n M} (D : ∀ t, LeviCivitaData (g t))
    {a b : ℝ} (hg : RiemannianMetric.IsSmoothFamilyOn g (Icc a b))
    (hD : ∀ t ∈ Icc a b, (D t).CurvatureTensorCalculus)
    (hRic : ∀ t ∈ Icc a b, ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (D t).ricci x v v)
    (hv : ∀ k ≤ n, ContinuousOn
      (fun z : M × ℝ => ricciPartialTrace (D z.2) k z.1) (U ×ˢ Icc a b))
    (hvs : ∀ k ≤ n, HeatLowerContacts D U (Ioo a b)
      (fun x t => ricciPartialTrace (D t) k x))
    {t : ℝ} (ht : t ∈ Ioc a b) {p q : M} (hp : p ∈ U) (hq : q ∈ U) :
    ricciNullity (D t) p = ricciNullity (D t) q := by
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
  have hthreshold (k : ℕ) (hk : k ≤ n) :
      k ≤ ricciNullity (D t) p ↔ k ≤ ricciNullity (D t) q := by
    rw [← ricciPartialTrace_eq_zero_iff_nullity (D t) (hD t ht') p (hRic t ht' p hp) hk,
      ← ricciPartialTrace_eq_zero_iff_nullity (D t) (hD t ht') q (hRic t ht' q hq) hk]
    exact eq_zero_at_positive_time_iff hU hconn D hg (hv k hk) (hvs k hk)
      (fun x hx s hs => ricciPartialTrace_nonneg (D s) (hD s hs) x hk (hRic s hs x hx))
      ht hp hq
  exact le_antisymm
    ((hthreshold _ (ricciNullity_le (D t) p)).mp le_rfl)
    ((hthreshold _ (ricciNullity_le (D t) q)).mpr le_rfl)


theorem ricciNullity_antitoneOn_of_heatLowerContacts
    {U : Set M} (hU : IsOpen U) (hconn : IsConnected U)
    {g : ℝ → RiemannianMetric n M} (D : ∀ t, LeviCivitaData (g t))
    {a b : ℝ} (hg : RiemannianMetric.IsSmoothFamilyOn g (Icc a b))
    (hD : ∀ t ∈ Icc a b, (D t).CurvatureTensorCalculus)
    (hRic : ∀ t ∈ Icc a b, ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (D t).ricci x v v)
    (hv : ∀ k ≤ n, ContinuousOn
      (fun z : M × ℝ => ricciPartialTrace (D z.2) k z.1) (U ×ˢ Icc a b))
    (hvs : ∀ k ≤ n, HeatLowerContacts D U (Ioo a b)
      (fun x t => ricciPartialTrace (D t) k x))
    {p : M} (hp : p ∈ U) : AntitoneOn (fun t => ricciNullity (D t) p) (Icc a b) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with heq | hlt
  · subst t
    exact le_rfl
  let k := ricciNullity (D t) p
  have hk : k ≤ n := ricciNullity_le (D t) p
  have hzero : ricciPartialTrace (D t) k p = 0 :=
    (ricciPartialTrace_eq_zero_iff_nullity (D t) (hD t ht) p (hRic t ht p hp) hk).mpr le_rfl
  apply (ricciPartialTrace_eq_zero_iff_nullity (D s) (hD s hs) p (hRic s hs p hp) hk).mp
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  exact eq_zero_on_Icc_of_eq_zero hU hconn D hlt (hg.mono (prod_mono_left hsub))
    ((hv k hk).mono (prod_mono_right hsub))
    (fun x hx r hr => hvs k hk x hx r ⟨hs.1.trans_lt hr.1, hr.2.trans_le ht.2⟩)
    (fun x hx r hr => ricciPartialTrace_nonneg (D r) (hD r (hsub hr)) x hk
      (hRic r (hsub hr) x hx))
    hp hzero ⟨le_rfl, hlt.le⟩ hp

end PoincareConjecture.RicciFlow.Splitting
