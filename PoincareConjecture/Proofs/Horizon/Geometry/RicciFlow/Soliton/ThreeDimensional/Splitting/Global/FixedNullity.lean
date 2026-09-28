import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.Persistence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

open RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem ricciKernel_eq_initial_of_constant_nullity
    (hC : RicciFlowCurvatureTheory.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ t ∈ Icc a b, ∀ x,
      ricciNullity (F.connection t) x = ricciNullity (F.connection a) x)
    (t : ℝ) (ht : t ∈ Icc a b) (x : M) :
    ricciKernel (F.connection t) x = ricciKernel (F.connection a) x := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  apply Submodule.eq_of_le_of_finrank_eq
    (ricciKernel_antitoneOn hC hab F hsec x ⟨le_rfl, hab.le⟩ ht ht.1)
  exact hdim t ht x

theorem parallel_gradient_persists_of_constant_nullity
    (hC : RicciFlowCurvatureTheory.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ t ∈ Icc a b, ∀ x,
      ricciNullity (F.connection t) x = ricciNullity (F.connection a) x)
    {r : M → ℝ} (hr : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ r)
    (hu : HasUnitGradient (F.connection a) r)
    (hz : HasZeroHessian (F.connection a) r) :
    ∀ t ∈ Icc a b,
      (F.connection t).gradient r = (F.connection a).gradient r ∧
        HasUnitGradient (F.connection t) r ∧ HasZeroHessian (F.connection t) r := by
  let V := (F.connection a).gradient r
  have hV := (F.connection a).contMDiff_gradient hr
  have hpar0 (x : M) : (F.connection a).connection V x = 0 := by
    ext v
    exact connection_gradient_eq_zero_of_hasZeroHessian hr hz x v
  have hn0 (x : M) : V x ∈ ricciKernel (F.connection a) x := by
    rw [mem_ricciKernel]
    exact ricci_eq_zero_of_parallel_field (F.connection a)
      (hC.tensor_calculus n M (F.metric a) (F.connection a)) V hV hpar0 x
  have hn (t : ℝ) (ht : t ∈ Icc a b) (x : M) (v : TangentSpace (𝓡 n) x) :
      (F.connection t).ricci x (V x) v = 0 := by
    apply (mem_ricciKernel (F.connection t) x (V x)).mp
    rw [ricciKernel_eq_initial_of_constant_nullity hC hab F hsec hdim t ht x]
    exact hn0 x
  have hconn := connection_eq_terminal_of_ricci_null hC hab F hsec V hV
    (fun t ht x => hn t ⟨ht.1.le, ht.2⟩ x (V x))
  have hpar (t : ℝ) (ht : t ∈ Icc a b) (x : M) :
      (F.connection t).connection V x = 0 := by
    rw [hconn t ht x, ← hconn a ⟨le_rfl, hab.le⟩ x]
    exact hpar0 x
  have hmetric (t : ℝ) (ht : t ∈ Icc a b) (x : M) (v : TangentSpace (𝓡 n) x) :
      (F.metric t).inner x (V x) v = (F.metric a).inner x (V x) v := by
    let q : ℝ → ℝ := fun s => (F.metric s).inner x (V x) v
    have hd (s : ℝ) (hs : s ∈ Icc a b) : HasDerivWithinAt q 0 (Icc a b) s := by
      simpa only [q, hn s hs x v, mul_zero] using F.equation s hs x (V x) v
    have hdiff : DifferentiableOn ℝ q (Icc a b) := fun s hs => (hd s hs).differentiableWithinAt
    have hzero (s : ℝ) (hs : s ∈ Ico a b) : derivWithin q (Icc a b) s = 0 :=
      (hd s ⟨hs.1, hs.2.le⟩).derivWithin (uniqueDiffOn_Icc hab s ⟨hs.1, hs.2.le⟩)
    exact (constant_of_derivWithin_zero hdiff hzero t ht).trans
      (constant_of_derivWithin_zero hdiff hzero a ⟨le_rfl, hab.le⟩).symm
  have hgrad (t : ℝ) (ht : t ∈ Icc a b) : (F.connection t).gradient r = V := by
    funext x
    apply (F.metric t).inner_isInvertible x |>.injective
    ext v
    rw [(F.connection t).gradient_eq_metric_gradient]
    exact ((F.metric t).inner_gradient r x v).trans
      ((hmetric t ht x v).trans ((F.metric a).inner_gradient r x v)).symm
  intro t ht
  refine ⟨hgrad t ht, ?_, ?_⟩
  · intro x
    rw [hgrad t ht, hmetric t ht x (V x)]
    exact hu x
  · intro x v w
    rw [(F.connection t).hessian_eq_inner_connection_gradient (hr x), hgrad t ht,
      hpar t ht x]
    simp

end PoincareConjecture.RicciFlow.Splitting
