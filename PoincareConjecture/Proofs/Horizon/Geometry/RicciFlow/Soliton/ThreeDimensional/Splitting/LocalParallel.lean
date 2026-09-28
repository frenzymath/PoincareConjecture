import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.NullSections
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.NullSectionEnergy












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem exists_local_smooth_unit_ricci_null_section
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) {x : M}
    (hdim : ∀ᶠ y in 𝓝 x, ricciNullity D y = ricciNullity D x)
    (v : TangentSpace (𝓡 n) x) (hv : ∀ w, D.ricci x v w = 0)
    (hunit : g.inner x v v = 1) :
    ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
      IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U ∧ V x = v ∧
      ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧ ∀ w, D.ricci y (V y) w = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨U, V, hU, hx, hV, hVx, hnull⟩ :=
    exists_local_smooth_ricci_null_section D hD hdim v hv
  let q : M → ℝ := fun y => g.inner y (V y) (V y)
  have hq (y : M) (hy : y ∈ U) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ q y := by
    exact (hV.contMDiffAt (hU.mem_nhds hy)).inner_bundle
      (hV.contMDiffAt (hU.mem_nhds hy))
  have hqx : q x = 1 := by simp only [q, hVx, hunit]
  have hnear : ∀ᶠ y in 𝓝 x, 0 < q y :=
    (hq x hx).continuousAt.eventually (Ioi_mem_nhds (by rw [hqx]; norm_num))
  obtain ⟨O, hOq, hO, hxO⟩ := mem_nhds_iff.mp hnear
  let W : (y : M) → TangentSpace (𝓡 n) y :=
    fun y => (Real.sqrt (q y))⁻¹ • V y
  refine ⟨U ∩ O, W, hU.inter hO, ⟨hx, hxO⟩, ?_, ?_, ?_⟩
  · intro y hy
    have hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun z => Real.sqrt (q z)) y :=
      (Real.contDiffAt_sqrt (hOq hy.2).ne').contMDiffAt.comp y (hq y hy.1)
    have hi := (contDiffAt_inv ℝ (Real.sqrt_pos.mpr (hOq hy.2)).ne').contMDiffAt.comp y hs
    exact (hi.smul_section (hV.contMDiffAt (hU.mem_nhds hy.1))).contMDiffWithinAt
  · simp only [W, hqx, Real.sqrt_one, inv_one, one_smul, hVx]
  · intro y hy
    constructor
    · simp only [W, map_smul, smul_apply, smul_eq_mul]
      change (Real.sqrt (q y))⁻¹ * ((Real.sqrt (q y))⁻¹ * q y) = 1
      field_simp [(Real.sqrt_pos.mpr (hOq hy.2)).ne']
      exact (Real.sq_sqrt (hOq hy.2).le).symm
    · intro w
      rw [← ricciBilinear_apply]
      change ricciBilinear D y ((Real.sqrt (q y))⁻¹ • V y) w = 0
      rw [map_smul, LinearMap.smul_apply]
      rw [ricciBilinear_apply, hnull y hy.1 w, smul_zero]



theorem connection_eq_zero_of_terminal_unit_null
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hnull : ∀ᶠ y in 𝓝 x, ∀ w, (F.connection b).ricci y (V y) w = 0)
    (hunit : ∀ᶠ y in 𝓝 x, (F.metric b).inner y (V y) (V y) = 1)
    (hdim : ricciNullity (F.connection b) x = 1)
    (u : TangentSpace (𝓡 n) x) : (F.connection b).connection V x u = 0 := by
  let D := F.connection b
  let g := F.metric b
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hderiv : ∀ w, D.ricci x (D.connection V x u) w = 0 :=
    ricci_connection_eq_zero_of_terminal_null hC hab F hsec V hV
      (hnull.mono fun y hy => hy (V y)) u
  let v : ricciKernel D x := ⟨V x, (mem_ricciKernel D x _).mpr hnull.self_of_nhds⟩
  have hv : v ≠ 0 := by
    intro hz
    have heq : V x = 0 := congrArg Subtype.val hz
    have := hunit.self_of_nhds
    simp only [heq, map_zero] at this
    norm_num at this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hdim
    ⟨D.connection V x u, (mem_ricciKernel D x _).mpr hderiv⟩
  have hc' : c • V x = D.connection V x u := congrArg Subtype.val hc
  have h := D.metricCompatible.mvfderiv_inner_eq
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (hV.mdifferentiableAt (by simp)) (hV.mdifferentiableAt (by simp))
  change mvfderiv (𝓡 n) (fun y => g.inner y (V y) (V y)) x
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x) =
      g.inner x (D.connection V x (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x)) (V x) +
      g.inner x (V x) (D.connection V x (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u x)) at h
  rw [FiberBundle.extend_apply_self, Poincare.mvfderiv_eq_of_eventuallyEq hunit,
    mvfderiv_const] at h
  rw [← hc'] at h
  simp only [map_smul, smul_apply, smul_eq_mul, zero_apply] at h
  rw [hunit.self_of_nhds] at h
  have hc0 : c = 0 := by linarith
  simpa only [hc0, zero_smul] using hc'.symm



theorem exists_local_parallel_unit_ricci_null_section
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ y : M, ricciNullity (F.connection b) y = 1) (x : M) :
    ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
      IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U ∧
      ∀ y ∈ U, (F.metric b).inner y (V y) (V y) = 1 ∧
        (∀ w, (F.connection b).ricci y (V y) w = 0) ∧
        ∀ w, (F.connection b).connection V y w = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < ricciNullity (F.connection b) x by rw [hdim]; norm_num)
  have hz' : (z : TangentSpace (𝓡 n) x) ≠ 0 := fun he => hz (Subtype.ext he)
  let q := (F.metric b).inner x z z
  have hq : 0 < q := (F.metric b).pos x z hz'
  let v : TangentSpace (𝓡 n) x := (Real.sqrt q)⁻¹ • (z : TangentSpace (𝓡 n) x)
  have hv : ∀ w, (F.connection b).ricci x v w = 0 :=
    (mem_ricciKernel _ _ _).mp ((ricciKernel (F.connection b) x).smul_mem _ z.property)
  have hu : (F.metric b).inner x v v = 1 := by
    simp only [v, map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = 1
    field_simp [(Real.sqrt_pos.mpr hq).ne']
    exact (Real.sq_sqrt hq.le).symm
  obtain ⟨U, V, hU, hx, hV, _, hnull⟩ := exists_local_smooth_unit_ricci_null_section
    (F.connection b) (hC.tensor_calculus n M (F.metric b) (F.connection b))
    (Eventually.of_forall fun y => (hdim y).trans (hdim x).symm) v hv hu
  refine ⟨U, V, hU, hx, hV, fun y hy => ⟨(hnull y hy).1, (hnull y hy).2, ?_⟩⟩
  intro w
  exact connection_eq_zero_of_terminal_unit_null hC hab F hsec V
    (hV.contMDiffAt (hU.mem_nhds hy))
    (Filter.mem_of_superset (hU.mem_nhds hy) fun z hz => (hnull z hz).2)
    (Filter.mem_of_superset (hU.mem_nhds hy) fun z hz => (hnull z hz).1) (hdim y) w

end PoincareConjecture.RicciFlow.Splitting
