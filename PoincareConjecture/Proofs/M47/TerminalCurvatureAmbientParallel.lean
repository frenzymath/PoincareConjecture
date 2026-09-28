import PoincareConjecture.Proofs.M47.TerminalCurvatureOpenInclusion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.LocalParallel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace VectorField
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open RicciFlow.Splitting Poincare.Geometry.Manifold.RegularLevel

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem terminalCurvature_parallel_from_open_germ
    (D : LeviCivitaData g) (hC : RicciFlowCurvatureTheory.{u})
    (U : Opens M) {a : ℝ} (ha : a < 0) (F : RicciFlow n U (Icc a 0))
    (hmetric : ∀ (y : U) (v w : TangentSpace (𝓡 n) y),
      (F.metric 0).inner y v w = g.inner y.val v w)
    (hsec : ∀ t ∈ Icc a 0, (F.connection t).NonnegativeSectionalCurvature)
    (V : (y : M) → TangentSpace (𝓡 n) y) (x : U)
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x.val)
    (hnull : ∀ᶠ y in 𝓝 x.val, ∀ w, D.ricci y (V y) w = 0)
    (hunit : ∀ᶠ y in 𝓝 x.val, g.inner y (V y) (V y) = 1)
    (hrank : ricciNullity D x.val = 1) (v : TangentSpace (𝓡 n) x.val) :
    D.connection V x.val v = 0 := by
  let W := mpullback (𝓡 n) (𝓡 n) (Subtype.val : U → M) V
  have hread := terminalCurvature_open_inclusion_readouts D U (F.connection 0) hmetric
  have hi : (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x).IsInvertible := by
    rw [mfderiv_opens_subtypeVal]
    exact ⟨ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)), rfl⟩
  have hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) x :=
    hV.mpullback_vectorField_preimage (contMDiff_subtype_val (n := ∞)).contMDiffAt
      hi (by simp)
  have hn : ∀ᶠ y : U in 𝓝 x, ∀ w, (F.connection 0).ricci y (W y) w = 0 := by
    filter_upwards [continuous_subtype_val.continuousAt hnull] with y hy
    intro w
    rw [show W y = V y.val from terminalCurvature_open_mpullback U V y,
      (hread y).2.2.1]
    exact hy w
  have hu : ∀ᶠ y : U in 𝓝 x, (F.metric 0).inner y (W y) (W y) = 1 := by
    filter_upwards [continuous_subtype_val.continuousAt hunit] with y hy
    rw [show W y = V y.val from terminalCurvature_open_mpullback U V y, hmetric]
    exact hy
  have hz := connection_eq_zero_of_terminal_unit_null hC ha F hsec W hW hn hu
    ((hread x).2.2.2.2.trans hrank) v
  have he := terminalCurvature_open_connection D U (F.connection 0) hmetric V x
    (hV.mdifferentiableAt (by simp)) v
  exact he.symm.trans hz

theorem terminalCurvature_ambient_local_parallel
    (D : LeviCivitaData g) (hC : RicciFlowCurvatureTheory.{u})
    (hrank : ∀ y, ricciNullity D y = 1)
    {ι : Type*} (U : ι → Opens M) (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow n (U i) (Icc (-tau i) 0))
    (hmetric : ∀ i (y : U i) (v w : TangentSpace (𝓡 n) y),
      ((F i).metric 0).inner y v w = g.inner y.val v w)
    (hsec : ∀ i t, t ∈ Icc (-tau i) 0 → ((F i).connection t).NonnegativeSectionalCurvature)
    (hcover : ∀ y : M, ∃ i, y ∈ U i) (x : M) :
    ∃ (O : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
      IsOpen O ∧ x ∈ O ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) O ∧
      ∀ y ∈ O, g.inner y (V y) (V y) = 1 ∧
        (∀ w, D.ricci y (V y) w = 0) ∧ ∀ w, D.connection V y w = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < ricciNullity D x by rw [hrank]; norm_num)
  have hz' : (z : TangentSpace (𝓡 n) x) ≠ 0 := fun he => hz (Subtype.ext he)
  let q := g.inner x z z
  have hq : 0 < q := g.pos x z hz'
  let v : TangentSpace (𝓡 n) x := (Real.sqrt q)⁻¹ • (z : TangentSpace (𝓡 n) x)
  have hv : ∀ w, D.ricci x v w = 0 :=
    (mem_ricciKernel _ _ _).mp ((ricciKernel D x).smul_mem _ z.property)
  have hu : g.inner x v v = 1 := by
    simp only [v, map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = 1
    field_simp [(Real.sqrt_pos.mpr hq).ne']
    exact (Real.sq_sqrt hq.le).symm
  obtain ⟨O, V, hO, hx, hV, _, hnull⟩ := exists_local_smooth_unit_ricci_null_section
    D (hC.tensor_calculus n M g D)
    (Eventually.of_forall fun y => (hrank y).trans (hrank x).symm) v hv hu
  refine ⟨O, V, hO, hx, hV, fun y hy => ⟨(hnull y hy).1, (hnull y hy).2, ?_⟩⟩
  intro w
  obtain ⟨i, hi⟩ := hcover y
  exact terminalCurvature_parallel_from_open_germ D hC (U i)
    (show -tau i < 0 by linarith [htau i]) (F i) (hmetric i) (hsec i) V ⟨y, hi⟩
    (hV.contMDiffAt (hO.mem_nhds hy))
    (mem_of_superset (hO.mem_nhds hy) fun z hz => (hnull z hz).2)
    (mem_of_superset (hO.mem_nhds hy) fun z hz => (hnull z hz).1) (hrank y) w

end PoincareConjecture.M47
