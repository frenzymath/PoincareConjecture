import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialLevel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open PoincareConjecture Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Curvature.Hypersurface

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)



theorem curvatureTensor_eq_one_of_radial_level_immersion
    {n : ℕ} {g : RiemannianMetric (n + 1) (E (n + 1))}
    {h : RiemannianMetric n (E n)} (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E n → E (n + 1)} {x : E n} {f : E (n + 1) → ℝ} {c : ℝ}
    (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hlevel : f ∘ F =ᶠ[𝓝 x] fun _ => c)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b,
      h.inner y a b = g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (hQ : D.levelQ f (F x) = 1)
    (hH : ∀ u v, D.hessian f (F x) u v = g.inner (F x) u v)
    (hflat : ∀ u v w z, D.curvatureTensor (F x) u v w z = 0)
    (u v w z : E n) :
    D'.curvatureTensor x u v w z =
      h.inner x u w * h.inner x v z - h.inner x u z * h.inner x v w := by
  have hnormal : ∀ᶠ y in 𝓝 x, ∀ a,
      g.inner (F y) (D.levelUnitNormal f (F y)) (fderiv ℝ F y a) = 0 := by
    obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp (hlevel.and hF)
    filter_upwards [hVo.mem_nhds hxV] with y hy a
    have heq : f ∘ F =ᶠ[𝓝 y] fun _ => c := by
      filter_upwards [hVo.mem_nhds hy] with s hs
      exact (hVsub hs).1
    have hFmd : MDifferentiableAt (𝓡 n) (𝓡 (n + 1)) F y :=
      mdifferentiableAt_iff_differentiableAt.mpr
        ((hVsub hy).2.differentiableAt (by simp))
    have hchain := mvfderiv_comp_apply y
      ((hf (F y)).mdifferentiableAt (by simp)) hFmd a
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq, mvfderiv_const] at hchain
    rw [mfderiv_eq_fderiv] at hchain
    rw [LeviCivitaData.levelUnitNormal]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [D.inner_gradient]
    change (Real.sqrt (D.levelQ f (F y)))⁻¹ *
      mvfderiv (𝓡 (n + 1)) f (F y) (fderiv ℝ F y a) = 0
    erw [← hchain]
    simp
  let N := D.levelUnitNormal f (F x)
  have hN : g.inner (F x) N N = 1 := by
    simp only [N, LeviCivitaData.levelUnitNormal, hQ, Real.sqrt_one, inv_one,
      one_smul]
    exact hQ
  have hreg : 0 < g.inner (F x) (D.gradient f (F x)) (D.gradient f (F x)) := by
    change 0 < D.levelQ f (F x)
    rw [hQ]
    norm_num
  have hshape (a b : E n) :
      h.inner x (shapeOperator D D' F x N a) b = -h.inner x a b := by
    rw [inner_shapeOperator_eq_neg_levelHessian D D' hF.self_of_nhds
      (hf (F x)) hreg N rfl hnormal.self_of_nhds hnormal, hH, hQ,
      Real.sqrt_one, div_one, ← hmetric.self_of_nhds]
  have hL := fderiv_injective_of_pullback_metric hmetric.self_of_nhds
  have hpair (a b c d : E n) :
      g.inner (F x) (secondFundamentalForm D D' F x a b)
        (secondFundamentalForm D D' F x c d) =
      h.inner x a b * h.inner x c d := by
    rw [metric_inner_normals_eq_mul g (F x) (fderiv ℝ F x).toLinearMap
      hL N hN hnormal.self_of_nhds _ _
      (secondFundamentalForm_normal D D' hF.self_of_nhds hmetric c d)]
    rw [g.symm (F x) (secondFundamentalForm D D' F x a b),
      g.symm (F x) (secondFundamentalForm D D' F x c d)]
    erw [← inner_shapeOperator, ← inner_shapeOperator, hshape, hshape, neg_mul_neg]
  rw [gauss_curvatureTensor_of_eventually D D' hF hmetric, hflat, hpair, hpair,
    zero_add]

end Poincare.Geometry.Curvature.Hypersurface

namespace PoincareConjecture.LeviCivitaData

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

variable {n : ℕ} {g : RiemannianMetric (n + 1) (E (n + 1))}
  (D : LeviCivitaData g) {f : E (n + 1) → ℝ}
  (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens (E (n + 1)))
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)

set_option maxHeartbeats 400000 in


theorem regularLevel_curvatureTensor_eq_one (c : ℝ) :
    letI : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    ∀ (D' : LeviCivitaData (RiemannianMetric.regularLevelMetric hf U hreg c g))
      (z : openLevelSet f U c),
      D.levelQ f (openLevelIncl f U c z) = 1 →
      (∀ u v, D.hessian f (openLevelIncl f U c z) u v =
        g.inner (openLevelIncl f U c z) u v) →
      (∀ u v w a, D.curvatureTensor (openLevelIncl f U c z) u v w a = 0) →
      ∀ u v w a : TangentSpace (𝓡 n) z,
      D'.curvatureTensor z u v w a =
        (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z u w *
          (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z v a -
        (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z u a *
          (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z v w := by
  let : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  intro D' z hQ hH hflat u v w a
  let h := RiemannianMetric.regularLevelMetric hf U hreg c g
  let ι := openLevelIncl f U c
  let C := extChartAt (𝓡 n) z
  let y := C z
  let F : E n → E (n + 1) := ι ∘ C.symm
  have hι : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ ι :=
    contMDiff_openLevelIncl hf U hreg n c
  have hp : C.symm y = z := C.left_inv (mem_extChartAt_source z)
  have hFy : F y = ι z := by simp only [F, Function.comp_apply, hp]
  have hC (s : E n) (hs : s ∈ C.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ C.symm s :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) z hs).contMDiffAt
      (extChartAt_target_mem_nhds' hs)
  have hF : ∀ᶠ s in 𝓝 y, ContDiffAt ℝ ∞ F s := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target z)] with s hs
    exact contMDiffAt_iff_contDiffAt.mp ((hι (C.symm s)).comp s (hC s hs))
  obtain ⟨hE, DE, hEeq⟩ := exists_chart_metric h z
  have hmetric : ∀ᶠ s in 𝓝 y, ∀ b d,
      hE.inner s b d = g.inner (F s) (fderiv ℝ F s b) (fderiv ℝ F s d) := by
    filter_upwards [hEeq, extChartAt_target_mem_nhds' (mem_extChartAt_target z)]
      with s hs hsC b d
    have hchain := mfderiv_comp s ((hι (C.symm s)).mdifferentiableAt (by simp))
      ((hC s hsC).mdifferentiableAt (by simp))
    have hderiv (v : E n) : fderiv ℝ F s v =
        mfderiv (𝓡 n) (𝓡 (n + 1)) ι (C.symm s)
          (mfderiv (𝓡 n) (𝓡 n) C.symm s v) := by
      rw [← mfderiv_eq_fderiv]
      exact congrArg (fun A => A v) hchain
    rw [hs, hderiv, hderiv]
    rfl
  have hlevel : f ∘ F =ᶠ[𝓝 y] fun _ => c := by
    exact Filter.Eventually.of_forall fun s => (C.symm s).property
  have hcoord := Poincare.Geometry.Curvature.Hypersurface.curvatureTensor_eq_one_of_radial_level_immersion
      D DE hF hf hlevel hmetric
      (by simpa only [hFy] using hQ)
      (by change ∀ b d : E (n + 1), _; rw [hFy]; exact hH)
      (by change ∀ b d e k : E (n + 1), _; rw [hFy]; exact hflat)
  have hinv : ∀ᶠ s in 𝓝 y,
      (mfderiv (𝓡 n) (𝓡 n) C.symm s).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target z)] with s hs
    exact Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm (p := z) hs
  have hback (v : TangentSpace (𝓡 n) z) :
      mfderiv (𝓡 n) (𝓡 n) C.symm y (mfderiv (𝓡 n) (𝓡 n) C z v) = v := by
    have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
      (I := 𝓡 n) (mem_extChartAt_source z)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
    exact congrArg (fun A => A v) hi
  have ht := hcoord (mfderiv (𝓡 n) (𝓡 n) C z u) (mfderiv (𝓡 n) (𝓡 n) C z v)
    (mfderiv (𝓡 n) (𝓡 n) C z w) (mfderiv (𝓡 n) (𝓡 n) C z a)
  rw [DE.curvatureTensor_eq_pullback_euclidean D'
    (hC y (mem_extChartAt_target z)) hinv hEeq] at ht
  have hinner (b d : TangentSpace (𝓡 n) z) :
      hE.inner y (mfderiv (𝓡 n) (𝓡 n) C z b) (mfderiv (𝓡 n) (𝓡 n) C z d) =
      h.inner z b d := by
    have hi := hEeq.self_of_nhds
      (mfderiv (𝓡 n) (𝓡 n) C z b) (mfderiv (𝓡 n) (𝓡 n) C z d)
    change hE.inner y _ _ = h.inner (C.symm y)
      (mfderiv (𝓡 n) (𝓡 n) C.symm y (mfderiv (𝓡 n) (𝓡 n) C z b))
      (mfderiv (𝓡 n) (𝓡 n) C.symm y (mfderiv (𝓡 n) (𝓡 n) C z d)) at hi
    erw [hback, hback, hp] at hi
    exact hi
  erw [hback, hback, hback, hback, hp, hinner, hinner, hinner, hinner] at ht
  exact ht



theorem radialLevel_curvatureTensor_eq_one
    (hH : ∀ x ∈ U, ∀ u v, D.hessian f x u v = g.inner x u v)
    (hQ : ∀ x ∈ U, D.levelQ f x = 2 * f x)
    (hflat : ∀ x ∈ U, ∀ u v w a, D.curvatureTensor x u v w a = 0) :
    letI : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg n (1 / 2)
    letI := isManifold_openLevelSet hf U hreg n (1 / 2)
    let h := RiemannianMetric.regularLevelMetric hf U hreg (1 / 2) g
    ∀ (z : openLevelSet f U (1 / 2)) (u v w a : TangentSpace (𝓡 n) z),
      h.leviCivitaData.curvatureTensor z u v w a =
        h.inner z u w * h.inner z v a - h.inner z u a * h.inner z v w := by
  let : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n (1 / 2)
  let := isManifold_openLevelSet hf U hreg n (1 / 2)
  intro h z u v w a
  exact D.regularLevel_curvatureTensor_eq_one hf U hreg (1 / 2) h.leviCivitaData z
    (by
      change D.levelQ f z.1.1 = 1
      rw [hQ _ z.1.property, show f z.1.1 = 1 / 2 from z.property]
      norm_num)
    (hH _ z.1.property) (hflat _ z.1.property) u v w a



theorem radialLevel_sectionalCurvature_eq_one
    (hH : ∀ x ∈ U, ∀ u v, D.hessian f x u v = g.inner x u v)
    (hQ : ∀ x ∈ U, D.levelQ f x = 2 * f x)
    (hflat : ∀ x ∈ U, ∀ u v w a, D.curvatureTensor x u v w a = 0) :
    letI : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg n (1 / 2)
    letI := isManifold_openLevelSet hf U hreg n (1 / 2)
    let h := RiemannianMetric.regularLevelMetric hf U hreg (1 / 2) g
    ∀ (z : openLevelSet f U (1 / 2)) (u v : TangentSpace (𝓡 n) z),
      h.inner z u u * h.inner z v v - h.inner z u v ^ 2 ≠ 0 →
      h.leviCivitaData.sectionalCurvature z u v = 1 := by
  let : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n (1 / 2)
  let := isManifold_openLevelSet hf U hreg n (1 / 2)
  intro h z u v hplane
  unfold sectionalCurvature
  rw [D.radialLevel_curvatureTensor_eq_one hf U hreg hH hQ hflat z u v u v,
    h.symm z v u, ← pow_two]
  exact div_self hplane





theorem exists_radialLevel_curvatureTensor_eq_one_of_local
    (hfLocal : ContMDiffOn (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f U)
    (hpos : ∀ x ∈ U, 0 < f x)
    (hH : ∀ x ∈ U, ∀ u v, D.hessian f x u v = g.inner x u v)
    (hQ : ∀ x ∈ U, D.levelQ f x = 2 * f x)
    (hflat : ∀ x ∈ U, D.curvatureTensorNorm x = 0)
    {x : E (n + 1)} (hx : x ∈ U) (hfx : f x = 1 / 2) :
    ∃ (ψ : E (n + 1) → ℝ) (hψ : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ ψ)
      (V : Opens (E (n + 1)))
      (hψreg : ∀ y ∈ V, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ψ y ≠ 0),
      x ∈ V ∧ V ≤ U ∧ EqOn ψ f V ∧ ψ x = 1 / 2 ∧
      (letI : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) :=
        ⟨finrank_euclideanSpace_fin⟩
       letI := openLevelSetChartedSpace hψ V hψreg n (1 / 2)
       letI := isManifold_openLevelSet hψ V hψreg n (1 / 2)
       let h := RiemannianMetric.regularLevelMetric hψ V hψreg (1 / 2) g
       ∀ (z : openLevelSet ψ V (1 / 2)) (u v w a : TangentSpace (𝓡 n) z),
         h.leviCivitaData.curvatureTensor z u v w a =
           h.inner z u w * h.inner z v a - h.inner z u a * h.inner z v w) := by
  obtain ⟨ψ, hψ, hψeq⟩ := Poincare.Manifold.exists_contMDiff_eq_near U.isOpen hfLocal hx
  obtain ⟨V₀, hV₀sub, hV₀o, hxV₀⟩ := mem_nhds_iff.mp hψeq
  let V : Opens (E (n + 1)) := ⟨V₀ ∩ U, hV₀o.inter U.isOpen⟩
  have hVU : V ≤ U := fun _ hy => hy.2
  have heq : EqOn ψ f V := fun y hy => hV₀sub hy.1
  have heqnear (y : E (n + 1)) (hy : y ∈ V) : ψ =ᶠ[𝓝 y] f := by
    filter_upwards [V.isOpen.mem_nhds hy] with s hs
    exact heq hs
  have hgrad (y : E (n + 1)) (hy : y ∈ V) : D.gradient ψ y = D.gradient f y := by
    simp only [gradient, Poincare.mvfderiv_eq_of_eventuallyEq (heqnear y hy)]
  have hQψ (y : E (n + 1)) (hy : y ∈ V) : D.levelQ ψ y = 2 * ψ y := by
    change g.inner y (D.gradient ψ y) (D.gradient ψ y) = _
    rw [hgrad y hy]
    change D.levelQ f y = _
    rw [hQ y (hVU hy), heq hy]
  have hψreg (y : E (n + 1)) (hy : y ∈ V) :
      mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ψ y ≠ 0 := by
    intro hz
    have hgzero : D.gradient ψ y = 0 :=
      (g.gradient_eq_zero_iff_mfderiv_eq_zero ψ y).mpr hz
    have hzero : D.levelQ ψ y = 0 := by
      simp [levelQ, hgzero]
    rw [hQψ y hy, heq hy] at hzero
    linarith [hpos y (hVU hy)]
  refine ⟨ψ, hψ, V, hψreg, ⟨hxV₀, hx⟩, hVU, heq, hψeq.self_of_nhds.trans hfx, ?_⟩
  apply D.radialLevel_curvatureTensor_eq_one hψ V hψreg
  · intro y hy u v
    rw [D.hessian_eq_of_eventuallyEq (heqnear y hy)]
    exact hH y (hVU hy) u v
  · exact hQψ
  · intro y hy u v w a
    apply abs_nonpos_iff.mp
    simpa only [hflat y (hVU hy), zero_mul] using
      D.abs_curvatureTensor_le_tangentNorm y u v w a

end PoincareConjecture.LeviCivitaData
