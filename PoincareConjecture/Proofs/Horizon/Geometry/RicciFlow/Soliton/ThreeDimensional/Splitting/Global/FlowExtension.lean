import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.FixedNullity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Source
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Components
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.UnscaledSource
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Normal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.CurvatureTensor










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

universe u

namespace PoincareConjecture.RicciFlow.Splitting

open RiemannianMetric Poincare.Geometry.RicciFlow.Harnack

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem exists_negative_slab (t : ℝ) (ht : t < 0) :
    ∃ a b : ℝ, a < b ∧ b < 0 ∧ t ∈ Icc a b ∧ (-1 : ℝ) ∈ Icc a b := by
  refine ⟨min t (-1) - 1, max t (-1), ?_, max_lt ht (by norm_num), ?_, ?_⟩
  · have h₁ := min_le_left t (-1)
    have h₂ := le_max_left t (-1)
    linarith
  · exact ⟨by linarith [min_le_left t (-1)], le_max_left t (-1)⟩
  · exact ⟨by linarith [min_le_right t (-1)], le_max_right t (-1)⟩



theorem ricciKernel_eq_minus_one_of_constant_nullity
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iio 0))
    (hsec : ∀ t < 0, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ t < 0, ∀ x,
      ricciNullity (F.connection t) x = ricciNullity (F.connection (-1)) x)
    (t : ℝ) (ht : t < 0) (x : M) :
    ricciKernel (F.connection t) x = ricciKernel (F.connection (-1)) x := by
  obtain ⟨a, b, hab, hb, hta, hma⟩ := exists_negative_slab t ht
  let F' := restrictFlow F (show Icc a b ⊆ Iio 0 from fun s hs => hs.2.trans_lt hb)
    ordConnected_Icc ⟨a, ⟨le_rfl, hab.le⟩, b, ⟨hab.le, le_rfl⟩, hab.ne⟩
  have hsec' (s : ℝ) (hs : s ∈ Icc a b) :
      (F'.connection s).NonnegativeSectionalCurvature := hsec s (hs.2.trans_lt hb)
  have hdim' (s : ℝ) (hs : s ∈ Icc a b) (y : M) :
      ricciNullity (F'.connection s) y = ricciNullity (F'.connection a) y :=
    (hdim s (hs.2.trans_lt hb) y).trans (hdim a (hab.trans hb) y).symm
  exact (ricciKernel_eq_initial_of_constant_nullity hC hab F' hsec' hdim' t hta x).trans
    (ricciKernel_eq_initial_of_constant_nullity hC hab F' hsec' hdim' (-1) hma x).symm



theorem parallel_gradient_persists_on_negative_times
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iio 0))
    (hsec : ∀ t < 0, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ t < 0, ∀ x,
      ricciNullity (F.connection t) x = ricciNullity (F.connection (-1)) x)
    {r : M → ℝ} (hr : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ r)
    (hu : HasUnitGradient (F.connection (-1)) r)
    (hz : HasZeroHessian (F.connection (-1)) r) :
    ∀ t < 0,
      (F.connection t).gradient r = (F.connection (-1)).gradient r ∧
        HasUnitGradient (F.connection t) r ∧ HasZeroHessian (F.connection t) r := by
  let V := (F.connection (-1)).gradient r
  have hV := (F.connection (-1)).contMDiff_gradient hr
  have hpar0 (x : M) : (F.connection (-1)).connection V x = 0 := by
    ext v
    exact connection_gradient_eq_zero_of_hasZeroHessian hr hz x v
  have hn0 (x : M) : V x ∈ ricciKernel (F.connection (-1)) x := by
    rw [mem_ricciKernel]
    exact ricci_eq_zero_of_parallel_field (F.connection (-1))
      (hC.tensor_calculus n M (F.metric (-1)) (F.connection (-1))) V hV hpar0 x
  have hn (t : ℝ) (ht : t < 0) (x : M) (v : TangentSpace (𝓡 n) x) :
      (F.connection t).ricci x (V x) v = 0 := by
    apply (mem_ricciKernel (F.connection t) x (V x)).mp
    rw [ricciKernel_eq_minus_one_of_constant_nullity hC F hsec hdim t ht x]
    exact hn0 x
  have hpar (t : ℝ) (ht : t < 0) (x : M) :
      (F.connection t).connection V x = 0 := by
    obtain ⟨a, b, hab, hb, hta, hma⟩ := exists_negative_slab t ht
    let F' := restrictFlow F (show Icc a b ⊆ Iio 0 from fun s hs => hs.2.trans_lt hb)
      ordConnected_Icc ⟨a, ⟨le_rfl, hab.le⟩, b, ⟨hab.le, le_rfl⟩, hab.ne⟩
    have hconn := connection_eq_terminal_of_ricci_null hC hab F'
      (fun s hs => hsec s (hs.2.trans_lt hb)) V hV
      (fun s hs y => hn s (hs.2.trans_lt hb) y (V y))
    exact (hconn t hta x).trans ((hconn (-1) hma x).symm.trans (hpar0 x))
  have hmetric (t : ℝ) (ht : t < 0) (x : M) (v : TangentSpace (𝓡 n) x) :
      (F.metric t).inner x (V x) v = (F.metric (-1)).inner x (V x) v := by
    have hd (s : ℝ) (hs : s < 0) :
        HasDerivAt (fun q => (F.metric q).inner x (V x) v) 0 s := by
      simpa only [hn s hs x v, mul_zero] using
        (F.equation s hs x (V x) v).hasDerivAt (isOpen_Iio.mem_nhds hs)
    exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) ht (by norm_num : (-1 : ℝ) < 0)
  have hgrad (t : ℝ) (ht : t < 0) : (F.connection t).gradient r = V := by
    funext x
    apply (F.metric t).inner_isInvertible x |>.injective
    ext v
    rw [(F.connection t).gradient_eq_metric_gradient]
    exact ((F.metric t).inner_gradient r x v).trans
      ((hmetric t ht x v).trans ((F.metric (-1)).inner_gradient r x v)).symm
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

namespace PoincareConjecture.LeviCivitaData

open RicciFlow.Splitting

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem ricci_eq_scalar_transverse_of_null_direction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (N : TangentSpace (𝓡 3) x) (hN : g.inner x N N = 1)
    (hzero : ∀ u v w, D.curvatureTensor x N u v w = 0)
    (u v : TangentSpace (𝓡 3) x) :
    D.ricci x u v = (D.scalarCurvature x / 2) *
      (g.inner x u v - g.inner x N u * g.inner x N v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  have hframe : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => N)) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    have hij : i = j := Subtype.ext (i.2.trans j.2.symm)
    rw [if_pos hij]
    exact hN
  obtain ⟨b, hb⟩ := hframe.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (TangentSpace (𝓡 3) x) = Fintype.card (Fin 3) from
      finrank_euclideanSpace_fin)
  have hb0 : b 0 = N := hb 0 (by simp)
  have z₁ (u v w) : D.curvatureTensor x (b 0) u v w = 0 := by rw [hb0]; exact hzero u v w
  have z₂ (u v w) : D.curvatureTensor x u (b 0) v w = 0 := by
    rw [D.curvatureTensor_swap_first, z₁, neg_zero]
  have z₃ (u v w) : D.curvatureTensor x u v (b 0) w = 0 := by
    rw [(hD.2.2.2.1 x u v (b 0) w).2.1, z₁]
  have d₁ (u v w) : D.curvatureTensor x u u v w = 0 := by
    linarith [D.curvatureTensor_swap_first x u u v w]
  have d₂ (u v w) : D.curvatureTensor x u v w w = 0 := by
    linarith [D.curvatureTensor_swap_last x u v w w]
  let K := D.curvatureTensor x (b 1) (b 2) (b 1) (b 2)
  have hswap : D.curvatureTensor x (b 2) (b 1) (b 2) (b 1) = K := by
    rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last x (b 1) (b 2), neg_neg]
  have hric (i j : Fin 3) : D.ricci x (b i) (b j) =
      if i = j ∧ i ≠ 0 then K else 0 := by
    rw [D.ricci_eq_sum_orthonormalBasis hD x b]
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_succ, z₁, z₂, z₃, d₁, d₂, hswap, K]
  have hR : D.scalarCurvature x = 2 * K := by
    rw [D.scalarCurvature_eq_sum_orthonormalBasis x b]
    simp [Fin.sum_univ_succ, z₁, z₂, d₁, hswap, K]
    ring
  have hbinner (i j : Fin 3) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  rw [hR, ← hb0, ← ricciBilinear_apply D x u v, ← b.sum_repr' u, ← b.sum_repr' v]
  simp [Fin.sum_univ_succ, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    ricciBilinear_apply, hric, hbinner]
  ring

theorem ricci_eq_scalar_transverse_of_parallel_gradient
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {r : M → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (hu : RiemannianMetric.HasUnitGradient D r)
    (hz : RiemannianMetric.HasZeroHessian D r)
    (x : M) (u v : TangentSpace (𝓡 3) x) :
    D.ricci x u v = (D.scalarCurvature x / 2) *
      (g.inner x u v - mvfderiv (𝓡 3) r x u * mvfderiv (𝓡 3) r x v) := by
  have h := D.ricci_eq_scalar_transverse_of_null_direction hD x (D.gradient r x)
    (hu x) (RiemannianMetric.curvatureTensor_gradient_first_eq_zero hr hz x) u v
  simpa only [D.gradient_eq_metric_gradient, g.inner_gradient] using h

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow.Splitting

open RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem inner_eq_transverse_scale_on_negative_times
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iio 0))
    (hsec : ∀ t < 0, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ t < 0, ∀ x,
      ricciNullity (F.connection t) x = ricciNullity (F.connection (-1)) x)
    (hscalar : ∀ t < 0, ∀ x, (F.connection t).scalarCurvature x = -(t⁻¹))
    {r : M → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (hu : HasUnitGradient (F.connection (-1)) r)
    (hz : HasZeroHessian (F.connection (-1)) r)
    (t : ℝ) (ht : t < 0) (x : M) (u v : TangentSpace (𝓡 3) x) :
    (F.metric t).inner x u v =
      (-t) * ((F.metric (-1)).inner x u v -
        mvfderiv (𝓡 3) r x u * mvfderiv (𝓡 3) r x v) +
          mvfderiv (𝓡 3) r x u * mvfderiv (𝓡 3) r x v := by
  let c := mvfderiv (𝓡 3) r x u * mvfderiv (𝓡 3) r x v
  have hp := parallel_gradient_persists_on_negative_times hC F hsec hdim hr hu hz
  have hd (s : ℝ) (hs : s < 0) :
      HasDerivAt (fun q => (F.metric q).inner x u v - c)
        (((F.metric s).inner x u v - c) / s) s := by
    have hR := (F.connection s).ricci_eq_scalar_transverse_of_parallel_gradient
      (hC.tensor_calculus 3 M (F.metric s) (F.connection s)) hr
      (hp s hs).2.1 (hp s hs).2.2 x u v
    have hder := ((F.equation s hs x u v).hasDerivAt
      (isOpen_Iio.mem_nhds hs)).sub_const c
    rw [hR, hscalar s hs x] at hder
    convert hder using 1 <;> first | rfl | (dsimp [c]; ring)
  have hquot (s : ℝ) (hs : s < 0) :
      HasDerivAt (fun q => ((F.metric q).inner x u v - c) / q) 0 s := by
    have hder := (hd s hs).div (hasDerivAt_id s) hs.ne
    convert hder using 1 <;> first | rfl | simp [hs.ne]
  have heq := isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
    (fun s hs => (hquot s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hquot s hs).deriv) ht (by norm_num : (-1 : ℝ) < 0)
  have hmul := (div_eq_iff ht.ne).mp heq
  simp only [div_neg, div_one] at hmul
  dsimp [c] at hmul ⊢
  nlinarith

end PoincareConjecture.RicciFlow.Splitting

namespace PoincareConjecture.ShrinkingSolitonFlow

open RicciFlow.Splitting RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)



theorem scalarCurvature_eq_neg_inv_of_initial_scalar_one
    (hscalar : ∀ x : M, S.connection.scalarCurvature x = 1)
    (t : ℝ) (ht : t < 0) (x : M) :
    (G.flow.connection t).scalarCurvature x = -(t⁻¹) := by
  obtain ⟨E⟩ := G.self_similar t ht
  rw [E.scalarCurvature (abs_pos.mpr ht.ne) S.connection, hscalar, mul_one,
    abs_of_neg ht, inv_neg]



theorem inner_eq_transverse_scale_of_initial_scalar_one
    (hC : RicciFlowCurvatureTheory.{u})
    (p : M) (a b : TangentSpace (𝓡 3) p)
    (ha : S.metric.inner p a a = 1) (hb : S.metric.inner p b b = 1)
    (hab : S.metric.inner p a b = 0)
    (hzero : S.connection.curvatureTensor p a b a b = 0)
    (hscalar : ∀ x : M, S.connection.scalarCurvature x = 1)
    {r : M → ℝ} (hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r)
    (hu : HasUnitGradient (G.flow.connection (-1)) r)
    (hz : HasZeroHessian (G.flow.connection (-1)) r)
    (t : ℝ) (ht : t < 0) (x : M) (u v : TangentSpace (𝓡 3) x) :
    (G.flow.metric t).inner x u v =
      (-t) * (S.metric.inner x u v -
        mvfderiv (𝓡 3) r x u * mvfderiv (𝓡 3) r x v) +
          mvfderiv (𝓡 3) r x u * mvfderiv (𝓡 3) r x v := by
  have hdim := G.ricciNullity_eq_one_of_null_plane hC p a b ha hb hab hzero
  have hsec (s : ℝ) (hs : s < 0) :
      (G.flow.connection s).NonnegativeSectionalCurvature := by
    obtain ⟨E⟩ := G.self_similar s hs
    intro y c d
    exact (G.flow.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      y (E.nonnegativeCurvatureOperator (abs_pos.mpr hs.ne) S.connection
        (G.flow.connection s) S.nonnegative_curvature y) c d
  simpa only [G.at_minus_one] using
    inner_eq_transverse_scale_on_negative_times hC G.flow hsec
      (fun s hs y => (hdim s hs y).trans (hdim (-1) (by norm_num) y).symm)
      (G.scalarCurvature_eq_neg_inv_of_initial_scalar_one hscalar) hr hu hz t ht x u v




theorem ancientSourceFlow_connection_zero_eq_unscaled
    (G : ShrinkingSolitonFlow S) :
    G.ancientSourceFlow.connection 0 = G.unscaledSourceFlow.connection 0 := rfl

end PoincareConjecture.ShrinkingSolitonFlow
