import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.LocalRegularity

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g0 : RiemannianMetric n M} (D0 : LeviCivitaData g0) (g : RiemannianMetric n M)

private noncomputable def metricDefect (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  D0.connection.derivMetricTensor x

private theorem metricDefect_apply {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) x) :
    metricDefect D0 g x (Y x) (Z x) (X x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x (X x) -
        g.inner x (D0.connection Y x (X x)) (Z x) -
        g.inner x (Y x) (D0.connection Z x (X x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact D0.connection.derivMetricTensor_apply (X := X) x hY hZ

private theorem metricDefect_symm (x : M) (u v w : TangentSpace (𝓡 n) x) :
    metricDefect D0 g x u v w = metricDefect D0 g x v u w := by
  let U := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let V := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  have hU := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) u
  have hV := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have h1 := metricDefect_apply D0 g (X := W) hU hV
  have h2 := metricDefect_apply D0 g (X := W) hV hU
  simp only [W, FiberBundle.extend_apply_self] at h1 h2
  rw [h1, h2]
  have heq : (fun y => g.inner y (U y) (V y)) =
      fun y => g.inner y (V y) (U y) := funext fun y => g.symm y _ _
  change mvfderiv (𝓡 n) (fun y => g.inner y (U y) (V y)) x w -
      g.inner x (D0.connection U x w) v - g.inner x u (D0.connection V x w) =
    mvfderiv (𝓡 n) (fun y => g.inner y (V y) (U y)) x w -
      g.inner x (D0.connection V x w) u - g.inner x v (D0.connection U x w)
  rw [heq, g.symm x (D0.connection U x w) v, g.symm x u (D0.connection V x w)]
  ring

private noncomputable def metricCorrection (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := TangentSpace (𝓡 n) x
  letI : FiniteDimensional ℝ V := VectorBundle.finiteDimensional ℝ
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) x
  let Q := metricDefect D0 g x
  let P := (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).toContinuousLinearMap.comp Q
  let K := (2⁻¹ : ℝ) • (P + P.flip - Q.flip)
  (ContinuousLinearMap.compL ℝ V (V →L[ℝ] ℝ) V (g.inner x).inverse).comp K

private theorem inner_metricCorrection (x : M) (u v w : TangentSpace (𝓡 n) x) :
    g.inner x (metricCorrection D0 g x v u) w =
      (2⁻¹ : ℝ) * (metricDefect D0 g x v w u + metricDefect D0 g x u w v -
        metricDefect D0 g x u v w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := congrArg (fun L => L w) ((g.inner_isInvertible x).self_apply_inverse
    ((2⁻¹ : ℝ) • ((metricDefect D0 g x v).flip u +
      (metricDefect D0 g x u).flip v - metricDefect D0 g x u v)))
  convert! h using 1

private theorem metricCorrection_symm (x : M) (u v : TangentSpace (𝓡 n) x) :
    metricCorrection D0 g x u v = metricCorrection D0 g x v u := by
  apply (g.inner_isInvertible x).injective
  ext w
  rw [inner_metricCorrection, inner_metricCorrection, metricDefect_symm D0 g x v u w]
  ring

private theorem inner_metricCorrection_add (x : M) (u v w : TangentSpace (𝓡 n) x) :
    g.inner x (metricCorrection D0 g x v u) w +
      g.inner x v (metricCorrection D0 g x w u) = metricDefect D0 g x v w u := by
  rw [g.symm x v, inner_metricCorrection, inner_metricCorrection,
    metricDefect_symm D0 g x w v u]
  ring

private noncomputable def metricConnection :
    CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
  D0.connection.addOneForm (metricCorrection D0 g)

private theorem metricConnection_apply
    (Y : (x : M) → TangentSpace (𝓡 n) x) (x : M) (v : TangentSpace (𝓡 n) x) :
    metricConnection D0 g Y x v = D0.connection Y x v +
      metricCorrection D0 g x (Y x) v := rfl

private theorem metricConnection_torsion : (metricConnection D0 g).torsion = 0 := by
  apply (CovariantDerivative.torsion_eq_zero_iff _).mpr
  intro X Y x hX hY
  have h := D0.connection.torsion_eq_zero_iff.mp D0.torsion_eq_zero hX hY
  rw [metricConnection_apply, metricConnection_apply,
    metricCorrection_symm D0 g x (Y x) (X x)]
  simpa only [add_sub_add_right_eq_sub] using h

private theorem metricConnection_metricCompatible :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (metricConnection D0 g).IsMetricCompatible := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply (CovariantDerivative.isMetricCompatible_iff _).mpr
  intro x X Y Z hX hY hZ
  have h := metricDefect_apply D0 g (X := X) hY hZ
  have hc := inner_metricCorrection_add D0 g x (X x) (Y x) (Z x)
  change mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x (X x) =
    g.inner x (metricConnection D0 g Y x (X x)) (Z x) +
      g.inner x (Y x) (metricConnection D0 g Z x (X x))
  rw [metricConnection_apply, metricConnection_apply]
  simp only [map_add, add_apply]
  linarith

private theorem metricDefect_smooth
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => metricDefect D0 g y (Y y) (Z y) (X y)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := ((contMDiffAt_mvfderiv_apply (hY.inner_bundle hZ) hX).sub
    ((D0.contMDiffAt_covariantDerivativeOnFields hX hY).inner_bundle hZ)).sub
    (hY.inner_bundle (D0.contMDiffAt_covariantDerivativeOnFields hX hZ))
  apply hs.congr_of_eventuallyEq
  filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hY,
    eventually_mdifferentiableAt_of_contMDiffAt hZ] with y hy hz
  exact metricDefect_apply D0 g hy hz

private theorem inner_metricConnection_smooth
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (metricConnection D0 g Y y (X y)) (Z y)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs := ((metricDefect_smooth D0 g hX hY hZ).add
    (metricDefect_smooth D0 g hY hX hZ)).sub
      (metricDefect_smooth D0 g hZ hX hY)
  have hh := ((D0.contMDiffAt_covariantDerivativeOnFields hX hY).inner_bundle hZ).add
    ((ContinuousLinearMap.lsmul ℝ ℝ (2⁻¹ : ℝ)).contDiff.contMDiff.contMDiffAt.comp x hs)
  convert! hh using 1
  funext y
  rw [metricConnection_apply, map_add, add_apply, inner_metricCorrection]
  rfl

private theorem metricConnection_field_smooth
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (fun y => metricConnection D0 g Y y (X y))) x := by
  apply g.contMDiffAt_of_metricDual
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply
  intro v
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E y v) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hZ := (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞)
    (FiberBundle.mem_baseSet_trivializationAt E V x)).clm_bundle_apply hv
  have h := inner_metricConnection_smooth D0 g hX hY hZ
  change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
    (fun y => (ContinuousLinearMap.inCoordinates E V ℝ (fun _ : M => ℝ)
      x y x y (g.inner y (metricConnection D0 g Y y (X y)))) v) x
  have he : trivializationAt ℝ (fun _ : M => ℝ) x = Bundle.Trivial.trivialization M ℝ := rfl
  simpa only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    he, Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_apply] using h

private theorem metricConnection_smooth :
    CovariantDerivative.ContMDiffCovariantDerivative (metricConnection D0 g) ∞ := by
  constructor
  constructor
  intro Y hY
  apply contMDiffOn_univ.mpr
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_apply
  intro v
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E y v) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩
  have hX := (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞)
    (FiberBundle.mem_baseSet_trivializationAt E V x)).clm_bundle_apply hv
  have hfield := metricConnection_field_smooth D0 g hX ((contMDiffOn_univ.mp hY) x)
  have hc := (contMDiffAt_totalSpace.mp hfield).2
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E V x)]
    with y hy
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy]

noncomputable def withMetric : LeviCivitaData g where
  connection := metricConnection D0 g
  smooth := metricConnection_smooth D0 g
  torsion_eq_zero := metricConnection_torsion D0 g
  metricCompatible := metricConnection_metricCompatible D0 g

end PoincareConjecture.LeviCivitaData
