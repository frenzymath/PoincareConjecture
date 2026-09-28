import PoincareConjecture.Proofs.M03.Existence.ConjugatorLieDerivativeNative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

noncomputable section

universe u

namespace PoincareConjecture.ConjugatorLieDerivativeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def chartConstantField (p : M) (v : E) : (y : M) → TangentSpace (𝓡 n) y :=
  VectorField.mpullback (𝓡 n) 𝓘(ℝ, E) (chartAt E p) (fun _ => v)

def chartVector (p : M) (W : (y : M) → TangentSpace (𝓡 n) y) : E → E :=
  VectorField.mpullback 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm W

def chartMetricForm (g : RiemannianMetric n M) (p : M) (z : E) :
    E →L[ℝ] E →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z
  exact (((ContinuousLinearMap.precompL (𝕜 := ℝ) E
    (g.inner ((chartAt E p).symm z))) A).comp A).flip

theorem chartMetricForm_apply (g : RiemannianMetric n M) (p : M) (z u v : E) :
    chartMetricForm g p z u v =
      g.inner ((chartAt E p).symm z)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z u)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z v) := rfl

private theorem chartDifferential_isInvertible (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x).IsInvertible :=
  ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hx, rfl⟩

private theorem chartInverseDifferential_isInvertible (p : M) {z : E}
    (hz : z ∈ (chartAt E p).target) :
    (mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z).IsInvertible :=
  ⟨(mdifferentiable_chart (I := 𝓡 n) p).symm.mfderiv hz, rfl⟩

theorem chartConstantField_apply (p : M) (v : E) {x : M}
    (hx : x ∈ (chartAt E p).source) :
    chartConstantField p v x =
      mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm (chartAt E p x) v := by
  let A := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv hx
  change A.toContinuousLinearMap.inverse v = _
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

theorem chartConstantField_inverse (p : M) (v : E) {z : E}
    (hz : z ∈ (chartAt E p).target) :
    chartConstantField p v ((chartAt E p).symm z) =
      mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z v := by
  rw [chartConstantField_apply p v ((chartAt E p).map_target hz),
    (chartAt E p).right_inv hz]

theorem chartVector_chartConstantField (p : M) (v : E) {z : E}
    (hz : z ∈ (chartAt E p).target) :
    chartVector p (chartConstantField p v) z = v := by
  change (mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z).inverse
    (chartConstantField p v ((chartAt E p).symm z)) = v
  rw [chartConstantField_inverse p v hz]
  exact (chartInverseDifferential_isInvertible p hz).inverse_apply_self v

theorem chartInverseDifferential_chartVector (p : M)
    (W : (y : M) → TangentSpace (𝓡 n) y) {z : E}
    (hz : z ∈ (chartAt E p).target) :
    mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z (chartVector p W z) =
      W ((chartAt E p).symm z) :=
  (chartInverseDifferential_isInvertible p hz).self_apply_inverse _

theorem chartVector_apply (p : M)
    (W : (y : M) → TangentSpace (𝓡 n) y) {z : E}
    (hz : z ∈ (chartAt E p).target) :
    chartVector p W z =
      mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) ((chartAt E p).symm z)
        (W ((chartAt E p).symm z)) := by
  let A := (mdifferentiable_chart (I := 𝓡 n) p).symm.mfderiv hz
  change A.toContinuousLinearMap.inverse
    (W ((chartAt E p).symm z)) = _
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

theorem chartVector_chart (p : M)
    (W : (y : M) → TangentSpace (𝓡 n) y) {y : M}
    (hy : y ∈ (chartAt E p).source) :
    chartVector p W (chartAt E p y) =
      mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) y (W y) := by
  rw [chartVector_apply p W ((chartAt E p).map_source hy),
    (chartAt E p).left_inv hy]

theorem chartConstantField_contMDiffOn (p : M) (v : E) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% (chartConstantField p v)) (chartAt E p).source := by
  have hc : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun y : E => (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  intro x hx
  have hchart : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ (chartAt E p) x :=
    (contMDiffOn_chart (I := 𝓡 n) (x := p) x hx).contMDiffAt
      ((chartAt E p).open_source.mem_nhds hx)
  exact ((hc _).mpullback_vectorField_preimage
    hchart
    (chartDifferential_isInvertible p hx) (by simp)).contMDiffWithinAt

theorem chartVector_contDiffAt (p : M)
    {W : (y : M) → TangentSpace (𝓡 n) y} {z : E}
    (hz : z ∈ (chartAt E p).target)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% W) ((chartAt E p).symm z)) :
    ContDiffAt ℝ ∞ (chartVector p W) z := by
  have hi : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ (chartAt E p).symm z :=
    (contMDiffOn_chart_symm (I := 𝓡 n) (x := p) z hz).contMDiffAt
      ((chartAt E p).open_target.mem_nhds hz)
  exact contMDiffAt_vectorSpace_iff_contDiffAt.mp
    (hW.mpullback_vectorField_preimage hi
      (chartInverseDifferential_isInvertible p hz) (by simp))

theorem chartMetricForm_contDiffOn (g : RiemannianMetric n M) (p : M) :
    ContDiffOn ℝ ∞ (chartMetricForm g p) (chartAt E p).target := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (chartAt E p).symm
      (chartAt E p).target := contMDiffOn_chart_symm (I := 𝓡 n) (x := p)
  have htan := hi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt E p).open_target.uniqueMDiffOn
  have hpush (u : E) : ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun z : E => (⟨(chartAt E p).symm z,
        mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z u⟩ :
          TangentBundle (𝓡 n) M)) (chartAt E p).target := by
    have hc : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun z : E => (⟨z, u⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    have h := htan.comp hc.contMDiffOn (fun z hz => hz)
    change ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun z : E => (⟨(chartAt E p).symm z,
        mfderivWithin 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm (chartAt E p).target z u⟩ :
          TangentBundle (𝓡 n) M)) (chartAt E p).target at h
    apply h.congr
    intro z hz
    rw [mfderivWithin_of_isOpen (chartAt E p).open_target hz]
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  exact ((hpush u).inner_bundle (hpush v)).contDiffOn

theorem chartVector_bracket_chartConstantField (p : M)
    {W : (y : M) → TangentSpace (𝓡 n) y} {z : E}
    (hz : z ∈ (chartAt E p).target)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% W) ((chartAt E p).symm z)) (u : E) :
    chartVector p (VectorField.mlieBracket (𝓡 n) W (chartConstantField p u)) z =
      -fderiv ℝ (chartVector p W) z u := by
  have hi : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ (chartAt E p).symm z :=
    (contMDiffOn_chart_symm (I := 𝓡 n) (x := p) z hz).contMDiffAt
      ((chartAt E p).open_target.mem_nhds hz)
  have hX := (chartConstantField_contMDiffOn p u).contMDiffAt
    ((chartAt E p).open_source.mem_nhds ((chartAt E p).map_target hz))
  have hmin : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) hmin
  have hnat := VectorField.mpullback_mlieBracket
    (hW.mdifferentiableAt (by simp)) (hX.mdifferentiableAt (by simp)) hi hmin
  have hc : chartVector p (chartConstantField p u) =ᶠ[𝓝 z] (fun _ => u) := by
    filter_upwards [(chartAt E p).open_target.mem_nhds hz] with w hw
    exact chartVector_chartConstantField p u hw
  have hchange :
      VectorField.mlieBracket 𝓘(ℝ, E) (chartVector p W)
        (chartVector p (chartConstantField p u)) z =
      VectorField.mlieBracket 𝓘(ℝ, E) (chartVector p W) (fun _ => u) z := by
    simp only [← VectorField.mlieBracketWithin_univ]
    exact (Filter.EventuallyEq.refl (𝓝 z) (chartVector p W)).mlieBracketWithin_vectorField_eq_nhds hc
  change chartVector p (VectorField.mlieBracket (𝓡 n) W (chartConstantField p u)) z =
    VectorField.mlieBracket 𝓘(ℝ, E) (chartVector p W)
      (chartVector p (chartConstantField p u)) z at hnat
  rw [hnat, hchange, ← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin]
  simp [VectorField.lieBracketWithin]

theorem coordinateLieMetric_chart_eq
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (p : M)
    {W : (y : M) → TangentSpace (𝓡 n) y} {z : E}
    (hz : z ∈ (chartAt E p).target)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% W) ((chartAt E p).symm z)) (u v : E) :
    coordinateLieMetric (chartMetricForm g p) (chartVector p W) z u v =
      DeTurckNative.metricLieDerivative D W ((chartAt E p).symm z)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z u)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z v) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hX (a : E) := (chartConstantField_contMDiffOn p a).contMDiffAt
    ((chartAt E p).open_source.mem_nhds ((chartAt E p).map_target hz))
  have hpair : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (chartConstantField p u y) (chartConstantField p v y))
      ((chartAt E p).symm z) := (hX u).inner_bundle (hX v)
  have hi := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt_symm hz
  have hG : DifferentiableAt ℝ (chartMetricForm g p) z :=
    ((chartMetricForm_contDiffOn g p).contDiffAt
      ((chartAt E p).open_target.mem_nhds hz)).differentiableAt (by simp)
  have heval := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const u z)).clm_apply
    (hasFDerivAt_const v z)
  have heval_apply :
      fderiv ℝ (fun w => chartMetricForm g p w u v) z (chartVector p W z) =
        fderiv ℝ (chartMetricForm g p) z (chartVector p W z) u v := by
    simpa using congrArg (fun L : E →L[ℝ] ℝ => L (chartVector p W z)) heval.fderiv
  have hscalar :
      (fun w => g.inner ((chartAt E p).symm w)
        (chartConstantField p u ((chartAt E p).symm w))
        (chartConstantField p v ((chartAt E p).symm w))) =ᶠ[𝓝 z]
      (fun w => chartMetricForm g p w u v) := by
    filter_upwards [(chartAt E p).open_target.mem_nhds hz] with w hw
    rw [chartConstantField_inverse p u hw, chartConstantField_inverse p v hw]
    rfl
  have hbase :
      mvfderiv (𝓡 n)
        (fun y => g.inner y (chartConstantField p u y) (chartConstantField p v y))
        ((chartAt E p).symm z) (W ((chartAt E p).symm z)) =
      fderiv ℝ (chartMetricForm g p) z (chartVector p W z) u v := by
    have hchain := mvfderiv_comp_apply_of_eq z
      (hpair.mdifferentiableAt (by simp)) hi rfl (chartVector p W z)
    rw [chartInverseDifferential_chartVector p W hz] at hchain
    calc
      _ = mvfderiv 𝓘(ℝ, E)
          ((fun y => g.inner y (chartConstantField p u y) (chartConstantField p v y)) ∘
            (chartAt E p).symm) z (chartVector p W z) := hchain.symm
      _ = fderiv ℝ
          ((fun y => g.inner y (chartConstantField p u y) (chartConstantField p v y)) ∘
            (chartAt E p).symm) z (chartVector p W z) := by
        simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] <;> rfl
      _ = fderiv ℝ (fun w => chartMetricForm g p w u v) z (chartVector p W z) :=
        congrArg (fun L : E →L[ℝ] ℝ => L (chartVector p W z)) hscalar.fderiv_eq
      _ = _ := heval_apply
  have hbracket (a : E) :
      VectorField.mlieBracket (𝓡 n) W (chartConstantField p a)
          ((chartAt E p).symm z) =
        -mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z
          (fderiv ℝ (chartVector p W) z a) := by
    calc
      _ = mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm z
          (chartVector p (VectorField.mlieBracket (𝓡 n) W
            (chartConstantField p a)) z) :=
        (chartInverseDifferential_chartVector p _ hz).symm
      _ = _ := by
        rw [chartVector_bracket_chartConstantField p hz hW a, map_neg]
  have hlie := DeTurckNative.metricLieDerivative_on_fields D W
    (chartConstantField p u) (chartConstantField p v)
    (hW.mdifferentiableAt (by simp)) ((hX u).mdifferentiableAt (by simp))
    ((hX v).mdifferentiableAt (by simp))
  rw [hbase, hbracket u, hbracket v,
    chartConstantField_inverse p u hz, chartConstantField_inverse p v hz] at hlie
  simpa only [coordinateLieMetric, chartMetricForm_apply, map_neg, neg_apply,
    sub_neg_eq_add] using hlie.symm

end PoincareConjecture.ConjugatorLieDerivativeNative

end
