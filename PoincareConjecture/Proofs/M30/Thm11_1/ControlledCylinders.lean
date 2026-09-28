import PoincareConjecture.Proofs.M30.Thm11_1.WorldlineControl
import PoincareConjecture.Proofs.M30.Generalized.Gluing
import PoincareConjecture.Proofs.M30.Thm5_33.CurvatureNorm

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem eventually_controlled_cylinders_of_scalar_worldlines
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (A : ℝ) (hA : 0 < A) {D tau : ℝ} (hD : 0 ≤ D) (htau : 0 < tau)
    (hworld : ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.baseBall k (A + 1),
      ∃ e : GeneralizedFlowCylinder (S.flow k) ((S.flow k).slice (S.base k).1)
        (S.base k).1 (S.scale k) (Icc (-tau) 0) ({x} : Set _),
        (∀ h₀, e.pointMap 0 h₀ x = (⟨(S.base k).1, x⟩ : (S.flow k).point)) ∧
          ∀ s (hs : s ∈ Icc (-tau) 0),
            (S.flow k).scalar (e.pointMap s hs x) ≤ D * S.scale k) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
      Nonempty (ControlledBlowupCylinder S k A tau (13 * max D 1) eta) := by
  classical
  have hA' : 0 < A + 1 := by linarith
  intro eta heta
  filter_upwards [hworld, H.balls_compact A hA,
    eventually_curvatureNorm_and_negativeDefect_le hC S H.branch D hD eta heta]
      with k hworldk hcompact hcurvature
  let C := (S.flow k).slice (S.base k).1
  let g : RiemannianMetric 3 C.carrier := (S.flow k).metric (S.base k).1
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) C.carrier
  have hsqrt : 0 < Real.sqrt (S.scale k) := Real.sqrt_pos.mpr (S.base_scalar_pos k)
  have hopen (R : ℝ) : IsOpen (S.baseBall k R) := by
    change IsOpen {x : C.carrier |
      edist (S.base k).2 x < ENNReal.ofReal (R / Real.sqrt (S.scale k))}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hbase (R : ℝ) (hR : 0 < R) : (S.base k).2 ∈ S.baseBall k R := by
    change edist (S.base k).2 (S.base k).2 < ENNReal.ofReal (R / Real.sqrt (S.scale k))
    rw [edist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hR hsqrt)
  let V : TopologicalSpace.Opens C.carrier := ⟨S.baseBall k (A + 1), hopen (A + 1)⟩
  have hbuffer : closure (S.baseBall k A) ⊆ V := by
    have hclosed : IsClosed {x : C.carrier |
        edist (S.base k).2 x ≤ ENNReal.ofReal (A / Real.sqrt (S.scale k))} :=
      isClosed_le (continuous_const.edist continuous_id) continuous_const
    have hsub : S.baseBall k A ⊆ {x : C.carrier |
        edist (S.base k).2 x ≤ ENNReal.ofReal (A / Real.sqrt (S.scale k))} := by
      intro x hx
      change edist (S.base k).2 x < ENNReal.ofReal (A / Real.sqrt (S.scale k)) at hx
      exact hx.le
    intro x hx
    exact (closure_minimal hsub hclosed hx).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (div_pos hA' hsqrt)).mpr
        (div_lt_div_of_pos_right (by linarith) hsqrt))
  choose ev hzero hscalar using hworldk
  let r : C.carrier → V := fun x =>
    if hx : x ∈ V then ⟨x, hx⟩ else ⟨(S.base k).2, hbase (A + 1) hA'⟩
  let p : C.carrier → C.carrier := fun x => (r x).1
  let e (x : C.carrier) : GeneralizedFlowCylinder (S.flow k) C
      (S.base k).1 (S.scale k) (Icc (-tau) 0) {p x} := ev (r x).1 (r x).2
  have hp (x : C.carrier) (hx : x ∈ V) : p x = x := by
    simp only [p, r, dif_pos hx]
  have hzero' (h₀ : (0 : ℝ) ∈ Icc (-tau) 0) (x : C.carrier) :
      (e x).pointMap 0 h₀ (p x) = (⟨(S.base k).1, p x⟩ : (S.flow k).point) :=
    hzero (r x).1 (r x).2 h₀
  have hs₀ : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
  have hregular (x : C.carrier) (hx : x ∈ V) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => (e z).forward 0 hs₀ (p z)) x ∧
        Function.Bijective
          (mfderiv (𝓡 3) (𝓡 3) (fun z => (e z).forward 0 hs₀ (p z)) x) := by
    apply regularAt_of_slice_identity (S.flow k) (by simp)
    filter_upwards [V.isOpen.mem_nhds hx] with z hz
    change (e z).pointMap 0 hs₀ (p z) = (⟨(S.base k).1, z⟩ : (S.flow k).point)
    rw [hzero', hp z hz]
  have hinitial : InjOn (fun z => (e z).forward 0 hs₀ (p z)) V := by
    intro x hx y hy hxy
    have hpoints := congrArg
      (fun z => (⟨(S.base k).1 + 0 / S.scale k, z⟩ : (S.flow k).point)) hxy
    change (e x).pointMap 0 hs₀ (p x) = (e y).pointMap 0 hs₀ (p y) at hpoints
    rw [hzero', hzero', hp x hx, hp y hy] at hpoints
    exact eq_of_heq (Sigma.mk.inj_iff.mp hpoints).2
  obtain ⟨E, hE⟩ := Cylinder.exists_of_singleton_family ordConnected_Icc isCompact_Icc
    V (hopen A) ⟨(S.base k).2, hbase A hA⟩ hcompact hbuffer p e hs₀ hregular hinitial
  have hscalarE (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : C.carrier) :
      (S.flow k).scalar (E.pointMap s hs x) ≤ D * S.scale k := by
    rw [hE]
    exact hscalar (r x).1 (r x).2 s hs
  have hbounds (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : C.carrier) :
      |(S.flow k).curvatureNorm (E.pointMap s hs x)| ≤
          (13 * max D 1) * S.scale k ∧
        ((S.flow k).connection (E.pointMap s hs x).1).negativeCurvaturePart
          (E.pointMap s hs x).2 ≤ eta * S.scale k := by
    exact hcurvature (E.pointMap s hs x).1
      (((S.flow k).slice_nonempty_iff _).mp ⟨(E.pointMap s hs x).2⟩)
      (E.pointMap s hs x).2 (hscalarE s hs x)
  refine ⟨{
    embedding := E
    zero_identity := ?_
    curvature_bound := fun s hs x _ => (hbounds s hs x).1
    negative_curvature_bound := fun s hs x _ => (hbounds s hs x).2 }⟩
  intro h₀ x hx
  rw [hE, hzero', hp x (hbuffer (subset_closure hx))]

theorem exists_radius_dependent_controlled_cylinders
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) (A : ℝ) (hA : 0 < A) :
    ∃ tau : ℝ, 0 < tau ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
        Nonempty (ControlledBlowupCylinder S k A tau B eta) := by
  obtain ⟨D, hD, tau, htau, hworld⟩ :=
    exists_uniform_scalar_controlled_worldlines hC H hbound (A + 1) (by linarith)
  refine ⟨tau, htau, 13 * max (2 * D) 1,
    mul_nonneg (by norm_num) (zero_le_one.trans (le_max_right _ _)), ?_⟩
  exact eventually_controlled_cylinders_of_scalar_worldlines hC H A hA
    (by linarith) htau hworld

theorem shortControlledBlowupHypotheses_of_terminal_scalar_bound
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    {D : ℝ} (hD : 4 ≤ D)
    (hterminal : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ S.baseBall k A,
        (S.flow k).scalar ⟨(S.base k).1, x⟩ ≤ D * S.scale k) :
    Nonempty (ShortControlledBlowupHypotheses S kappa r₀) := by
  obtain ⟨tau, htau, hworld⟩ :=
    exists_common_scalar_controlled_worldlines hC H hD hterminal
  refine ⟨{
    kappa_pos := H.kappa_pos
    radius_pos := H.radius_pos
    balls_compact := H.balls_compact
    backward_time := tau
    backward_time_pos := htau
    curvature_bound := 13 * max (2 * D) 1
    curvature_bound_nonneg :=
      mul_nonneg (by norm_num) (zero_le_one.trans (le_max_right _ _))
    cylinders := ?_
    noncollapsed_at_zero := H.noncollapsed_at_zero }⟩
  intro A hA
  exact eventually_controlled_cylinders_of_scalar_worldlines hC H A hA
    (by linarith) htau (hworld (A + 1) (by linarith))

end PoincareConjecture.M30
