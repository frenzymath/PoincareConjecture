import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.Connection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Frames.ODE

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle NNReal

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem shiChartMetric_at_source
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {y : M} (hy : y ∈ c.source) (v w : E) :
    shiChartMetric g c (c y) v w =
      g.inner y (shiChartField c v y) (shiChartField c w y) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have he := c.left_inv hy
  change g.inner (c.symm (c y))
    (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm (c y) v)
    (mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm (c y) w) = _
  rw [← shiChartField_at_inverse hc hi (c.map_source hy) v,
    ← shiChartField_at_inverse hc hi (c.map_source hy) w]
  exact congrArg (fun z => g.inner z (shiChartField c v z) (shiChartField c w z)) he

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_shiChart_parallel_frame [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {a b : ℝ} (hab : a < b) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hinside : MapsTo γ (Icc a b) c.source) (K : ℝ≥0)
    (hK : ∀ t ∈ Icc a b,
      ‖shiChartChristoffel D c (c (γ t)) (deriv (c ∘ γ) t)‖ ≤ (K : ℝ))
    (hshort : b - a ≤ 1 / (2 * (K : ℝ) + 1)) (Pb : E →L[ℝ] E) :
    ∃ P : ℝ → E →L[ℝ] E,
      ContDiffOn ℝ 1 P (Icc a b) ∧ P b = Pb ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt P
        (-((shiChartChristoffel D c (c (γ t)) (deriv (c ∘ γ) t)).comp (P t)))
        (Icc a b) t) ∧
      ∀ t ∈ Icc a b, ∀ v w,
        shiChartMetric g c (c (γ t)) (P t v) (P t w) =
          shiChartMetric g c (c (γ b)) (Pb v) (Pb w) := by
  let U : Set ℝ := γ ⁻¹' c.source
  let x : ℝ → E := c ∘ γ
  let A : ℝ → E →L[ℝ] E := fun t => shiChartChristoffel D c (x t) (deriv x t)
  let G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun t => shiChartMetric g c (x t)
  let G' : ℝ → E →L[ℝ] E →L[ℝ] ℝ :=
    fun t => fderiv ℝ (shiChartMetric g c) (x t) (deriv x t)
  have hU : IsOpen U := c.open_source.preimage hγ.continuous
  have hI : Icc a b ⊆ U := hinside
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hx : ContDiffOn ℝ 1 x U :=
    ((hc.of_le h1).comp hγ.contMDiffOn (fun _ ht => ht)).contDiffOn
  have hxt : MapsTo x U c.target := fun t ht => c.map_source ht
  have hA : ContinuousOn A (Icc a b) := by
    exact (((shiChartChristoffel_smooth D hc hi).continuousOn.comp
      hx.continuousOn hxt).clm_apply
        (hx.continuousOn_deriv_of_isOpen hU le_rfl)).mono hI
  let tb : Icc a b := ⟨b, hab.le, le_rfl⟩
  obtain ⟨P, hP, hPb, hPd⟩ := exists_contDiffOn_frame_ode hab tb A hA K hK hshort Pb
  have hG : ∀ t ∈ Icc a b, HasDerivWithinAt G (G' t) (Icc a b) t := by
    intro t ht
    have hxd := ((hx.contDiffAt (hU.mem_nhds (hI ht))).differentiableAt
      (by norm_num)).hasDerivAt
    have hGd := ((shiChartMetric_smooth g hc hi).contDiffAt
      (c.open_target.mem_nhds (hxt (hI ht)))).differentiableAt (by simp)
    have hdG : HasFDerivAt (shiChartMetric g c)
        (fderiv ℝ (shiChartMetric g c) (x t)) (x t) := hGd.hasFDerivAt
    have hd := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
      («E» := E →L[ℝ] E →L[ℝ] ℝ) (F := E)
      (l := shiChartMetric g c) (l' := fderiv ℝ (shiChartMetric g c) (x t))
      (f := x) (f' := deriv x t) t hdG hxd
    simpa only [G, G', Function.comp_apply] using! hd.hasDerivWithinAt
  have hcompat : ∀ t ∈ Icc a b, ∀ v w,
      G' t v w = G t (A t v) w + G t v (A t w) := by
    intro t ht v w
    exact shiChartMetric_derivative D hc hi (hxt (hI ht)) v (deriv x t) w
  refine ⟨P, hP, hPb, hPd, ?_⟩
  intro t ht v w
  simpa only [G, x, Function.comp_apply, tb, hPb] using!
    frame_ode_pairing_eq hab tb A P G G' hPd hG hcompat t ht v w

set_option backward.isDefEq.respectTransparency false in
theorem exists_shiChart_native_parallel_frame [T2Space M]
    (D : LeviCivitaData g) {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {a b : ℝ} (hab : a < b) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hinside : MapsTo γ (Icc a b) c.source) (K : ℝ≥0)
    (hK : ∀ t ∈ Icc a b,
      ‖shiChartChristoffel D c (c (γ t)) (deriv (c ∘ γ) t)‖ ≤ (K : ℝ))
    (hshort : b - a ≤ 1 / (2 * (K : ℝ) + 1))
    (J : E →L[ℝ] TangentSpace (𝓡 n) (γ b)) :
    ∃ P : ℝ → E →L[ℝ] E,
      ContDiffOn ℝ 1 P (Icc a b) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt P
        (-((shiChartChristoffel D c (c (γ t)) (deriv (c ∘ γ) t)).comp (P t)))
        (Icc a b) t) ∧
      (∀ v, shiChartField c (P b v) (γ b) = J v) ∧
      ∀ t ∈ Icc a b, ∀ v w,
        g.inner (γ t) (shiChartField c (P t v) (γ t))
            (shiChartField c (P t w) (γ t)) = g.inner (γ b) (J v) (J w) := by
  let Pb : E →L[ℝ] E := (mvfderiv (𝓡 n) c (γ b)).comp J
  obtain ⟨P, hP, hPb, hPd, hpair⟩ :=
    exists_shiChart_parallel_frame D hc hi hab hγ hinside K hK hshort Pb
  have hb : γ b ∈ c.source := hinside ⟨hab.le, le_rfl⟩
  have hend (v : E) : shiChartField c (P b v) (γ b) = J v := by
    rw [hPb]
    exact (shiChart_mfderiv_isInvertible hc hi hb).inverse_apply_self (J v)
  refine ⟨P, hP, hPd, hend, ?_⟩
  intro t ht v w
  have he := hpair t ht v w
  rw [shiChartMetric_at_source hc hi (hinside ht),
    shiChartMetric_at_source hc hi hb] at he
  rw [← hPb, hend, hend] at he
  exact he

end PoincareConjecture.RicciFlowAnalysis
