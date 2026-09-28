import PoincareConjecture.Proofs.M32.Claim11_32.Extension.TerminalPinching
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

private theorem scalarDifferential_pullback
    {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 n) ∞ Y]
    {g : RiemannianMetric n X} {g' : RiemannianMetric n Y}
    (D : LeviCivitaData g) (D' : LeviCivitaData g')
    (f : X → Y) (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hscalar : ∀ x, D'.scalarCurvature (f x) = D.scalarCurvature x)
    (x : X) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) D'.scalarCurvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) =
      mvfderiv (𝓡 n) D.scalarCurvature x v := by
  have heq : D'.scalarCurvature ∘ f = D.scalarCurvature := funext hscalar
  have h := mvfderiv_comp_apply x
    (D'.contMDiff_scalarCurvature.mdifferentiable (by simp) (f x))
    (hf.mdifferentiable (by simp) x) v
  rw [heq] at h
  exact h.symm

private theorem unit_bound_to_tangent_bound
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (𝓡 n) ∞ X]
    (g : RiemannianMetric n X) (f : X → ℝ) (x : X) (B : ℝ)
    (hunit : ∀ v : TangentSpace (𝓡 n) x, g.inner x v v = 1 →
      |mvfderiv (𝓡 n) f x v| ≤ B)
    (v : TangentSpace (𝓡 n) x) :
    |mvfderiv (𝓡 n) f x v| ≤ B * Real.sqrt (g.inner x v v) := by
  by_cases hv : v = 0
  · subst v
    simp [mvfderiv]
  have hpos : 0 < g.inner x v v := g.pos x v hv
  have hs : 0 < Real.sqrt (g.inner x v v) := Real.sqrt_pos.mpr hpos
  have hn : g.inner x ((Real.sqrt (g.inner x v v))⁻¹ • v)
      ((Real.sqrt (g.inner x v v))⁻¹ • v) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
    nlinarith [Real.sq_sqrt hpos.le]
  have h := hunit ((Real.sqrt (g.inner x v v))⁻¹ • v) hn
  simp only [mvfderiv, map_smul, smul_eq_mul, abs_mul,
    abs_inv, abs_of_pos hs] at h
  simpa only [mvfderiv, mul_comm] using (inv_mul_le_iff₀ hs).mp h

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

theorem extension_scalar_gradient_bound
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (t : ℝ) (ht : t ∈ F.interval) (x : (E.extended.slice t).carrier)
    (hx : H.r₀⁻¹ ^ 2 ≤ (E.extended.connection t).scalarCurvature x)
    (v : TangentSpace (𝓡 3) x) (hv : (E.extended.metric t).inner x v v = 1) :
    |mvfderiv (𝓡 3) (E.extended.connection t).scalarCurvature x v| ≤
      H.analytic_constant * (E.extended.connection t).scalarCurvature x ^ (3 / 2 : ℝ) := by
  obtain ⟨y, rfl⟩ := (E.right_inverse t ht).surjective x
  obtain ⟨w, rfl⟩ := ((F.metric t).mfderiv_bijective_of_pullback_eq
    (E.extended.metric t) y (E.metric_pullback t ht y)).2 v
  rw [scalarDifferential_pullback (F.connection t) (E.extended.connection t)
    (E.forward t ht) (E.forward_smooth t ht) (E.scalar_pullback t ht)]
  rw [E.scalar_pullback] at hx ⊢
  rw [E.metric_pullback] at hv
  exact H.scalar_gradient_bound t ht y hx w hv

theorem extension_box_scalar_gradient_bound
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (t : ℝ) (ht : t ∈ F.interval)
    (hb : t ∈ (E.extended.box b).interval)
    (x : (E.extended.box b).carrier.carrier)
    (hx : H.r₀⁻¹ ^ 2 ≤ ((E.extended.box b).flow.connection t).scalarCurvature x)
    (v : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) ((E.extended.box b).flow.connection t).scalarCurvature x v| ≤
      H.analytic_constant * ((E.extended.box b).flow.connection t).scalarCurvature x ^
        (3 / 2 : ℝ) * Real.sqrt (((E.extended.box b).flow.metric t).inner x v v) := by
  apply unit_bound_to_tangent_bound
  intro w hw
  have h := extension_scalar_gradient_bound H E t ht
    ((E.extended.box b).forward t hb x)
    (by simpa only [box_scalar_pullback] using hx)
    (mfderiv (𝓡 3) (𝓡 3) ((E.extended.box b).forward t hb) x w)
    (by rwa [(E.extended.box b).metric_pullback])
  rwa [box_scalar_pullback,
    scalarDifferential_pullback ((E.extended.box b).flow.connection t)
      (E.extended.connection t) ((E.extended.box b).forward t hb)
      ((E.extended.box b).forward_smooth t hb) (box_scalar_pullback E.extended b t hb)] at h

theorem terminal_box_scalar_gradient_bound
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (hT : T ∈ (E.extended.box b).interval)
    (x : (E.extended.box b).carrier.carrier)
    (hx : H.r₀⁻¹ ^ 2 < ((E.extended.box b).flow.connection T).scalarCurvature x)
    (v : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) ((E.extended.box b).flow.connection T).scalarCurvature x v| ≤
      H.analytic_constant * ((E.extended.box b).flow.connection T).scalarCurvature x ^
        (3 / 2 : ℝ) * Real.sqrt (((E.extended.box b).flow.metric T).inner x v v) := by
  have hevent := terminal_box_eventually H E b hT
  have hfilter : 𝓝[<] T ≤ 𝓝[(E.extended.box b).interval] T :=
    nhdsWithin_le_iff.mpr (hevent.mono fun _ ht => ht.2)
  have hscalar := (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time
    hM04 _ (E.extended.box b).flow x T hT).tendsto.mono_left hfilter
  have hdifferential :=
    (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_mvfderiv_continuousOn_time
      hM04 _ (E.extended.box b).flow x v T hT).tendsto.mono_left hfilter
  have hmetric := (Poincare.Geometry.RicciFlow.Harnack.metric_inner_contDiffOn_time
    (E.extended.box b).flow x v v).continuousOn T hT
  have hupper := (hscalar.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ 3 / 2))).const_mul
    H.analytic_constant
  apply le_of_tendsto_of_tendsto hdifferential.abs
    (hupper.mul (hmetric.tendsto.mono_left hfilter).sqrt)
  filter_upwards [hevent, hscalar.eventually (Ioi_mem_nhds hx)] with t ht htx
  exact extension_box_scalar_gradient_bound H E b t ht.1 ht.2 x htx.le v

theorem terminal_scalar_gradient_bound
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (x : (E.extended.slice T).carrier)
    (hx : H.r₀⁻¹ ^ 2 < (E.extended.connection T).scalarCurvature x)
    (v : TangentSpace (𝓡 3) x) (hv : (E.extended.metric T).inner x v v = 1) :
    |mvfderiv (𝓡 3) (E.extended.connection T).scalarCurvature x v| ≤
      H.analytic_constant * (E.extended.connection T).scalarCurvature x ^ (3 / 2 : ℝ) := by
  obtain ⟨b, hT, y, rfl⟩ := E.extended.box_covers T x
  obtain ⟨w, rfl⟩ := (((E.extended.box b).flow.metric T).mfderiv_bijective_of_pullback_eq
    (E.extended.metric T) y ((E.extended.box b).metric_pullback T hT y)).2 v
  rw [scalarDifferential_pullback ((E.extended.box b).flow.connection T)
    (E.extended.connection T) ((E.extended.box b).forward T hT)
    ((E.extended.box b).forward_smooth T hT) (box_scalar_pullback E.extended b T hT)]
  rw [box_scalar_pullback] at hx ⊢
  rw [(E.extended.box b).metric_pullback] at hv
  have h := terminal_box_scalar_gradient_bound hM04 H E b hT y hx w
  simpa only [hv, Real.sqrt_one, mul_one] using h

theorem extension_scalar_gradient_bound_of_strict
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (t : ℝ) (ht : t ∈ E.extended.interval) (x : (E.extended.slice t).carrier)
    (hx : H.r₀⁻¹ ^ 2 < (E.extended.connection t).scalarCurvature x)
    (v : TangentSpace (𝓡 3) x) (hv : (E.extended.metric t).inner x v v = 1) :
    |mvfderiv (𝓡 3) (E.extended.connection t).scalarCurvature x v| ≤
      H.analytic_constant * (E.extended.connection t).scalarCurvature x ^ (3 / 2 : ℝ) := by
  rcases E.times_subset ht with htold | htT
  · exact extension_scalar_gradient_bound H E t htold x hx.le v hv
  · have htT' : t = T := mem_singleton_iff.mp htT
    subst t
    exact terminal_scalar_gradient_bound hM04 H E x hx v hv

end PoincareConjecture.M32
