import PoincareConjecture.Statements.Ch06.ReducedLength

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in

theorem mvfderiv_eq_of_eventuallyEq {f g : M → ℝ} {q : M}
    (h : f =ᶠ[𝓝 q] g) : mvfderiv (𝓡 n) f q = mvfderiv (𝓡 n) g q := by
  unfold mvfderiv
  rw [h.eq_of_nhds, h.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))]

theorem hessianOnFields_eq_of_eventuallyEq {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {f h : M → ℝ} {q : M}
    (heq : f =ᶠ[𝓝 q] h)
    (X Y : (x : M) → TangentSpace (𝓡 n) x) :
    D.hessianOnFields f X Y q = D.hessianOnFields h X Y q := by
  have hfield : (fun x ↦ mvfderiv (𝓡 n) f x (Y x)) =ᶠ[𝓝 q]
      (fun x ↦ mvfderiv (𝓡 n) h x (Y x)) := by
    filter_upwards [heq.eventuallyEq_nhds] with x hx
    rw [mvfderiv_eq_of_eventuallyEq hx]
  unfold LeviCivitaData.hessianOnFields
  rw [mvfderiv_eq_of_eventuallyEq hfield, mvfderiv_eq_of_eventuallyEq heq]

theorem hessian_eq_of_eventuallyEq {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {f h : M → ℝ} {q : M}
    (heq : f =ᶠ[𝓝 q] h) (v w : TangentSpace (𝓡 n) q) :
    D.hessian f q v w = D.hessian h q v w :=
  hessianOnFields_eq_of_eventuallyEq D heq _ _

theorem laplacian_eq_of_eventuallyEq {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {f h : M → ℝ} {q : M}
    (heq : f =ᶠ[𝓝 q] h) : D.laplacian f q = D.laplacian h q := by
  unfold LeviCivitaData.laplacian
  exact Finset.sum_congr rfl fun _ _ ↦ hessian_eq_of_eventuallyEq D heq _ _

variable {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p q : M} {τ : ℝ}

theorem regular_representative_eventuallyEq
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    r.representative =ᶠ[𝓝 (q, τ)]
      (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2) :=
  Filter.eventuallyEq_of_mem (r.neighborhood_open.mem_nhds r.center_mem)
    r.representative_eq

theorem regular_time_eventuallyEq
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    (fun s ↦ r.representative (q, s)) =ᶠ[𝓝 τ]
      (fun s ↦ reducedLength F T p q s) :=
  (regular_representative_eventuallyEq r).comp_tendsto
    (continuous_const.prodMk continuous_id).continuousAt

theorem regular_space_eventuallyEq
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    (fun x ↦ r.representative (x, τ)) =ᶠ[𝓝 q]
      (fun x ↦ reducedLength F T p x τ) :=
  (regular_representative_eventuallyEq r).comp_tendsto
    (continuous_id.prodMk continuous_const).continuousAt

theorem reducedLength_contMDiffAt
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2) (q, τ) :=
  r.representative_spacetime_smooth.congr_of_eventuallyEq
    (regular_representative_eventuallyEq r).symm

theorem reducedLength_space_contMDiffAt
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun x ↦ reducedLength F T p x τ) q :=
  r.representative_space_smooth.congr_of_eventuallyEq
    (regular_space_eventuallyEq r).symm

theorem reducedLength_hasDerivAt
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    HasDerivAt (fun s ↦ reducedLength F T p q s)
      (deriv (fun s ↦ reducedLength F T p q s) τ) τ := by
  obtain ⟨d, hd⟩ := r.representative_time_derivative
  have h := hd.congr_of_eventuallyEq (regular_time_eventuallyEq r).symm
  exact h.differentiableAt.hasDerivAt

theorem regular_gradientNormSq_eq
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    reducedLengthGradientNormSq F T r.representative τ q =
      reducedLengthGradientNormSq F T
        (fun z ↦ reducedLength F T p z.1 z.2) τ q := by
  unfold reducedLengthGradientNormSq
  rw [mvfderiv_eq_of_eventuallyEq (regular_space_eventuallyEq r)]

theorem regular_laplacian_eq
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    reducedLengthLaplacian F T r.representative τ q =
      reducedLengthLaplacian F T
        (fun z ↦ reducedLength F T p z.1 z.2) τ q :=
  laplacian_eq_of_eventuallyEq _ (regular_space_eventuallyEq r)

theorem reducedLength_regular_inequalities [ConnectedSpace M]
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (r : ReducedLengthRegularPoint F T τmax p q τ) :
    0 ≤ deriv (fun s ↦ reducedLength F T p q s) τ -
        reducedLengthLaplacian F T (fun z ↦ reducedLength F T p z.1 z.2) τ q +
        reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2) τ q -
        (F.connection (T - τ)).scalarCurvature q + (n : ℝ) / (2 * τ) ∧
      2 * reducedLengthLaplacian F T (fun z ↦ reducedLength F T p z.1 z.2) τ q -
        reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2) τ q +
        (F.connection (T - τ)).scalarCurvature q +
        (reducedLength F T p q τ - (n : ℝ)) / τ ≤ 0 := by
  have h := (hDifferential.regular_point_formulas p q τ r).2.2.2.2
  rw [(regular_time_eventuallyEq r).deriv_eq, regular_laplacian_eq r,
    regular_gradientNormSq_eq r, r.representative_eq (q, τ) r.center_mem] at h
  exact h

end PoincareConjecture.M10
