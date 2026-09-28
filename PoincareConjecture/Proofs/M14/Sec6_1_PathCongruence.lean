import PoincareConjecture.Proofs.M14.Sec6_1_LLength

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

private theorem horizontal_transport_val {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) :
    (show SpacetimeModelVector n from (h ▸ v : G.Horizontal r).val) = v.val := by
  cases h
  rfl

private theorem inner_transport_forward {q r : G.Point} (h : q = r)
    (v w : G.Horizontal q) :
    G.spacetime.horizontalMetric.inner r (h ▸ v) (h ▸ w) =
      G.spacetime.horizontalMetric.inner q v w := by
  cases h
  rfl

theorem horizontal_velocity_val (p : M14BackwardPath G T τ₁ τ₂ x y)
    {t : ℝ} (ht : t ∈ Set.Ioo τ₁ τ₂) :
    (p.horizontal_velocity t).val =
      mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve t (1 : ℝ) +
        G.spacetime.timeVector (p.curve t) := by
  rw [p.derivative_eq t ht]
  simp [add_comm]

theorem backwardLIntegrand_eqOn_of_curve_eqOn
    (p q : M14BackwardPath G T τ₁ τ₂ x y)
    (h : Set.EqOn p.curve q.curve (Set.Ioo τ₁ τ₂)) :
    Set.EqOn (M14BackwardLIntegrand G p) (M14BackwardLIntegrand G q)
      (Set.Ioo τ₁ τ₂) := by
  intro t ht
  have hpoint := h ht
  have hnear : p.curve =ᶠ[𝓝 t] q.curve :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) h
  have hd := hnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
  have hv : (show SpacetimeModelVector n from (p.horizontal_velocity t).val) =
      (q.horizontal_velocity t).val := by
    rw [horizontal_velocity_val p ht, horizontal_velocity_val q ht, hd]
    rw [hpoint]
  have hvelocity : hpoint ▸ p.horizontal_velocity t = q.horizontal_velocity t := by
    apply Subtype.ext
    exact (horizontal_transport_val hpoint (p.horizontal_velocity t)).trans hv
  have hmetric := inner_transport_forward hpoint
    (p.horizontal_velocity t) (p.horizontal_velocity t)
  rw [hvelocity] at hmetric
  unfold M14BackwardLIntegrand M14RawLIntegrand
  rw [← hmetric, hpoint]

theorem action_eq_of_curve_eqOn (p q : M14BackwardPath G T τ₁ τ₂ x y)
    (h : Set.EqOn p.curve q.curve (Set.Ioo τ₁ τ₂)) :
    M14BackwardLAction G p = M14BackwardLAction G q :=
  intervalIntegral.integral_congr_Ioo_of_le p.tau_lt.le
    (backwardLIntegrand_eqOn_of_curve_eqOn p q h)

theorem isMinimizing_iff_of_curve_eqOn (p q : M14BackwardPath G T τ₁ τ₂ x y)
    (h : Set.EqOn p.curve q.curve (Set.Ioo τ₁ τ₂)) :
    M14IsMinimizing p ↔ M14IsMinimizing q := by
  unfold M14IsMinimizing
  rw [action_eq_of_curve_eqOn p q h]

end PoincareConjecture.M14
