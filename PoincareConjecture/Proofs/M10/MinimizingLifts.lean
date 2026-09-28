import PoincareConjecture.Statements.Ch06.ReducedLength

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

theorem backwardLIntegrand_eq_of_eventuallyEq {γ η : ℝ → M} {s : ℝ}
    (h : γ =ᶠ[𝓝 s] η) : backwardLIntegrand F T γ s = backwardLIntegrand F T η s := by
  unfold backwardLIntegrand curveVelocity
  rw [h.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n), h.eq_of_nhds]

theorem backwardLLength_eq_of_eqOn {a b : ℝ} {γ η : ℝ → M} (hab : a ≤ b)
    (h : Set.EqOn γ η (Set.Icc a b)) :
    backwardLLength F T a b γ = backwardLLength F T a b η := by
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro s hs
  apply backwardLIntegrand_eq_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
    (fun x hx ↦ h ⟨hx.1.le, hx.2.le⟩)

theorem minimizing_of_eqOn {a b : ℝ} {γ η : BackwardTimePath F T a b}
    (hγ : IsMinimizingBackwardLPath F T a b γ)
    (h : Set.EqOn γ.curve η.curve (Set.Icc a b)) :
    IsMinimizingBackwardLPath F T a b η := by
  intro path hstart hend
  have ha := h ⟨le_rfl, γ.ordered.le⟩
  have hb := h ⟨γ.ordered.le, le_rfl⟩
  rw [← backwardLLength_eq_of_eqOn γ.ordered.le h]
  exact hγ path (hstart.trans ha.symm) (hend.trans hb.symm)

variable [ConnectedSpace M] {p : M}

theorem exists_minimizing_lift (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (q : M) (τ : ℝ)
    (hτ : 0 < τ) (hmax : τ < τmax) :
    ∃ Z : TangentSpace (𝓡 n) p,
      G.gamma Z τ = q ∧
      IsMinimizingBackwardLPath F T 0 τ (G.path Z τ hτ hmax) ∧
      reducedLength F T p q τ = G.toLExponentialFamily.action Z τ / (2 * Real.sqrt τ) := by
  obtain ⟨path, hp, hq, hmin, hlength⟩ := hL.reduced_length_attained τ hτ hmax.le p q
  obtain ⟨Z, hZ, _⟩ := G.minimizers_lift τ hτ hmax path hp hmin
  have hpath : Set.EqOn path.curve (G.path Z τ hτ hmax).curve (Set.Icc 0 τ) := by
    rw [G.path_eq]
    exact hZ
  refine ⟨Z, (hZ ⟨hτ.le, le_rfl⟩).symm.trans hq, minimizing_of_eqOn hmin hpath, ?_⟩
  exact hlength.trans (congrArg (fun a : ℝ ↦ a / (2 * Real.sqrt τ))
    (backwardLLength_eq_of_eqOn hτ.le hZ))

theorem reducedLength_le_normalized_action (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (Z : TangentSpace (𝓡 n) p) (τ : ℝ)
    (hτ : 0 < τ) (hmax : τ < τmax) :
    reducedLength F T p (G.gamma Z τ) τ ≤
      G.toLExponentialFamily.action Z τ / (2 * Real.sqrt τ) := by
  obtain ⟨path, hp, hq, hmin, hlength⟩ :=
    hL.reduced_length_attained τ hτ hmax.le p (G.gamma Z τ)
  have hstart : (G.path Z τ hτ hmax).curve 0 = path.curve 0 := by
    rw [G.path_eq, G.gamma_at_zero, hp]
  have hend : (G.path Z τ hτ hmax).curve τ = path.curve τ := by
    rw [G.path_eq, hq]
  have hcomp := hmin (G.path Z τ hτ hmax) hstart hend
  rw [G.path_eq] at hcomp
  rw [hlength]
  exact div_le_div_of_nonneg_right hcomp
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg τ))

end PoincareConjecture.M10
