import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Manifold

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem radialVariation_field_eq
    {e : EuclideanSpace ℝ (Fin n) → M} (v w : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e (t • v)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1 =
      mfderiv (𝓡 n) (𝓡 n) e (t • v) (t • w) := by
  have hline : HasDerivAt (fun s : ℝ => t • (v + s • w)) (t • w) 0 := by
    simpa only [one_smul, id_eq, Pi.smul_apply] using!
      (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v).const_smul t
  have he' : MDifferentiableAt (𝓡 n) (𝓡 n) e (t • (v + (0 : ℝ) • w)) := by
    simpa using he
  have hd := mfderiv_comp 0 he' hline.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hd
  have hd1 := congrArg (fun L => L 1) hd
  rw [zero_smul, add_zero] at hd1
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1 =
    mfderiv (𝓡 n) (𝓡 n) e (t • v)
      (fderiv ℝ (fun s : ℝ => t • (v + s • w)) 0 1) at hd1
  rw [fderiv_eq_smul_deriv, one_smul, hline.deriv] at hd1
  exact hd1

theorem radialVariation_field_zero
    (e : EuclideanSpace ℝ (Fin n) → M) (v w : EuclideanSpace ℝ (Fin n)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e ((0 : ℝ) • (v + s • w))) 0 1 = 0 := by
  have hconst : (fun s : ℝ => e ((0 : ℝ) • (v + s • w))) = fun _ : ℝ => e 0 := by
    funext s
    rw [zero_smul]
  rw [hconst, mfderiv_const]
  rfl

theorem radialVariation_field_one
    {e : EuclideanSpace ℝ (Fin n) → M} (v w : EuclideanSpace ℝ (Fin n))
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e v) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e ((1 : ℝ) • (v + s • w))) 0 1 =
      mfderiv (𝓡 n) (𝓡 n) e v w := by
  have h := radialVariation_field_eq v w 1 (by simpa using he)
  rw [show (1 : ℝ) • v = v from one_smul ℝ v,
    show (1 : ℝ) • w = w from one_smul ℝ w] at h
  exact h

theorem radialVariation_initial_covariantDerivative
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e 0) (v w : EuclideanSpace ℝ (Fin n)) :
    let γ : ℝ → M := fun t => e (t • v)
    let J : (t : ℝ) → TangentSpace (𝓡 n) (γ t) :=
      fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1
    ConnectionVariation.manifoldCovDerivAlong g γ J 1 0 =
      mfderiv (𝓡 n) (𝓡 n) e 0 w := by
  let c := extChartAt (𝓡 n) (e 0)
  let q := c ∘ e
  let γ : ℝ → M := fun t => e (t • v)
  let J : (t : ℝ) → TangentSpace (𝓡 n) (γ t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1
  let V : ℝ → EuclideanSpace ℝ (Fin n) := fun t => t • fderiv ℝ q (t • v) w
  have hq : ContDiffAt ℝ ∞ q 0 :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (mem_chart_source _ _)).comp 0 he)
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      MDifferentiableAt (𝓡 n) (𝓡 n) e (t • v) ∧ e (t • v) ∈ c.source := by
    have hdiff := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
      (he.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
    have hsource := he.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (e 0)).mem_nhds
        (mem_extChartAt_source (I := 𝓡 n) (e 0)))
    have hline : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
      have h : Continuous (fun t : ℝ => t • v) := by fun_prop
      have h' := h.continuousAt (x := (0 : ℝ))
      change Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)) at h'
      rw [zero_smul] at h'
      exact h'
    filter_upwards [hline (hdiff.and hsource)] with t ht
    exact ⟨ht.1.mdifferentiableAt (by simp), ht.2⟩
  have hVnear : (fun t => mfderiv (𝓡 n) (𝓡 n) c (γ t) (J t)) =ᶠ[𝓝 0] V := by
    filter_upwards [hnear] with t ht
    have hd := mfderiv_comp (t • v)
      (mdifferentiableAt_extChartAt (by simpa only [c, extChartAt_source] using ht.2)) ht.1
    rw [mfderiv_eq_fderiv] at hd
    change mfderiv (𝓡 n) (𝓡 n) c (e (t • v))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1) = _
    rw [radialVariation_field_eq v w t ht.1]
    have hd1 := congrArg (fun L => L (t • w)) hd
    change mfderiv (𝓡 n) (𝓡 n) c (e (t • v))
      (mfderiv (𝓡 n) (𝓡 n) e (t • v) (t • w)) = V t
    change fderiv ℝ q (t • v) (t • w) =
      mfderiv (𝓡 n) (𝓡 n) c (e (t • v))
        (mfderiv (𝓡 n) (𝓡 n) e (t • v) (t • w)) at hd1
    rw [← hd1]
    exact map_smul _ _ _
  have hF : DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ q (t • v) w) 0 := by
    have h : ContDiffAt ℝ ∞ (fun x => fderiv ℝ q x w) 0 :=
      (hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    have h' : ContDiffAt ℝ ∞ (fun x => fderiv ℝ q x w) ((0 : ℝ) • v) := by
      simpa using h
    exact (h'.comp (f := fun t : ℝ => t • v) 0
      (by fun_prop)).differentiableAt (by simp)
  have hV : HasDerivAt V (fderiv ℝ q 0 w) 0 := by
    simpa only [Pi.smul_apply, id_eq, one_smul, zero_smul, zero_add, V] using!
      (hasDerivAt_id (0 : ℝ)).smul hF.hasDerivAt
  change ConnectionVariation.manifoldCovDerivAlong g γ J 1 0 = _
  unfold ConnectionVariation.manifoldCovDerivAlong
  have hγ0 : γ 0 = e 0 := by simp [γ]
  rw [hγ0]
  change (mfderiv (𝓡 n) (𝓡 n) c (e 0)).inverse
    (ConnectionVariation.covDerivAlong
      (CoordinateExponential.christoffelBilinear (g.pullbackCoefficients c.symm))
      (c ∘ γ) (fun t => mfderiv (𝓡 n) (𝓡 n) c (γ t) (J t)) 1 0) = _
  rw [ConnectionVariation.covDerivAlong_congr _ _ hVnear,
    ConnectionVariation.covDerivAlong]
  have hV0 : V 0 = 0 := by simp [V]
  rw [hV0, map_zero, add_zero, fderiv_eq_smul_deriv, one_smul, hV.deriv]
  have hd := mfderiv_comp 0 (mdifferentiableAt_extChartAt (mem_chart_source _ _))
    (he.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  have hdw := congrArg (fun L => L w) hd
  change fderiv ℝ q 0 w = mfderiv (𝓡 n) (𝓡 n) c (e 0)
    (mfderiv (𝓡 n) (𝓡 n) e 0 w) at hdw
  rw [hdw]
  exact (isInvertible_mfderiv_extChartAt (I := 𝓡 n)
    (mem_extChartAt_source (e 0))).inverse_apply_self _

theorem radialVariation_initial_tangentNorm
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e 0)
    (hnorm : ∀ v w, g.pullbackCoefficients e 0 v w = inner ℝ v w)
    (v w : EuclideanSpace ℝ (Fin n)) :
    let γ : ℝ → M := fun t => e (t • v)
    let J : (t : ℝ) → TangentSpace (𝓡 n) (γ t) :=
      fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1
    g.tangentNorm (γ 0) (ConnectionVariation.manifoldCovDerivAlong g γ J 1 0) = ‖w‖ := by
  dsimp only
  rw [g.radialVariation_initial_covariantDerivative he v w]
  change Real.sqrt (g.inner (e ((0 : ℝ) • v))
    (mfderiv (𝓡 n) (𝓡 n) e 0 w) (mfderiv (𝓡 n) (𝓡 n) e 0 w)) = ‖w‖
  rw [zero_smul]
  have h := hnorm w w
  change g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 w)
    (mfderiv (𝓡 n) (𝓡 n) e 0 w) = inner ℝ w w at h
  rw [h, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]

end PoincareConjecture.RiemannianMetric
