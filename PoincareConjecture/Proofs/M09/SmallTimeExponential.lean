import PoincareConjecture.Proofs.M09.SmallTimeInjectivity
import PoincareConjecture.Proofs.M09.ChartVelocity
import PoincareConjecture.Proofs.M09.InitialVectorIdentification

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_smallTime_injective {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax : ℝ} (hτmax : 0 < τmax) {p : M} (A : LExponentialFamily F T τmax p)
    (R : ℝ) (_hR : 0 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < τmax ∧ ∀ τ, 0 < τ → τ < δ →
      Set.InjOn (fun Z ↦ A.gamma Z τ) {Z | (F.metric T).tangentNorm p Z ≤ R} ∧
      ∀ Z : TangentSpace (𝓡 n) p, (F.metric T).tangentNorm p Z ≤ R →
        Function.Bijective (A.sliceDifferential Z τ) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  let Q := EuclideanSpace ℝ (Fin n)
  letI : FiniteDimensional ℝ E :=
    VectorBundle.finiteDimensional ℝ Q (TangentSpace (𝓡 n) : M → Type _) p
  let c := chartAt Q p
  let a : E × ℝ → M := fun z ↦ A.squareFamily z.1 z.2
  let U := A.squareDomain ∩ a ⁻¹' c.source
  let f : E × ℝ → Q := fun z ↦ c (a z)
  have ha : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ a A.squareDomain := by
    convert! A.square_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hU : IsOpen U := ha.continuousOn.isOpen_inter_preimage A.square_open c.open_source
  have hf : ContDiffOn ℝ ∞ f U :=
    (contMDiffOn_chart.comp (ha.mono Set.inter_subset_left) (fun z hz ↦ hz.2)).contDiffOn
  have hzeroU (Z : E) : (Z, (0 : ℝ)) ∈ U := by
    refine ⟨A.square_contains ⟨Set.mem_univ _, le_rfl, Real.sqrt_pos.mpr hτmax⟩, ?_⟩
    change A.squareFamily Z 0 ∈ c.source
    rw [A.square_at_zero]
    exact mem_chart_source Q p
  have hzero (Z : E) : f (Z, 0) = c p := by
    change c (A.squareFamily Z 0) = c p
    rw [A.square_at_zero]
  let D : E →L[ℝ] Q := mfderiv (𝓡 n) (𝓡 n) c p
  have hD : Function.Bijective D :=
    (mdifferentiable_chart (I := 𝓡 n) p).mfderiv_bijective (mem_chart_source Q p)
  have htwoD : Function.Bijective ((2 : ℝ) • D) := by
    constructor
    · intro v w hvw
      apply hD.1
      exact (smul_right_injective (M := Q) (by norm_num : (2 : ℝ) ≠ 0)) hvw
    · intro v
      obtain ⟨w, hw⟩ := hD.2 ((2 : ℝ)⁻¹ • v)
      refine ⟨w, ?_⟩
      change (2 : ℝ) • D w = v
      rw [hw, smul_smul]
      norm_num
  let L : E ≃L[ℝ] Q :=
    (LinearEquiv.ofBijective ((2 : ℝ) • D).toLinearMap htwoD).toContinuousLinearEquiv
  have hjet (Z : E) : HasDerivAt (fun s ↦ f (Z, s)) (L Z) 0 := by
    have hsmooth := (lExponentialFamily_squareSlice_contMDiffAt A Z 0
      ⟨le_rfl, Real.sqrt_pos.mpr hτmax⟩).mdifferentiableAt (by simp)
    have h := hasDerivAt_chart_curve p (A.squareFamily Z) 0 (hzeroU Z).2 hsmooth
    change HasDerivAt (fun s ↦ c (A.squareFamily Z s))
      (mfderiv (𝓡 n) (𝓡 n) c (A.squareFamily Z 0)
        (curveVelocity (A.squareFamily Z) 0 : Q)) 0 at h
    rw [lExponentialFamily_initial_velocity, A.square_at_zero] at h
    convert! h using 1
    exact (map_smul D (2 : ℝ) Z).symm
  let K : Set E := {Z | (F.metric T).tangentNorm p Z ≤ R}
  have hKeq : K = Metric.closedBall (0 : E) R := by
    ext Z
    simp only [K, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hK : IsCompact K := by rw [hKeq]; exact isCompact_closedBall (0 : E) R
  have hconv : Convex ℝ K := by rw [hKeq]; exact convex_closedBall (0 : E) R
  obtain ⟨d, hd, hsmall⟩ := exists_uniform_smallTime_injective f U hU hf hzeroU
    (c p) hzero L hjet K hK hconv
  let δ := min (τmax / 2) (d ^ 2)
  have hδ : 0 < δ := lt_min (by linarith) (sq_pos_of_pos hd)
  have hδmax : δ < τmax := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro τ hτ hτδ
  have hτmax' := hτδ.trans hδmax
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hsd : Real.sqrt τ < d := by
    have h := Real.sqrt_lt_sqrt hτ.le (hτδ.trans_le (min_le_right _ _))
    simpa only [Real.sqrt_sq hd.le] using h
  obtain ⟨hinj, hbij⟩ := hsmall (Real.sqrt τ) hs hsd
  have heq : (fun Z : E ↦ A.squareFamily Z (Real.sqrt τ)) = fun Z ↦ A.gamma Z τ := by
    funext Z
    simpa only [Real.sq_sqrt hτ.le] using A.square_agrees Z (Real.sqrt τ)
      ⟨hs.le, Real.sqrt_lt_sqrt hτ.le hτmax'⟩
  constructor
  · intro Z hZ W hW hend
    apply hinj hZ hW
    change c (A.squareFamily Z (Real.sqrt τ)) = c (A.squareFamily W (Real.sqrt τ))
    rw [congrFun heq Z, congrFun heq W]
    exact congrArg c hend
  · intro Z hZ
    obtain ⟨hZU, hZbij⟩ := hbij Z hZ
    have hq : A.gamma Z τ ∈ c.source := by
      have h := hZU.2
      change A.squareFamily Z (Real.sqrt τ) ∈ c.source at h
      rwa [congrFun heq Z] at h
    have hγ : MDifferentiableAt (𝓘(ℝ, E)) (𝓡 n) (fun W ↦ A.gamma W τ) Z :=
      ((A.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
        ⟨Set.mem_univ _, hτ, hτmax'⟩)).comp Z
          (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
    have hc := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hq
    have hchain : fderiv ℝ (fun y ↦ f (y, Real.sqrt τ)) Z =
        (mfderiv (𝓡 n) (𝓡 n) c (A.gamma Z τ)).comp (A.sliceDifferential Z τ) := by
      have hh : HasFDerivAt (fun y ↦ c (A.gamma y τ))
          ((mfderiv (𝓡 n) (𝓡 n) c (A.gamma Z τ)).comp (A.sliceDifferential Z τ)) Z :=
        (hc.hasMFDerivAt.comp Z hγ.hasMFDerivAt).hasFDerivAt
      have hfτ : (fun y ↦ f (y, Real.sqrt τ)) = fun y ↦ c (A.gamma y τ) := by
        funext y
        exact congrArg c (congrFun heq y)
      rw [hfτ]
      exact hh.fderiv
    have hcbij := (mdifferentiable_chart (I := 𝓡 n) p).mfderiv_bijective hq
    rw [hchain] at hZbij
    constructor
    · intro v w hvw
      exact hZbij.1 (congrArg (mfderiv (𝓡 n) (𝓡 n) c (A.gamma Z τ)) hvw)
    · intro v
      obtain ⟨w, hw⟩ := hZbij.2 (mfderiv (𝓡 n) (𝓡 n) c (A.gamma Z τ) v)
      exact ⟨w, hcbij.1 hw⟩

end PoincareConjecture.Proofs.M09
