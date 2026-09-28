import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RicciTimeGluing












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M44




theorem hasFDerivWithinAt_birth_of_continuous_derivative
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {T : ℝ} (hT : 0 < T) {f : ℝ × E → V}
    {D : ℝ × E → (ℝ × E) →L[ℝ] V}
    (hf : ContinuousOn f (Ico 0 T ×ˢ univ))
    (hD : ContinuousOn D (Ico 0 T ×ˢ univ))
    (hderivative : ∀ p ∈ Ioo 0 T ×ˢ univ, HasFDerivAt f (D p) p)
    (x : E) :
    HasFDerivWithinAt f (D (0, x)) (Ico 0 T ×ˢ univ) (0, x) := by
  let S : Set (ℝ × E) := Ioo 0 (T / 2) ×ˢ univ
  have hhalf : 0 < T / 2 := half_pos hT
  have hhalfT : T / 2 < T := half_lt_self hT
  have hS : S ⊆ Ioo 0 T ×ˢ univ := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hhalfT⟩, hp.2⟩
  have hSco : S ⊆ Ico 0 T ×ˢ univ :=
    hS.trans (prod_mono Ioo_subset_Ico_self Subset.rfl)
  have hclosure : closure S = Icc 0 (T / 2) ×ˢ (univ : Set E) := by
    dsimp only [S]
    rw [closure_prod_eq, closure_Ioo hhalf.ne, closure_univ]
  have hclosure_sub : closure S ⊆ Ico 0 T ×ˢ univ := by
    rw [hclosure]
    exact fun p hp => ⟨⟨hp.1.1, hp.1.2.trans_lt hhalfT⟩, hp.2⟩
  have hzero : (0, x) ∈ Ico 0 T ×ˢ (univ : Set E) :=
    ⟨⟨le_rfl, hT⟩, mem_univ _⟩
  have hlimit : Tendsto (fderiv ℝ f) (𝓝[S] (0, x)) (𝓝 (D (0, x))) := by
    apply ((hD (0, x) hzero).mono hSco).congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hderivative p (hS hp)).fderiv.symm
  have hclosed : HasFDerivWithinAt f (D (0, x)) (closure S) (0, x) :=
    hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun p hp => (hderivative p (hS hp)).differentiableAt.differentiableWithinAt)
      ((convex_Ioo (0 : ℝ) (T / 2)).prod convex_univ)
      (isOpen_Ioo.prod isOpen_univ)
      (fun p hp => (hf p (hclosure_sub hp)).mono hSco) hlimit
  apply hclosed.mono_of_mem_nhdsWithin
  have hnear : {p : ℝ × E | p.1 < T / 2} ∈ 𝓝 (0, x) :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hhalf)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnear] with p hp hpt
  rw [hclosure]
  exact ⟨⟨hp.1.1, hpt.le⟩, hp.2⟩

set_option maxHeartbeats 800000 in





theorem contDiffOn_of_birth_jet_evolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : ℕ → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {T : ℝ} (hT : 0 < T) (f : ∀ i, ℝ × E → V i)
    (spatial : ∀ i, V (i + 1) →L[ℝ] E →L[ℝ] V i) (arity : ℕ → ℕ)
    (rhs : ∀ i, (∀ j : Fin (arity i), V j.1) → V i)
    (domain : ∀ i, Set (∀ j : Fin (arity i), V j.1))
    (hrhs : ∀ i, ContDiffOn ℝ ∞ (rhs i) (domain i))
    (hrange : ∀ i p, p ∈ Ico 0 T ×ˢ univ →
      (fun j : Fin (arity i) => f j.1 p) ∈ domain i)
    (hcont : ∀ i, ContinuousOn (f i) (Ico 0 T ×ˢ univ))
    (hspatial : ∀ i t, t ∈ Ico 0 T → ∀ x : E,
      HasFDerivAt (fun y => f i (t, y)) (spatial i (f (i + 1) (t, x))) x)
    (htime : ∀ i t, t ∈ Ioo 0 T → ∀ x : E,
      HasDerivAt (fun s => f i (s, x))
        (rhs i (fun j : Fin (arity i) => f j.1 (t, x))) t) :
    ∀ i, ContDiffOn ℝ ∞ (f i) (Ico 0 T ×ˢ univ) := by
  let H (i : ℕ) (p : ℝ × E) := rhs i (fun j : Fin (arity i) => f j.1 p)
  have hH (i : ℕ) : ContinuousOn (H i) (Ico 0 T ×ˢ univ) :=
    (hrhs i).continuousOn.comp (continuousOn_pi.mpr fun j => hcont j.1) (hrange i)
  let D (i : ℕ) (p : ℝ × E) : ℝ × E →L[ℝ] V i :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (H i p)).coprod (spatial i (f (i + 1) p))
  have hDt (i : ℕ) : ContinuousOn
      (fun p => (ContinuousLinearMap.id ℝ ℝ).smulRight (H i p)) (Ico 0 T ×ˢ univ) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ (V i)
      (ContinuousLinearMap.id ℝ ℝ)).continuous.comp_continuousOn (hH i)
  have hDx (i : ℕ) : ContinuousOn (fun p => spatial i (f (i + 1) p)) (Ico 0 T ×ˢ univ) :=
    (spatial i).continuous.comp_continuousOn (hcont (i + 1))
  have hD (i : ℕ) : ContinuousOn (D i) (Ico 0 T ×ˢ univ) :=
    (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ)
      (F := E) (G := V i) ℝ).continuous.comp_continuousOn ((hDt i).prodMk (hDx i))
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set E) ⊆ Ico 0 T ×ˢ univ :=
    prod_mono Ioo_subset_Ico_self Subset.rfl
  have hderivative (i : ℕ) (p : ℝ × E) (hp : p ∈ Ioo 0 T ×ˢ univ) :
      HasFDerivAt (f i) (D i p) p := by
    apply (hasStrictFDerivAt_uncurry_coprod
      (f := fun t x => f i (t, x))
      (f₁ := fun t x => (ContinuousLinearMap.id ℝ ℝ).smulRight (H i (t, x)))
      (f₂ := fun t x => spatial i (f (i + 1) (t, x))) ?_ ?_
      (((hDt i).mono hsub).continuousAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp))
      (((hDx i).mono hsub).continuousAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp))).hasFDerivAt
    · filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
      exact (htime i q.1 hq.1 q.2).hasFDerivAt
    · filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
      exact hspatial i q.1 (Ioo_subset_Ico_self hq.1) q.2
  have hwithin (i : ℕ) (p : ℝ × E) (hp : p ∈ Ico 0 T ×ˢ univ) :
      HasFDerivWithinAt (f i) (D i p) (Ico 0 T ×ˢ univ) p := by
    rcases p with ⟨t, x⟩
    rcases eq_or_lt_of_le hp.1.1 with hzero | hpos
    · change 0 = t at hzero
      subst t
      exact hasFDerivWithinAt_birth_of_continuous_derivative hT
        (hcont i) (hD i) (hderivative i) x
    · exact (hderivative i (t, x) ⟨⟨hpos, hp.1.2⟩, hp.2⟩).hasFDerivWithinAt
  have hfinite : ∀ m : ℕ, ∀ i, ContDiffOn ℝ m (f i) (Ico 0 T ×ˢ univ) := by
    intro m
    induction m with
    | zero => exact fun i => contDiffOn_zero.mpr (hcont i)
    | succ m ih =>
        intro i
        have hHm : ContDiffOn ℝ m (H i) (Ico 0 T ×ˢ univ) :=
          ((hrhs i).of_le (by exact_mod_cast le_top)).comp
            (contDiffOn_pi.mpr fun j => ih j.1) (hrange i)
        have htm := (contDiffOn_const (c := ContinuousLinearMap.id ℝ ℝ)).smulRight hHm
        have hxm : ContDiffOn ℝ m (fun p => spatial i (f (i + 1) p)) (Ico 0 T ×ˢ univ) :=
          (spatial i).contDiff.comp_contDiffOn (ih (i + 1))
        have hDm : ContDiffOn ℝ m (D i) (Ico 0 T ×ˢ univ) :=
          (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ)
            (F := E) (G := V i) ℝ).contDiff.comp_contDiffOn (htm.prodMk hxm)
        rw [Nat.cast_add, Nat.cast_one]
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
          ((uniqueDiffOn_Ico (0 : ℝ) T).prod uniqueDiffOn_univ)).mpr
        exact ⟨by simp, D i, hDm, hwithin i⟩
  exact fun i => contDiffOn_infty.mpr (fun m => hfinite m i)

open SpacetimeBounds SpacetimeBounds.Bootstrap

set_option maxHeartbeats 800000 in





theorem contDiffOn_ricci_coefficients_birth
    {n : ℕ} {T : ℝ} (hT : 0 < T)
    {B : ℝ × EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    (hsmooth : ContDiffOn ℝ ∞ B (Ioo 0 T ×ˢ univ))
    (hspace : ∀ t ∈ Ico 0 T, ContDiffOn ℝ ∞ (fun x => B (t, x)) univ)
    (hjets : ∀ m : ℕ, ContinuousOn
      (fun p => iteratedFDeriv ℝ m (fun x => B (p.1, x)) p.2) (Ico 0 T ×ˢ univ))
    (hinvertible : ∀ p ∈ Ico 0 T ×ˢ univ, (B p).IsInvertible)
    (hevolution : ∀ t ∈ Ioo 0 T, ∀ x : EuclideanSpace ℝ (Fin n),
      HasDerivAt (fun s => B (s, x))
        (ricciFlowOperator n (metricTwoJet (fun y => B (t, y)) x)) t) :
    ContDiffOn ℝ ∞ B (Ico 0 T ×ˢ univ) := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := MetricCoefficient n
  let A (m : ℕ) (p : ℝ × E) := iteratedFDeriv ℝ m (fun x => B (p.1, x)) p.2
  let D (m : ℕ) : (E [×(m + 1)]→L[ℝ] V) →L[ℝ] E →L[ℝ] E [×m]→L[ℝ] V :=
    (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (m + 1) => E) V).toContinuousLinearEquiv.toContinuousLinearMap
  have hrange (p : ℝ × E) (hp : p ∈ Ico 0 T ×ˢ univ) :
      spatialJet 2 B p ∈ jetRicciFlowDomain n := by
    change (twoJetProjection n (spatialJet 2 B p)).1.IsInvertible
    rw [twoJetProjection_spatialJet]
    exact hinvertible p hp
  have hfields : ∀ m, ContDiffOn ℝ ∞ (A m) (Ico 0 T ×ˢ univ) := by
    apply contDiffOn_of_birth_jet_evolution hT A D
      (fun m => 2 + m + 1) (operator 2 (jetRicciFlowOperator n))
      (fun m => (baseProjection 2 m) ⁻¹' jetRicciFlowDomain n)
      (fun m => contDiffOn_operator (isOpen_jetRicciFlowDomain n)
        (contDiffOn_jetRicciFlowOperator n) m)
    · intro m p hp
      change baseProjection 2 m (spatialJet (2 + m) B p) ∈ jetRicciFlowDomain n
      simpa only [baseProjection_spatialJet] using hrange p hp
    · exact hjets
    · intro m t ht x
      have hg := (hspace t ht).contDiffAt (isOpen_univ.mem_nhds (mem_univ x))
      have hd := (hg.iteratedFDeriv_right (i := m) (m := 1)
        (by exact_mod_cast le_top)).differentiableAt (by simp) |>.hasFDerivAt
      change HasFDerivAt (iteratedFDeriv ℝ m (fun y => B (t, y)))
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) V)
          (iteratedFDeriv ℝ (m + 1) (fun y => B (t, y)) x)) x
      rw [iteratedFDeriv_succ_eq_comp_left]
      simpa only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply] using hd
    · intro m t ht x
      change HasDerivAt (fun s => iteratedFDeriv ℝ m (fun y => B (s, y)) x)
        (operator 2 (jetRicciFlowOperator n) m (spatialJet (2 + m) B (t, x))) t
      rw [operator_spatialJet (isOpen_jetRicciFlowDomain n)
        (contDiffOn_jetRicciFlowOperator n) hsmooth isOpen_Ioo isOpen_univ
        (fun p hp => hrange p ⟨Ioo_subset_Ico_self hp.1, hp.2⟩) ht (mem_univ x) m]
      apply SpacetimeBounds.hasDerivAt_spatialJet hsmooth isOpen_Ioo isOpen_univ ht
      · intro y _hy
        simpa only [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
          using hevolution t ht y
      · exact mem_univ x
  exact (continuousMultilinearCurryFin0 ℝ E V).toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hfields 0)

end PoincareConjecture.M44
