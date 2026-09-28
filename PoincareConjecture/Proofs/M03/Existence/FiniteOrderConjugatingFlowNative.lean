import PoincareConjecture.Proofs.M03.Existence.CompactTimeDependentFlowNative









set_option autoImplicit false

open Set Filter Manifold
open scoped Topology ContDiff Bundle

noncomputable section

namespace PoincareConjecture.FiniteOrderConjugatingFlowNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓡 n
local notation "J" => ModelWithCorners.prod (𝓡 n) 𝓘(ℝ, ℝ)

def suspension (X : (q : M × ℝ) → TangentSpace I q.1)
    (q : M × ℝ) : TangentSpace J q := (X q, 1)

theorem contMDiff_suspension {k : ℕ∞}
    (X : (q : M × ℝ) → TangentSpace I q.1)
    (hX : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun q => (Bundle.TotalSpace.mk' E q.1 (X q) : TangentBundle I M))) :
    ContMDiff J (ModelWithCorners.prod J 𝓘(ℝ, E × ℝ)) k
      (fun q => (⟨q, suspension X q⟩ : TangentBundle J (M × ℝ))) := by
  have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) k
      (fun t : ℝ => (Bundle.TotalSpace.mk' ℝ t (1 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro t
    apply (contMDiffAt_vectorSpace_iff_contDiffAt
      (V := fun _ : ℝ => ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t))).2
    exact contDiffAt_const
  have ht := hone.comp
    (contMDiff_snd : ContMDiff J 𝓘(ℝ, ℝ) k (fun q : M × ℝ => q.2))
  have hpair := hX.prodMk ht
  have hsymm : ContMDiff
      ((ModelWithCorners.prod I 𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      (ModelWithCorners.prod J 𝓘(ℝ, E × ℝ)) k
      ((equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ).symm) :=
    contMDiff_equivTangentBundleProd_symm
  exact hsymm.comp hpair

open CompactTimeDependentFlowNative

set_option backward.isDefEq.respectTransparency false in
theorem time_coordinate
    (X : (q : M × ℝ) → TangentSpace I q.1)
    {ε : ℝ} (hε : 0 < ε) {α : (M × ℝ) × ℝ → M × ℝ} {z : M × ℝ}
    (hzero : α (z, 0) = z)
    (hcurve : IsMIntegralCurveOn (fun s => α (z, s)) (suspension X) (Ioo (-ε) ε))
    {s : ℝ} (hs : s ∈ Ioo (-ε) ε) : (α (z, s)).2 = z.2 + s := by
  have hder (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt (fun u => (α (z, u)).2) 1 t := by
    have hp := (hasMFDerivAt_snd (α (z, t))).comp t
      ((hcurve t ht).hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2))
    have hD : (1 : ℝ →L[ℝ] ℝ) =
        (ContinuousLinearMap.snd ℝ (TangentSpace I (α (z, t)).1)
          (TangentSpace 𝓘(ℝ, ℝ) (α (z, t)).2)) ∘L
            ((1 : ℝ →L[ℝ] ℝ).smulRight (suspension X (α (z, t)))) := by
      apply ContinuousLinearMap.ext
      intro r
      change r = (r • (X (α (z, t)), (1 : ℝ))).2
      change r = r * (1 : ℝ)
      exact (mul_one r).symm
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u => (α (z, u)).2) t
      ((ContinuousLinearMap.snd ℝ (TangentSpace I (α (z, t)).1)
        (TangentSpace 𝓘(ℝ, ℝ) (α (z, t)).2)) ∘L
          ((1 : ℝ →L[ℝ] ℝ).smulRight (suspension X (α (z, t))))) at hp
    have hp' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u => (α (z, u)).2) t
        (1 : ℝ →L[ℝ] ℝ) := hp.congr_mfderiv hD.symm
    have hfd : HasFDerivAt (fun u : ℝ => (α (z, u)).2) (1 : ℝ →L[ℝ] ℝ) t :=
      hp'.hasFDerivAt
    simpa only [one_apply_eq_self] using hfd.hasDerivAt
  have hlinear (t : ℝ) : HasDerivAt (fun u : ℝ => z.2 + u) 1 t :=
    (hasDerivAt_id t).const_add z.2
  exact isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
    (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (hlinear t).differentiableAt.differentiableWithinAt)
    (fun t ht => (hder t ht).deriv.trans (hlinear t).deriv.symm)
    (show 0 ∈ Ioo (-ε) ε from ⟨neg_lt_zero.mpr hε, hε⟩)
    (by simp only [hzero, add_zero]) hs

theorem spatial_derivative
    (X : (q : M × ℝ) → TangentSpace I q.1)
    {ε : ℝ} {α : (M × ℝ) × ℝ → M × ℝ} {z : M × ℝ}
    (hcurve : IsMIntegralCurveOn (fun s => α (z, s)) (suspension X) (Ioo (-ε) ε))
    {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (α (z, s)).1) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (α (z, t)))) := by
  have hp := (hasMFDerivAt_fst (α (z, t))).comp t
    ((hcurve t ht).hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2))
  have hD : (1 : ℝ →L[ℝ] ℝ).smulRight (X (α (z, t))) =
      (ContinuousLinearMap.fst ℝ (TangentSpace I (α (z, t)).1)
        (TangentSpace 𝓘(ℝ, ℝ) (α (z, t)).2)) ∘L
          ((1 : ℝ →L[ℝ] ℝ).smulRight (suspension X (α (z, t)))) := by
    apply ContinuousLinearMap.ext
    intro r
    rfl
  rw [hD]
  exact hp

variable [T2Space M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_contDiff_suspended_local_flow [CompactSpace M]
    {k : ℕ∞} (hk : k ≠ 0)
    (X : (q : M × ℝ) → TangentSpace I q.1)
    (hX : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun q => (Bundle.TotalSpace.mk' E q.1 (X q) : TangentBundle I M))) :
    ∃ U : Set (M × ℝ), IsOpen U ∧
      ((univ : Set M) ×ˢ Icc (-1 : ℝ) 1) ⊆ U ∧
      ∃ ε > 0, ∃ α : (M × ℝ) × ℝ → M × ℝ,
        (∀ z ∈ U, α (z, 0) = z) ∧
        (∀ z ∈ U, IsMIntegralCurveOn (fun s => α (z, s)) (suspension X) (Ioo (-ε) ε)) ∧
        ContMDiffOn (ModelWithCorners.prod J 𝓘(ℝ, ℝ)) J k α (U ×ˢ Ioo (-ε) ε) := by
  have hprod : IsManifold J ∞ (M × ℝ) := inferInstance
  letI : ChartedSpace (E × ℝ) (M × ℝ) := prodChartedSpace E M ℝ ℝ
  letI : IsManifold 𝓘(ℝ, E × ℝ) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact hprod
  have hV : ContMDiff 𝓘(ℝ, E × ℝ)
      (𝓘(ℝ, E × ℝ).prod 𝓘(ℝ, E × ℝ)) k
      (fun z => (⟨z, suspension X z⟩ : TangentBundle 𝓘(ℝ, E × ℝ) (M × ℝ))) := by
    simpa +instances only [modelWithCornersSelf_prod] using contMDiff_suspension X hX
  obtain ⟨U, hUo, hK, ε, hε, α, hzero, hcurve, hsm⟩ :=
    exists_contDiff_local_flow_on_compact hk (suspension X) hV
      (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)))
  refine ⟨U, hUo, hK, ε, hε, α, hzero, ?_, ?_⟩
  · intro z hz
    exact hcurve z hz
  · simp_rw +instances [modelWithCornersSelf_prod] at hsm
    exact hsm

theorem local_step_compare
    (X Y : (q : M × ℝ) → TangentSpace I q.1)
    (hX : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) 1
      (fun q => (Bundle.TotalSpace.mk' E q.1 (X q) : TangentBundle I M)))
    {T ε η : ℝ} (hT : 0 < T) (hTε : T ≤ ε) (hη : 0 < η)
    (hYX : ∀ q : M × ℝ, q.2 ∈ Ico 0 T → Y q = X q)
    {α β : (M × ℝ) × ℝ → M × ℝ} {x : M}
    (hα0 : α ((x, 0), 0) = (x, 0))
    (hα : IsMIntegralCurveOn (fun s => α ((x, 0), s)) (suspension X) (Ioo (-ε) ε))
    {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (had : a + d < T) (hdη : d < η)
    (hβ0 : β (α ((x, 0), a), 0) = α ((x, 0), a))
    (hβ : IsMIntegralCurveOn (fun s => β (α ((x, 0), a), s))
      (suspension Y) (Ioo (-η) η)) :
    β (α ((x, 0), a), d) = α ((x, 0), a + d) := by
  have hε : 0 < ε := hT.trans_le hTε
  have haT : a < T := by linarith
  have hatime : (α ((x, 0), a)).2 = a := by
    simpa only [zero_add] using time_coordinate X hε hα0 hα
      (show a ∈ Ioo (-ε) ε from ⟨by linarith, haT.trans_le hTε⟩)
  let L := min η (T - a)
  have hL : 0 < L := lt_min hη (sub_pos.mpr haT)
  have hdL : d < L := lt_min hdη (by linarith)
  have hsub : Ico 0 L ⊆ Ioo (-η) η := by
    intro s hs
    exact ⟨(neg_lt_zero.mpr hη).trans_le hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hβX : IsMIntegralCurveOn (fun s => β (α ((x, 0), a), s))
      (suspension X) (Ico 0 L) := by
    intro s hs
    have htime := time_coordinate Y hη hβ0 hβ (hsub hs)
    rw [hatime] at htime
    have habs : (β (α ((x, 0), a), s)).2 ∈ Ico 0 T := by
      rw [htime]
      exact ⟨add_nonneg ha hs.1, by linarith [hs.2.trans_le (min_le_right η (T - a))]⟩
    have hfield : suspension Y (β (α ((x, 0), a), s)) =
        suspension X (β (α ((x, 0), a), s)) := by
      dsimp only [suspension]
      rw [hYX _ habs]
    have hder := (hβ.mono hsub) s hs
    simpa only [hfield] using hder
  have hshift : Ico 0 L ⊆ {s : ℝ | s + a ∈ Ioo (-ε) ε} := by
    intro s hs
    refine ⟨by linarith [hs.1], ?_⟩
    have hsL : s < T - a := hs.2.trans_le (min_le_right _ _)
    linarith
  have heq := isMIntegralCurveOn_Ico_eqOn (contMDiff_suspension X hX) hL hβX
    ((hα.comp_add a).mono hshift) (by simpa only [Function.comp_apply, zero_add] using hβ0)
  simpa only [Function.comp_apply, add_comm d a] using heq ⟨hd, hdL⟩

def spatialStep (α : (M × ℝ) × ℝ → M × ℝ) (a d : ℝ) (x : M) : M :=
  (α ((x, a), d)).1

theorem spatialStep_inverse
    (X : (q : M × ℝ) → TangentSpace I q.1)
    (hX : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) 1
      (fun q => (Bundle.TotalSpace.mk' E q.1 (X q) : TangentBundle I M)))
    {U : Set (M × ℝ)} (hK : ((univ : Set M) ×ˢ Icc (-1 : ℝ) 1) ⊆ U)
    {ε : ℝ} (hε : 0 < ε) {α : (M × ℝ) × ℝ → M × ℝ}
    (hzero : ∀ z ∈ U, α (z, 0) = z)
    (hcurve : ∀ z ∈ U,
      IsMIntegralCurveOn (fun s => α (z, s)) (suspension X) (Ioo (-ε) ε))
    {a d : ℝ} (ha : a ∈ Icc (-1 : ℝ) 1) (had : a + d ∈ Icc (-1 : ℝ) 1)
    (hd : d ∈ Ioo (-(ε / 2)) (ε / 2)) :
    Function.LeftInverse (spatialStep α (a + d) (-d)) (spatialStep α a d) ∧
      Function.RightInverse (spatialStep α (a + d) (-d)) (spatialStep α a d) := by
  have hsmall : Ioo (-(ε / 2)) (ε / 2) ⊆ Ioo (-ε) ε :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  have hnd : -d ∈ Ioo (-(ε / 2)) (ε / 2) :=
    ⟨by linarith [hd.2], by linarith [hd.1]⟩
  have hstart (x : M) {b : ℝ} (hb : b ∈ Icc (-1 : ℝ) 1) : (x, b) ∈ U :=
    hK ⟨mem_univ _, hb⟩
  have hf (x : M) : α ((x, a), d) = (spatialStep α a d x, a + d) := by
    apply Prod.ext
    · rfl
    exact time_coordinate X hε (hzero _ (hstart x ha))
      (hcurve _ (hstart x ha)) (hsmall hd)
  have hr (x : M) : α ((x, a + d), -d) = (spatialStep α (a + d) (-d) x, a) := by
    apply Prod.ext
    · rfl
    simpa only [add_neg_cancel_right] using
      time_coordinate X hε (hzero _ (hstart x had))
        (hcurve _ (hstart x had)) (hsmall hnd)
  constructor
  · intro x
    have hret : α ((x, a), d) ∈ U := by
      rw [hf x]
      exact hstart _ had
    have h := local_flow_reverse (contMDiff_suspension X hX) hε hzero hcurve
      (hstart x ha) hd hret
    rw [hf x] at h
    exact congrArg Prod.fst h
  · intro x
    have hret : α ((x, a + d), -d) ∈ U := by
      rw [hr x]
      exact hstart _ ha
    have h := local_flow_reverse (contMDiff_suspension X hX) hε hzero hcurve
      (hstart x had) hnd hret
    rw [hr x, neg_neg] at h
    exact congrArg Prod.fst h

theorem contMDiffOn_spatialStep {k : ℕ∞}
    {U : Set (M × ℝ)} {ε : ℝ} {α : (M × ℝ) × ℝ → M × ℝ}
    (hα : ContMDiffOn (ModelWithCorners.prod J 𝓘(ℝ, ℝ)) J k α
      (U ×ˢ Ioo (-ε) ε))
    {S : Set ℝ} (a d : ℝ)
    (ha : ∀ t ∈ S, ∀ x : M, (x, a * t) ∈ U)
    (hd : ∀ t ∈ S, d * t ∈ Ioo (-ε) ε) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
      (fun q : ℝ × M => spatialStep α (a * q.1) (d * q.1) q.2) (S ×ˢ univ) := by
  have ha' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k (fun t : ℝ => a * t) :=
    (contDiff_const.mul contDiff_id).contMDiff
  have hd' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k (fun t : ℝ => d * t) :=
    (contDiff_const.mul contDiff_id).contMDiff
  have he : ContMDiff (𝓘(ℝ, ℝ).prod I) (ModelWithCorners.prod J 𝓘(ℝ, ℝ)) k
      (fun q : ℝ × M => ((q.2, a * q.1), d * q.1)) :=
    (contMDiff_snd.prodMk (ha'.comp contMDiff_fst)).prodMk (hd'.comp contMDiff_fst)
  have hh : ContMDiffOn (𝓘(ℝ, ℝ).prod I) J k
      (fun q : ℝ × M => α ((q.2, a * q.1), d * q.1)) (S ×ˢ univ) :=
    hα.comp he.contMDiffOn (fun q hq => ⟨ha _ hq.1 _, hd _ hq.1⟩)
  exact fun q hq => (hh q hq).fst

def forwardIter (α : (M × ℝ) × ℝ → M × ℝ) (c : ℝ) : ℕ → ℝ → M → M
  | 0, _, x => x
  | j + 1, t, x => spatialStep α ((j : ℝ) * c * t) (c * t) (forwardIter α c j t x)

def reverseIter (α : (M × ℝ) × ℝ → M × ℝ) (c : ℝ) : ℕ → ℝ → M → M
  | 0, _, x => x
  | j + 1, t, x => reverseIter α c j t
      (spatialStep α (((j : ℝ) + 1) * c * t) (-(c * t)) x)

theorem contMDiffOn_forwardIter {k : ℕ∞} {α : (M × ℝ) × ℝ → M × ℝ}
    {c : ℝ} {m : ℕ} {S : Set ℝ}
    (hstep : ∀ j < m, ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
      (fun q : ℝ × M => spatialStep α ((j : ℝ) * c * q.1) (c * q.1) q.2)
      (S ×ˢ univ)) :
    ∀ j ≤ m, ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
      (fun q : ℝ × M => forwardIter α c j q.1 q.2) (S ×ˢ univ) := by
  intro j
  induction j with
  | zero => intro _; exact contMDiff_snd.contMDiffOn
  | succ j ih =>
      intro hj
      exact (hstep j (Nat.lt_of_succ_le hj)).comp
        (contMDiff_fst.contMDiffOn.prodMk (ih (Nat.le_of_succ_le hj)))
        (fun q hq => ⟨hq.1, mem_univ _⟩)

theorem contMDiffOn_reverseIter {k : ℕ∞} {α : (M × ℝ) × ℝ → M × ℝ}
    {c : ℝ} {m : ℕ} {S : Set ℝ}
    (hstep : ∀ j < m, ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
      (fun q : ℝ × M => spatialStep α (((j : ℝ) + 1) * c * q.1) (-(c * q.1)) q.2)
      (S ×ˢ univ)) :
    ∀ j ≤ m, ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
      (fun q : ℝ × M => reverseIter α c j q.1 q.2) (S ×ˢ univ) := by
  intro j
  induction j with
  | zero => intro _; exact contMDiff_snd.contMDiffOn
  | succ j ih =>
      intro hj
      exact (ih (Nat.le_of_succ_le hj)).comp
        (contMDiff_fst.contMDiffOn.prodMk (hstep j (Nat.lt_of_succ_le hj)))
        (fun q hq => ⟨hq.1, mem_univ _⟩)

theorem iterations_inverse {α : (M × ℝ) × ℝ → M × ℝ} {c t : ℝ} {m : ℕ}
    (hstep : ∀ j < m,
      Function.LeftInverse (spatialStep α (((j : ℝ) + 1) * c * t) (-(c * t)))
        (spatialStep α ((j : ℝ) * c * t) (c * t)) ∧
      Function.RightInverse (spatialStep α (((j : ℝ) + 1) * c * t) (-(c * t)))
        (spatialStep α ((j : ℝ) * c * t) (c * t))) :
    ∀ j ≤ m, Function.LeftInverse (reverseIter α c j t) (forwardIter α c j t) ∧
      Function.RightInverse (reverseIter α c j t) (forwardIter α c j t) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ j ih =>
      intro hj
      obtain ⟨hleft, hright⟩ := ih (Nat.le_of_succ_le hj)
      obtain ⟨hsleft, hsright⟩ := hstep j (Nat.lt_of_succ_le hj)
      constructor
      · intro x
        change reverseIter α c j t
          (spatialStep α (((j : ℝ) + 1) * c * t) (-(c * t))
            (spatialStep α ((j : ℝ) * c * t) (c * t) (forwardIter α c j t x))) = x
        rw [hsleft]
        exact hleft x
      · intro x
        change spatialStep α ((j : ℝ) * c * t) (c * t)
          (forwardIter α c j t (reverseIter α c j t
            (spatialStep α (((j : ℝ) + 1) * c * t) (-(c * t)) x))) = x
        rw [hright]
        exact hsright x

theorem subdivision_time_bounds {c t : ℝ} {m j : ℕ}
    (hc : 0 ≤ c) (hmc : (m : ℝ) * c = 1) (ht : 0 ≤ t) (hj : j ≤ m) :
    0 ≤ (j : ℝ) * c * t ∧ (j : ℝ) * c * t ≤ t := by
  refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg j) hc) ht, ?_⟩
  calc
    (j : ℝ) * c * t = (j : ℝ) * (c * t) := mul_assoc _ _ _
    _ ≤ (m : ℝ) * (c * t) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (mul_nonneg hc ht)
    _ = t := by rw [← mul_assoc, hmc, one_mul]

theorem forwardIter_eq
    (X Y : (q : M × ℝ) → TangentSpace I q.1)
    (hX : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) 1
      (fun q => (Bundle.TotalSpace.mk' E q.1 (X q) : TangentBundle I M)))
    {T ε η : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hTε : T ≤ ε) (hη : 0 < η)
    (hYX : ∀ q : M × ℝ, q.2 ∈ Ico 0 T → Y q = X q)
    {α β : (M × ℝ) × ℝ → M × ℝ}
    (hα0 : ∀ x : M, α ((x, 0), 0) = (x, 0))
    (hα : ∀ x : M,
      IsMIntegralCurveOn (fun s => α ((x, 0), s)) (suspension X) (Ioo (-ε) ε))
    {U : Set (M × ℝ)} (hK : ((univ : Set M) ×ˢ Icc (-1 : ℝ) 1) ⊆ U)
    (hβ0 : ∀ z ∈ U, β (z, 0) = z)
    (hβ : ∀ z ∈ U,
      IsMIntegralCurveOn (fun s => β (z, s)) (suspension Y) (Ioo (-η) η))
    {c : ℝ} {m : ℕ} (hc : 0 ≤ c) (hmc : (m : ℝ) * c = 1) (hcη : c < η / 2)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    ∀ j ≤ m, ∀ x : M, forwardIter β c j t x = spatialStep α 0 ((j : ℝ) * c * t) x := by
  have hε : 0 < ε := hT.trans_le hTε
  have hdt : c * t < η := by
    have hct : c * t ≤ c := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (ht.2.le.trans hT1) hc
    linarith
  intro j
  induction j with
  | zero =>
      intro _ x
      simpa only [forwardIter, spatialStep, Nat.cast_zero, zero_mul] using
        (congrArg Prod.fst (hα0 x)).symm
  | succ j ih =>
      intro hj x
      let a := (j : ℝ) * c * t
      let d := c * t
      have ha := subdivision_time_bounds hc hmc ht.1 (Nat.le_of_succ_le hj)
      have had := subdivision_time_bounds hc hmc ht.1 hj
      have haT : a < T := ha.2.trans_lt ht.2
      have hadT : a + d < T := by
        have h := had.2.trans_lt ht.2
        simpa only [a, d, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h
      have hcoord : α ((x, 0), a) = (spatialStep α 0 a x, a) := by
        apply Prod.ext
        · rfl
        simpa only [zero_add] using time_coordinate X hε (hα0 x) (hα x)
          (show a ∈ Ioo (-ε) ε from ⟨by linarith [ha.1], haT.trans_le hTε⟩)
      have hstart : α ((x, 0), a) ∈ U := by
        rw [hcoord]
        exact hK ⟨mem_univ _, ⟨by linarith [ha.1], ha.2.trans (ht.2.le.trans hT1)⟩⟩
      have hcmp := congrArg Prod.fst (local_step_compare X Y hX hT hTε hη hYX
        (hα0 x) (hα x) ha.1 (mul_nonneg hc ht.1) hadT hdt
        (hβ0 _ hstart) (hβ _ hstart))
      rw [hcoord] at hcmp
      change spatialStep β a d (forwardIter β c j t x) =
        spatialStep α 0 (((j + 1 : ℕ) : ℝ) * c * t) x
      rw [ih (Nat.le_of_succ_le hj) x]
      simpa only [a, d, spatialStep, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hcmp

theorem contMDiffOn_canonical_of_extension [CompactSpace M]
    (X Y : (q : M × ℝ) → TangentSpace I q.1)
    (hX : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) 1
      (fun q => (Bundle.TotalSpace.mk' E q.1 (X q) : TangentBundle I M)))
    {k : ℕ∞} (hk : k ≠ 0)
    (hY : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun q => (Bundle.TotalSpace.mk' E q.1 (Y q) : TangentBundle I M)))
    {T ε : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hTε : T ≤ ε / 2)
    (hYX : ∀ q : M × ℝ, q.2 ∈ Ico 0 T → Y q = X q)
    {U : Set (M × ℝ)} (hK : ((univ : Set M) ×ˢ Icc (-1 : ℝ) 1) ⊆ U)
    {α : (M × ℝ) × ℝ → M × ℝ}
    (hα0 : ∀ z ∈ U, α (z, 0) = z)
    (hα : ∀ z ∈ U,
      IsMIntegralCurveOn (fun s => α (z, s)) (suspension X) (Ioo (-ε) ε)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
      (fun q : ℝ × M => spatialStep α 0 q.1 q.2) (Ico 0 T ×ˢ univ) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
      (fun q : ℝ × M => spatialStep α q.1 (-q.1) q.2) (Ico 0 T ×ˢ univ) := by
  obtain ⟨A, _, hKA, η, hη, β, hβ0, hβ, hβsm⟩ :=
    exists_contDiff_suspended_local_flow hk Y hY
  obtain ⟨l, hl⟩ := exists_nat_one_div_lt (half_pos hη)
  let m : ℕ := l + 1
  let c : ℝ := (m : ℝ)⁻¹
  have hm : 0 < (m : ℝ) := by dsimp [m]; positivity
  have hc : 0 ≤ c := (inv_pos.mpr hm).le
  have hmc : (m : ℝ) * c = 1 := mul_inv_cancel₀ (ne_of_gt hm)
  have hcη : c < η / 2 := by
    simpa only [c, m, Nat.cast_add, Nat.cast_one, one_div] using hl
  have hε : 0 < ε := by linarith
  have hY1 : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) 1
      (fun q => (Bundle.TotalSpace.mk' E q.1 (Y q) : TangentBundle I M)) :=
    hY.of_le (by exact_mod_cast (Order.one_le_iff_ne_zero.mpr hk : (1 : ℕ∞) ≤ k))
  have hanchor {t : ℝ} (ht : t ∈ Ico 0 T) {j : ℕ} (hj : j ≤ m) :
      (j : ℝ) * c * t ∈ Icc (-1 : ℝ) 1 := by
    have h := subdivision_time_bounds hc hmc ht.1 hj
    exact ⟨by linarith [h.1], h.2.trans (ht.2.le.trans hT1)⟩
  have hsmall {t : ℝ} (ht : t ∈ Ico 0 T) :
      c * t ∈ Ioo (-(η / 2)) (η / 2) := by
    have hct : c * t ≤ c := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (ht.2.le.trans hT1) hc
    exact ⟨by linarith [mul_nonneg hc ht.1], hct.trans_lt hcη⟩
  have hfull : Ioo (-(η / 2)) (η / 2) ⊆ Ioo (-η) η :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  have hfstep (j : ℕ) (hj : j < m) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
        (fun q : ℝ × M => spatialStep β ((j : ℝ) * c * q.1) (c * q.1) q.2)
        (Ico 0 T ×ˢ univ) :=
    contMDiffOn_spatialStep hβsm ((j : ℝ) * c) c
      (fun t ht x => hKA ⟨mem_univ _, hanchor ht hj.le⟩)
      (fun _ ht => hfull (hsmall ht))
  have hrstep (j : ℕ) (hj : j < m) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
        (fun q : ℝ × M => spatialStep β (((j : ℝ) + 1) * c * q.1) (-(c * q.1)) q.2)
        (Ico 0 T ×ˢ univ) := by
    have h := contMDiffOn_spatialStep hβsm (((j : ℝ) + 1) * c) (-c)
      (S := Ico 0 T) (fun t ht x => hKA ⟨mem_univ _, by
        simpa only [Nat.cast_succ] using hanchor ht (Nat.succ_le_of_lt hj)⟩)
      (fun t ht => by
        have hs := hfull (hsmall ht)
        rw [neg_mul]
        exact ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    simpa only [neg_mul] using h
  have hfinv {t : ℝ} (ht : t ∈ Ico 0 T) :
      Function.LeftInverse (reverseIter β c m t) (forwardIter β c m t) ∧
      Function.RightInverse (reverseIter β c m t) (forwardIter β c m t) := by
    apply iterations_inverse (m := m) ?_ m le_rfl
    intro j hj
    have had : (j : ℝ) * c * t + c * t ∈ Icc (-1 : ℝ) 1 := by
      simpa only [Nat.cast_succ, add_mul, one_mul] using
        hanchor ht (Nat.succ_le_of_lt hj)
    simpa only [add_mul, one_mul] using
      spatialStep_inverse Y hY1 hKA hη hβ0 hβ (hanchor ht hj.le) had (hsmall ht)
  have hstart (x : M) : (x, (0 : ℝ)) ∈ U :=
    hK ⟨mem_univ _, ⟨by norm_num, by norm_num⟩⟩
  have heq {t : ℝ} (ht : t ∈ Ico 0 T) (x : M) :
      forwardIter β c m t x = spatialStep α 0 t x := by
    simpa only [hmc, one_mul] using forwardIter_eq X Y hX hT hT1 (by linarith) hη hYX
      (fun x => hα0 _ (hstart x)) (fun x => hα _ (hstart x)) hKA hβ0 hβ
      hc hmc hcη ht m le_rfl x
  have hrev {t : ℝ} (ht : t ∈ Ico 0 T) :
      reverseIter β c m t = spatialStep α t (-t) := by
    have hcan := spatialStep_inverse X hX hK hε hα0 hα
      (a := 0) (d := t) ⟨by norm_num, by norm_num⟩
      (by simpa only [zero_add] using
        (show t ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [ht.1], ht.2.le.trans hT1⟩))
      ⟨by linarith [ht.1], ht.2.trans_le hTε⟩
    have hleft : Function.LeftInverse (reverseIter β c m t) (spatialStep α 0 t) := by
      intro x
      rw [← heq ht x]
      exact (hfinv ht).1 x
    exact hleft.eq_rightInverse (by simpa only [zero_add] using hcan.2)
  refine ⟨(contMDiffOn_forwardIter hfstep m le_rfl).congr ?_,
    (contMDiffOn_reverseIter hrstep m le_rfl).congr ?_⟩
  · intro q hq
    exact (heq hq.1 q.2).symm
  · intro q hq
    exact congrFun (hrev hq.1).symm q.2

theorem exists_diffeomorph_family_of_finite_extensions [CompactSpace M]
    (X : (q : M × ℝ) → TangentSpace I q.1) {S : ℝ} (hS : 0 < S)
    (hext : ∀ k : ℕ, ∃ Y : (q : M × ℝ) → TangentSpace I q.1,
      ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) (k + 1 : ℕ)
        (fun q => (Bundle.TotalSpace.mk' E q.1 (Y q) : TangentBundle I M)) ∧
      ∀ q : M × ℝ, q.2 ∈ Ico 0 S → Y q = X q) :
    ∃ T > 0, T ≤ S ∧ ∃ Phi : ℝ → Diffeomorph I I M M ∞,
      Phi 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => Phi q.1 q.2) (Ico 0 T ×ˢ univ) ∧
      ∀ t ∈ Ico 0 T, ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => Phi s x) (Ico 0 T) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X (Phi t x, t))) := by
  classical
  obtain ⟨Y, hY, hYX⟩ := hext 0
  have hY1 : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) 1
      (fun q => (Bundle.TotalSpace.mk' E q.1 (Y q) : TangentBundle I M)) := by
    simpa only [Nat.zero_add, Nat.cast_one] using hY
  obtain ⟨U, _, hK, ε, hε, α, hα0, hα, _⟩ :=
    exists_contDiff_suspended_local_flow (k := 1) (by simp) Y hY1
  let T := min S (min 1 (ε / 2))
  have hT : 0 < T := lt_min hS (lt_min zero_lt_one (half_pos hε))
  have hTS : T ≤ S := min_le_left _ _
  have hT1 : T ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hTε : T ≤ ε / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : Ico (0 : ℝ) T ⊆ Ico 0 S := Ico_subset_Ico_right hTS
  have hall (k : ℕ) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
        (fun q : ℝ × M => spatialStep α 0 q.1 q.2) (Ico 0 T ×ˢ univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I k
        (fun q : ℝ × M => spatialStep α q.1 (-q.1) q.2) (Ico 0 T ×ˢ univ) := by
    obtain ⟨Z, hZ, hZX⟩ := hext k
    have hZY : ∀ q : M × ℝ, q.2 ∈ Ico 0 T → Z q = Y q :=
      fun q hq => (hZX q (hsub hq)).trans (hYX q (hsub hq)).symm
    have h := contMDiffOn_canonical_of_extension Y Z hY1
      (k := (k + 1 : ℕ)) (by simp) hZ hT hT1 hTε hZY hK hα0 hα
    exact ⟨h.1.of_le (by exact_mod_cast Nat.le_succ k),
      h.2.of_le (by exact_mod_cast Nat.le_succ k)⟩
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => spatialStep α 0 q.1 q.2) (Ico 0 T ×ˢ univ) :=
    contMDiffOn_infty.mpr (fun k => (hall k).1)
  have hr : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => spatialStep α q.1 (-q.1) q.2) (Ico 0 T ×ˢ univ) :=
    contMDiffOn_infty.mpr (fun k => (hall k).2)
  have hinv {t : ℝ} (ht : t ∈ Ico 0 T) :
      Function.LeftInverse (spatialStep α t (-t)) (spatialStep α 0 t) ∧
      Function.RightInverse (spatialStep α t (-t)) (spatialStep α 0 t) := by
    simpa only [zero_add] using spatialStep_inverse Y hY1 hK hε hα0 hα
      (a := 0) (d := t) ⟨by norm_num, by norm_num⟩
      (by simpa only [zero_add] using
        (show t ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [ht.1], ht.2.le.trans hT1⟩))
      ⟨by linarith [ht.1], ht.2.trans_le hTε⟩
  have hfixed {F : ℝ → M → M}
      (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => F q.1 q.2) (Ico 0 T ×ˢ univ))
      {t : ℝ} (ht : t ∈ Ico 0 T) : ContMDiff I I ∞ (F t) := by
    rw [← contMDiffOn_univ]
    exact hF.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩)
  let F (t : ℝ) (ht : t ∈ Ico 0 T) : Diffeomorph I I M M ∞ :=
    { toEquiv :=
        { toFun := spatialStep α 0 t
          invFun := spatialStep α t (-t)
          left_inv := (hinv ht).1
          right_inv := (hinv ht).2 }
      contMDiff_toFun := hfixed hf ht
      contMDiff_invFun := by
        change ContMDiff I I ∞ (spatialStep α t (-t))
        exact hfixed (F := fun s x => spatialStep α s (-s) x) hr ht }
  let Phi : ℝ → Diffeomorph I I M M ∞ := fun t =>
    if ht : t ∈ Ico 0 T then F t ht else Diffeomorph.refl I M ∞
  have hPhi (t : ℝ) (ht : t ∈ Ico 0 T) (x : M) : Phi t x = spatialStep α 0 t x := by
    simp only [Phi, dif_pos ht]
    rfl
  have hstart (x : M) : (x, (0 : ℝ)) ∈ U :=
    hK ⟨mem_univ _, ⟨by norm_num, by norm_num⟩⟩
  refine ⟨T, hT, hTS, Phi, ?_, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    rw [hPhi 0 ⟨le_rfl, hT⟩ x]
    exact congrArg Prod.fst (hα0 _ (hstart x))
  · exact hf.congr (fun q hq => hPhi q.1 hq.1 q.2)
  · intro t ht x
    have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hcoord : α ((x, 0), t) = (spatialStep α 0 t x, t) := by
      apply Prod.ext
      · rfl
      simpa only [zero_add] using time_coordinate Y hε
        (hα0 _ (hstart x)) (hα _ (hstart x)) htε
    have hder := spatial_derivative Y (hα _ (hstart x)) htε
    rw [hcoord] at hder
    have hfield : Y (spatialStep α 0 t x, t) = X (spatialStep α 0 t x, t) :=
      hYX _ (hsub ht)
    rw [hfield, ← hPhi t ht x] at hder
    exact hder.hasMFDerivWithinAt.congr_mono
      (fun s hs => hPhi s hs x) (hPhi t ht x) (Subset.refl _)

end PoincareConjecture.FiniteOrderConjugatingFlowNative

end
