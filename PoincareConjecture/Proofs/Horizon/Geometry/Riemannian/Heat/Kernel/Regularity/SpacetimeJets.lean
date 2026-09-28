import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.RowJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.CoordinateKernel
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LinearPrecompose

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace

namespace Poincare.Analysis.Calculus

theorem norm_iteratedFDeriv_comp_continuousLinearMap_le_of_contDiffAt
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) {f : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f (L x)) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (f ∘ L) x‖ ≤
      ‖iteratedFDeriv ℝ m f (L x)‖ * ‖L‖ ^ m := by
  rw [iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L hf]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ m f (L x)).norm_compContinuousLinearMap_le (fun _ : Fin m => L)

theorem norm_iteratedFDeriv_clm_apply_le_of_contDiffAt
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F →L[ℝ] G} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y (g y)) x‖ ≤
      ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (m - l) g x‖ := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (inter_mem hs ht)
  have h := norm_iteratedFDerivWithin_clm_apply
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (m : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using h

theorem norm_iteratedFDeriv_inner_le_of_contDiffAt
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : E → H} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => inner ℝ (f y) (g y)) x‖ ≤
      ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (m - l) g x‖ := by
  have h := norm_iteratedFDeriv_bilinear_le_of_contDiffAt (innerSL ℝ) hf hg m
  exact h.trans (mul_le_of_le_one_left
    (Finset.sum_nonneg fun _ _ => by positivity) (norm_innerSL_le (𝕜 := ℝ)))

end Poincare.Analysis.Calculus

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary Poincare.Analysis.Dirichlet.Kernel Poincare.Analysis.Calculus

variable {n d : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin d)

theorem exists_coordinateHeatKernel_jet_bound
    (D : LeviCivitaData g) (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (hei₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁.symm e₁.target)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source)
    (hei₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂.symm e₂.target)
    {V₁ V₂ : Set E} (hV₁ : IsOpen V₁) (hc₁ : IsCompact (closure V₁))
    (hs₁ : closure V₁ ⊆ e₁.source)
    (hV₂ : IsOpen V₂) (hc₂ : IsCompact (closure V₂)) (hs₂ : closure V₂ ⊆ e₂.source)
    {K : Set F} (hK : IsCompact K) (hX : X '' K ⊆ V₁) (hY : Y '' K ⊆ V₂)
    {a : ℝ} (ha : 0 < a) (hT : ∀ z ∈ K, 3 * a ≤ T z) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω),
      e₁ '' V₁ ⊆ Ω → e₂ '' V₂ ⊆ Ω → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (coordinateHeatKernel D S T X Y e₁ e₂) z‖ ≤ C := by
  obtain ⟨A, hA, hAb⟩ := exists_evaluationRow_coordinate_jets_bound
    D e₁ he₁ hei₁ hV₁ hc₁ hs₁ (hK.image X.continuous) hX 0 m ha
  obtain ⟨B, hB, hBb⟩ := exists_evaluationRow_coordinate_jets_bound
    D e₂ he₂ hei₂ hV₂ hc₂ hs₂ (hK.image Y.continuous) hY 0 m ha
  let Q (j : ℕ) : ℝ := ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
    ((l.factorial / a ^ l) * ‖T‖ ^ l) * (B * ‖Y‖ ^ (j - l))
  let C : ℝ := ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) *
    (A * ‖X‖ ^ l) * Q (m - l)
  have hQ (j : ℕ) : 0 ≤ Q j := Finset.sum_nonneg (fun _ _ => by positivity)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨C + 1, by positivity, ?_⟩
  intro Ω S hΩ₁ hΩ₂ z hz
  let H := Lp ℝ 2 (g.volumeMeasure.restrict Ω)
  let R₁ : E → H := fun w => evaluationRow (heatPowerContinuous D S 0 a ha) (e₁ w)
  let R₂ : E → H := fun w => evaluationRow (heatPowerContinuous D S 0 a ha) (e₂ w)
  let P : ℝ → H →L[ℝ] H := heatSpectralPower D Ω
    (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure 0
  have hxV := hX (mem_image_of_mem X hz)
  have hyV := hY (mem_image_of_mem Y hz)
  have hxs := hs₁ (subset_closure hxV)
  have hys := hs₂ (subset_closure hyV)
  have hxΩ := hΩ₁ (mem_image_of_mem e₁ hxV)
  have hyΩ := hΩ₂ (mem_image_of_mem e₂ hyV)
  have hRx : ContDiffAt ℝ ∞ R₁ (X z) := contMDiffAt_iff_contDiffAt.mp
    (((contMDiffOn_evaluationRow_heatPowerContinuous D S 0 a ha).contMDiffAt
      (S.isOpen.mem_nhds hxΩ)).comp (X z) (he₁.contMDiffAt (e₁.open_source.mem_nhds hxs)))
  have hRy : ContDiffAt ℝ ∞ R₂ (Y z) := contMDiffAt_iff_contDiffAt.mp
    (((contMDiffOn_evaluationRow_heatPowerContinuous D S 0 a ha).contMDiffAt
      (S.isOpen.mem_nhds hyΩ)).comp (Y z) (he₂.contMDiffAt (e₂.open_source.mem_nhds hys)))
  have ht : a ≤ T z - 2 * a := by linarith [hT z hz]
  have hPt : ContDiffAt ℝ ∞ P (T z - 2 * a) :=
    (contDiffOn_heatSpectralPower_operator D S 0).contDiffAt
      (isOpen_Ioi.mem_nhds (ha.trans_le ht))
  have hPs : ContDiffAt ℝ ∞ (fun t => P (t - 2 * a)) (T z) :=
    hPt.comp (T z) (contDiffAt_id.sub contDiffAt_const)
  have hPc : ContDiffAt ℝ ∞ (fun w => P (T w - 2 * a)) z :=
    hPs.comp z T.contDiff.contDiffAt
  have hRxc := hRx.comp z X.contDiff.contDiffAt
  have hRyc := hRy.comp z Y.contDiff.contDiffAt
  have hxb (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (R₁ ∘ X) z‖ ≤ A * ‖X‖ ^ j :=
    (norm_iteratedFDeriv_comp_continuousLinearMap_le_of_contDiffAt X hRx j).trans
      (mul_le_mul_of_nonneg_right
        (hAb S hΩ₁ le_rfl j hj (X z) (mem_image_of_mem X hz)) (by positivity))
  have hyb (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (R₂ ∘ Y) z‖ ≤ B * ‖Y‖ ^ j :=
    (norm_iteratedFDeriv_comp_continuousLinearMap_le_of_contDiffAt Y hRy j).trans
      (mul_le_mul_of_nonneg_right
        (hBb S hΩ₂ le_rfl j hj (Y z) (mem_image_of_mem Y hz)) (by positivity))
  have hpb (j : ℕ) :
      ‖iteratedFDeriv ℝ j (fun w => P (T w - 2 * a)) z‖ ≤
        (j.factorial / a ^ j) * ‖T‖ ^ j := by
    have hh := norm_iteratedFDeriv_comp_continuousLinearMap_le_of_contDiffAt T hPs j
    rw [iteratedFDeriv_comp_sub] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa only [Nat.zero_add] using norm_iteratedFDeriv_heatSpectralPower_operator_le D S j 0 ha ht
  have hqb (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (fun w => P (T w - 2 * a) (R₂ (Y w))) z‖ ≤ Q j := by
    apply (norm_iteratedFDeriv_clm_apply_le_of_contDiffAt hPc hRyc j).trans
    apply Finset.sum_le_sum
    intro l hl
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hpb l) (by positivity))
      (hyb (j - l) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (by positivity)
  have heq : coordinateHeatKernel D S T X Y e₁ e₂ =ᶠ[𝓝 z]
      (fun w => inner ℝ (R₁ (X w)) (P (T w - 2 * a) (R₂ (Y w)))) := by
    have htz : 2 * a < T z := by linarith [hT z hz]
    filter_upwards [(isOpen_lt continuous_const T.continuous).mem_nhds htz] with w hw
    exact heatKernelContinuousTime_eq_fixed_spectral_rows D S ha hw _ _
  rw [(heq.iteratedFDeriv ℝ m).self_of_nhds]
  apply le_trans _ (le_add_of_nonneg_right zero_le_one : C ≤ C + 1)
  apply (norm_iteratedFDeriv_inner_le_of_contDiffAt hRxc (hPc.clm_apply hRyc) m).trans
  apply Finset.sum_le_sum
  intro l hl
  exact mul_le_mul (mul_le_mul_of_nonneg_left
    (hxb l (Nat.le_of_lt_succ (Finset.mem_range.mp hl))) (by positivity))
    (hqb (m - l) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)

theorem locallyEventuallyBoundedDerivatives_coordinateHeatKernel
    (D : LeviCivitaData g) (_hc : MetricComplete g) {k : ℝ} (_hk : 0 ≤ k)
    (_hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (T : F →L[ℝ] ℝ) (X Y : F →L[ℝ] E)
    (e₁ e₂ : OpenPartialHomeomorph E M)
    (he₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁ e₁.source)
    (hei₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₁.symm e₁.target)
    (he₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂ e₂.source)
    (hei₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e₂.symm e₂.target) :
    LocallyEventuallyBoundedDerivatives
      (coordinateKernelDomain T X Y e₁ e₂)
      (fun q => coordinateHeatKernel D (S q) T X Y e₁ e₂) := by
  intro K hK hKD m
  by_cases hne : K.Nonempty
  · have hKdom : K ⊆ coordinateKernelDomain T X Y e₁ e₂ := hKD
    have hKX : X '' K ⊆ e₁.source := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hKdom hz).2.1
    have hKY : Y '' K ⊆ e₂.source := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hKdom hz).2.2
    obtain ⟨W₁, hW₁, hIW₁, hW₁c⟩ :=
      exists_isOpen_superset_and_isCompact_closure (hK.image X.continuous)
    obtain ⟨V₁, hV₁, hXV₁, hV₁s⟩ :=
      (hK.image X.continuous).exists_isOpen_closure_subset
        ((e₁.open_source.inter hW₁).mem_nhdsSet.mpr
          (fun x hx => ⟨hKX hx, hIW₁ hx⟩))
    obtain ⟨W₂, hW₂, hIW₂, hW₂c⟩ :=
      exists_isOpen_superset_and_isCompact_closure (hK.image Y.continuous)
    obtain ⟨V₂, hV₂, hYV₂, hV₂s⟩ :=
      (hK.image Y.continuous).exists_isOpen_closure_subset
        ((e₂.open_source.inter hW₂).mem_nhdsSet.mpr
          (fun x hx => ⟨hKY hx, hIW₂ hx⟩))
    have hc₁ : IsCompact (closure V₁) :=
      hW₁c.of_isClosed_subset isClosed_closure
        (fun x hx => subset_closure (hV₁s hx).2)
    have hc₂ : IsCompact (closure V₂) :=
      hW₂c.of_isClosed_subset isClosed_closure
        (fun x hx => subset_closure (hV₂s hx).2)
    have hTcont : ContinuousOn T K := T.continuous.continuousOn
    obtain ⟨z₀, hz₀, hzmin⟩ := hK.exists_isMinOn hne hTcont
    have hmin : 0 < T z₀ := (hKdom hz₀).1
    let a : ℝ := T z₀ / 3
    have ha : 0 < a := by dsimp [a]; positivity
    have hTa : ∀ z ∈ K, 3 * a ≤ T z := by
      intro z hz
      rw [show 3 * a = T z₀ by dsimp [a]; ring]
      exact hzmin hz
    obtain ⟨C, _hC, hbound⟩ := exists_coordinateHeatKernel_jet_bound
      D T X Y e₁ e₂ he₁ hei₁ he₂ hei₂ hV₁ hc₁
        (fun x hx => (hV₁s hx).1) hV₂ hc₂ (fun x hx => (hV₂s hx).1)
      hK hXV₁ hYV₂ ha hTa m
    obtain ⟨q₁, hq₁⟩ := ((hc₁.image_of_continuousOn
      (e₁.continuousOn.mono fun z hz => (hV₁s hz).1))).elim_directed_cover
      Ω (fun q => (S q).isOpen) (by rw [hcover]; exact subset_univ _)
      hΩmono.directed_le
    obtain ⟨q₂, hq₂⟩ := ((hc₂.image_of_continuousOn
      (e₂.continuousOn.mono fun z hz => (hV₂s hz).1))).elim_directed_cover
      Ω (fun q => (S q).isOpen) (by rw [hcover]; exact subset_univ _)
      hΩmono.directed_le
    refine ⟨C + 1, ?_⟩
    filter_upwards [eventually_ge_atTop (max q₁ q₂)] with q hq z hz
    have hq₁' : q₁ ≤ q := (le_max_left _ _).trans hq
    have hq₂' : q₂ ≤ q := (le_max_right _ _).trans hq
    have hΩ₁ : e₁ '' V₁ ⊆ Ω q :=
      (image_mono subset_closure).trans (hq₁.trans (hΩmono hq₁'))
    have hΩ₂ : e₂ '' V₂ ⊆ Ω q :=
      (image_mono subset_closure).trans (hq₂.trans (hΩmono hq₂'))
    exact (hbound (S q) hΩ₁ hΩ₂ z hz).trans (le_add_of_nonneg_right zero_le_one)
  · refine ⟨0, Eventually.of_forall ?_⟩
    intro q x hx
    exact (False.elim (hne ⟨x, hx⟩))

end PoincareConjecture.LeviCivitaData.Dirichlet
