import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Density

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal ContDiff

namespace Poincare.Analysis.Sobolev.Euclidean
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma euclidean_coord_le_norm
    (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |v i| ≤ ‖v‖ := by
  classical
  have h_sq : (v i)^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h_le := Finset.single_le_sum
      (f := fun j : Fin d => (v j)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    convert h_le
  have hv_norm_nn : 0 ≤ ‖v‖ := norm_nonneg _
  have h_abs_sq : |v i|^2 = (v i)^2 := sq_abs _
  rw [show |v i| = Real.sqrt ((v i)^2) from (Real.sqrt_sq_eq_abs _).symm]
  rw [show ‖v‖ = Real.sqrt (‖v‖^2) from (Real.sqrt_sq hv_norm_nn).symm]
  exact Real.sqrt_le_sqrt h_sq

omit [NeZero d] in
private lemma continuousMultilinearMap_norm_le_sum_basis
    {n : ℕ}
    (f : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) ℝ) :
    ‖f‖ ≤ ∑ β : Fin n → Fin d,
      |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| := by
  classical
  set M : ℝ := ∑ β : Fin n → Fin d,
      |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| with hM_def
  have hM_nonneg : 0 ≤ M :=
    Finset.sum_nonneg (fun β _ => abs_nonneg _)
  refine ContinuousMultilinearMap.opNorm_le_bound hM_nonneg ?_
  intro m
  have h_expand : ∀ i : Fin n, m i =
      ∑ α : Fin d, (m i α) • EuclideanSpace.single α (1 : ℝ) := by
    intro i
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (m i)
    rw [show (fun α : Fin d => (m i α) • EuclideanSpace.single α (1 : ℝ)) =
      (fun α : Fin d => (EuclideanSpace.basisFun (Fin d) ℝ).repr (m i) α •
        (EuclideanSpace.basisFun (Fin d) ℝ) α) from ?_, h]
    funext α
    rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have h_f_expand :
      f m = ∑ β : Fin n → Fin d,
        (∏ i : Fin n, m i (β i)) *
          f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) := by
    have h_step1 : f m = f (fun i : Fin n =>
        ∑ α : Fin d, (m i α) • EuclideanSpace.single α (1 : ℝ)) := by
      congr; funext i; exact h_expand i
    rw [h_step1]
    have h_mult_sum :
        (f.toMultilinearMap fun i : Fin n =>
          ∑ α : Fin d, (m i α) • EuclideanSpace.single α (1 : ℝ)) =
        ∑ β : Fin n → Fin d,
          f.toMultilinearMap fun i : Fin n =>
            (m i (β i)) • EuclideanSpace.single (β i) (1 : ℝ) := by
      exact f.toMultilinearMap.map_sum
        (fun (i : Fin n) (α : Fin d) =>
          (m i α) • EuclideanSpace.single α (1 : ℝ))
    change f.toMultilinearMap _ = _
    rw [h_mult_sum]
    refine Finset.sum_congr rfl ?_
    intro β _
    rw [f.toMultilinearMap.map_smul_univ
      (c := fun i : Fin n => m i (β i))
      (m := fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))]
    rw [smul_eq_mul]
    rfl
  rw [Real.norm_eq_abs]
  rw [h_f_expand]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h_inner_bound : ∀ β : Fin n → Fin d,
      |(∏ i : Fin n, m i (β i)) *
          f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| ≤
        (∏ i : Fin n, ‖m i‖) *
          |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| := by
    intro β
    rw [abs_mul]
    have h_prod_le : |∏ i : Fin n, m i (β i)| ≤ ∏ i : Fin n, ‖m i‖ := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod ?_ ?_
      · intro i _; exact abs_nonneg _
      · intro i _; exact euclidean_coord_le_norm (d := d) (m i) (β i)
    exact mul_le_mul_of_nonneg_right h_prod_le (abs_nonneg _)
  refine (Finset.sum_le_sum (fun β _ => h_inner_bound β)).trans ?_
  have h_factor :
      ∑ β : Fin n → Fin d,
        (∏ i : Fin n, ‖m i‖) *
          |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| =
      (∏ i : Fin n, ‖m i‖) * M := by
    rw [← Finset.mul_sum]
  rw [h_factor]
  exact le_of_eq (mul_comm _ _)

omit [NeZero d] in
private lemma norm_iteratedFDeriv_le_sum_basis
    (n : ℕ) {ψ : E → ℝ} (y : E) :
    ‖iteratedFDeriv ℝ n ψ y‖ ≤
      ∑ β : Fin n → Fin d,
        |iteratedFDeriv ℝ n ψ y
          (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| :=
  continuousMultilinearMap_norm_le_sum_basis (d := d) (iteratedFDeriv ℝ n ψ y)

omit [NeZero d] in
private lemma iteratedFDeriv_clm_apply_basis
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F →L[ℝ] ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : F)
    (β : Fin n → Fin d) (y : E) :
    iteratedFDeriv ℝ n g y
      (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) v =
    iteratedFDeriv ℝ n (fun y' => g y' v) y
      (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) := by
  have h := iteratedFDeriv_clm_apply_const_apply (𝕜 := ℝ)
    (n := (⊤ : ℕ∞)) (c := g) (u := v) (i := n) (x := y)
    (m := fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))
    hg (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  exact h.symm

omit [NeZero d] in
private lemma iteratedFDeriv_basis_eq_iterClassicalPartial_rev :
    ∀ (n : ℕ) (β : Fin n → Fin d) {f : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) f → ∀ y : E,
        iteratedFDeriv ℝ n f y
          (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) =
        iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y := by
  intro n
  induction n with
  | zero =>
      intro β f _ y
      simp [iteratedFDeriv_zero_apply, iterClassicalPartial_zero]
  | succ n ih =>
      intro β f hf y
      rw [show (fun i : Fin (n + 1) => EuclideanSpace.single (β i) (1 : ℝ)) =
        Fin.snoc (fun i : Fin n => EuclideanSpace.single (β i.castSucc) (1 : ℝ))
          (EuclideanSpace.single (β (Fin.last n)) (1 : ℝ)) by
        ext i
        induction i using Fin.lastCases with
        | last => simp
        | cast j => simp]
      rw [iteratedFDeriv_succ_apply_right]
      rw [Fin.init_snoc, Fin.snoc_last]
      have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by
        have hf_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by simpa using hf
        have h := hf_top.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        simpa using h
      rw [iteratedFDeriv_clm_apply_basis (d := d)
        (g := fderiv ℝ f) hfd (EuclideanSpace.single (β (Fin.last n)) (1 : ℝ))
        (β := fun i : Fin n => β i.castSucc) y]
      have h_inner_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun y' : E => (fderiv ℝ f y') (EuclideanSpace.single (β (Fin.last n)) (1 : ℝ))) :=
        hfd.clm_apply contDiff_const
      rw [ih (fun i : Fin n => β i.castSucc) h_inner_smooth y]
      rw [iterClassicalPartial_succ]
      have h_index_eq :
          (fun i : Fin n => β i.rev.castSucc) =
          (fun i : Fin n => β i.succ.rev) := by
        funext i
        rw [Fin.rev_succ]
      have h_first_eq : β (Fin.last n) = β (Fin.rev 0) := by
        rw [Fin.rev_zero]
      rw [h_index_eq, h_first_eq]

omit [NeZero d] in
private lemma norm_iteratedFDeriv_le_sum_iterClassicalPartial
    (n : ℕ) {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : E) :
    ‖iteratedFDeriv ℝ n f y‖ ≤
      ∑ β : Fin n → Fin d, |iterClassicalPartial (d := d) n β f y| := by
  classical
  have h1 := norm_iteratedFDeriv_le_sum_basis (d := d) n (ψ := f) y
  have h2 : ∀ β : Fin n → Fin d,
      |iteratedFDeriv ℝ n f y
        (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| =
      |iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y| := by
    intro β
    rw [iteratedFDeriv_basis_eq_iterClassicalPartial_rev (d := d) n β hf y]
  have h3 : ∑ β : Fin n → Fin d,
      |iteratedFDeriv ℝ n f y
        (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| =
      ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y| :=
    Finset.sum_congr rfl (fun β _ => h2 β)
  rw [h3] at h1
  have h_equiv :
      ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y| =
      ∑ β : Fin n → Fin d, |iterClassicalPartial (d := d) n β f y| := by
    have h_invol : ∀ β : Fin n → Fin d,
        (fun i : Fin n => (fun j : Fin n => β j.rev) i.rev) = β := by
      intro β
      funext i
      simp [Fin.rev_rev]
    refine Finset.sum_bij (fun β _ => fun i : Fin n => β i.rev) ?_ ?_ ?_ ?_
    · intro β _; exact Finset.mem_univ _
    · intro β1 _ β2 _ h
      have h_apply : ∀ i : Fin n,
          (fun j : Fin n => β1 j.rev) i = (fun j : Fin n => β2 j.rev) i :=
        fun i => congrFun h i
      funext i
      have := h_apply i.rev
      simpa [Fin.rev_rev] using this
    · intro β _
      refine ⟨fun i : Fin n => β i.rev, Finset.mem_univ _, ?_⟩
      funext i
      simp [Fin.rev_rev]
    · intro β _; rfl
  rw [h_equiv] at h1
  exact h1

omit [NeZero d] in
private lemma eLpNorm_iteratedFDeriv_le_sum_iterClassicalPartial
    (n : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : E → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (Ω : Set E) :
    eLpNorm (fun y => ‖iteratedFDeriv ℝ n f y‖) p (volume.restrict Ω) ≤
      ∑ β : Fin n → Fin d,
        eLpNorm (iterClassicalPartial (d := d) n β f) p (volume.restrict Ω) := by
  classical
  have h_pt : ∀ y, ‖iteratedFDeriv ℝ n f y‖ ≤
      ∑ β : Fin n → Fin d, |iterClassicalPartial (d := d) n β f y| :=
    fun y => norm_iteratedFDeriv_le_sum_iterClassicalPartial (d := d) n hf_smooth y
  have h_eLp_le :
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n f y‖) p (volume.restrict Ω) ≤
      eLpNorm (fun y => ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n β f y|) p (volume.restrict Ω) := by
    refine eLpNorm_mono_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg]
    · exact h_pt y
    · exact Finset.sum_nonneg (fun β _ => abs_nonneg _)
  refine h_eLp_le.trans ?_
  have h_strong_meas : ∀ β : Fin n → Fin d,
      AEStronglyMeasurable
        (fun y => |iterClassicalPartial (d := d) n β f y|) (volume.restrict Ω) := by
    intro β
    have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (iterClassicalPartial (d := d) n β f) :=
      contDiff_iterClassicalPartial (d := d) n β hf_smooth
    have h_aem : AEStronglyMeasurable
        (iterClassicalPartial (d := d) n β f) (volume.restrict Ω) :=
      h_smooth.continuous.aestronglyMeasurable
    have h_norm := h_aem.norm
    refine h_norm.congr (Filter.Eventually.of_forall ?_)
    intro y
    exact (Real.norm_eq_abs _).symm
  have h_triangle :
      eLpNorm (fun y => ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n β f y|) p (volume.restrict Ω) ≤
      ∑ β : Fin n → Fin d,
        eLpNorm (fun y => |iterClassicalPartial (d := d) n β f y|) p (volume.restrict Ω) := by
    have hsum := eLpNorm_sum_le
      (μ := volume.restrict Ω) (p := p)
      (s := (Finset.univ : Finset (Fin n → Fin d)))
      (f := fun β y => |iterClassicalPartial (d := d) n β f y|)
      (fun β _ => h_strong_meas β) hp
    have h_eq : (fun y => ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n β f y|) =
        ((Finset.univ : Finset (Fin n → Fin d)).sum
          (fun β => fun y => |iterClassicalPartial (d := d) n β f y|)) := by
      funext y; rw [Finset.sum_apply]
    rw [h_eq]
    exact hsum
  refine h_triangle.trans ?_
  refine Finset.sum_le_sum (fun β _ => ?_)
  refine eLpNorm_mono_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  rw [Real.norm_eq_abs, abs_abs]
  exact le_of_eq rfl

omit [NeZero d] in
lemma eLpNorm_iteratedFDeriv_le_wkpNorm
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    (k : ℕ)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ) (hψ_supp : tsupport ψ ⊆ Ω) :
    ∑ n ∈ Finset.range (k + 1),
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p (volume.restrict Ω) ≤
    iteratedWeakSobolevNorm (d := d) k p ψ Ω := by
  classical
  have h_per_n : ∀ n, n ≤ k →
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p (volume.restrict Ω) ≤
      ∑ β : Fin n → Fin d,
        eLpNorm (iterClassicalPartial (d := d) n β ψ) p (volume.restrict Ω) := fun n _ =>
    eLpNorm_iteratedFDeriv_le_sum_iterClassicalPartial (d := d) n hp_one
      hψ_smooth Ω
  have h_iter_eq : ∀ n β,
      eLpNorm (iterClassicalPartial (d := d) n β ψ) p (volume.restrict Ω) =
      eLpNorm (iterWeakPartial (d := d) p n β ψ Ω) p (volume.restrict Ω) := fun n β => by
    refine eLpNorm_congr_ae ?_
    exact (iterWeakPartial_smooth_ae_eq_iterClassicalPartial
      (d := d) hp_one hΩ_open n β hψ_smooth hψ_cpt hψ_supp).symm
  unfold iteratedWeakSobolevNorm
  refine Finset.sum_le_sum ?_
  intro n hn
  have hn_le : n ≤ k := by rw [Finset.mem_range] at hn; omega
  refine (h_per_n n hn_le).trans ?_
  refine Finset.sum_le_sum ?_
  intro β _
  rw [h_iter_eq]

end Poincare.Analysis.Sobolev.Euclidean
