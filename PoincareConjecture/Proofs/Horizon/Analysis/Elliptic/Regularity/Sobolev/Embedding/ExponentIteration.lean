import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.Subcritical






noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal ContDiff

namespace Poincare.Analysis.Sobolev.EuclideanEmbedding

namespace EuclideanIterated

variable {d : ℕ}

local notation "EuN" => EuclideanSpace ℝ (Fin d)

theorem wkpNorm_mono_order
    {j k : ℕ} (hjk : j ≤ k) {p : ℝ≥0∞} {f : EuN → ℝ} {Ω : Set EuN} :
    Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) j p f Ω ≤
      Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) k p f Ω := by
  classical
  unfold Poincare.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
  refine Finset.sum_le_sum_of_subset ?_
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Finset.mem_range]
  omega

theorem chosenWeakPartial'_cross_exponent_ae_eq
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) {Ω : Set EuN}
    (hΩ_open : IsOpen Ω) {f : EuN → ℝ}
    (hfp : Poincare.Analysis.Sobolev.Weak.MemW1p p f Ω) (hfq : Poincare.Analysis.Sobolev.Weak.MemW1p q f Ω) (i : Fin d) :
    Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' (d := d)
        p i f Ω
      =ᵐ[volume.restrict Ω]
      Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' (d := d)
        q i f Ω := by
  classical
  have h_p_isWeak :=
    Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      (d := d) hfp i
  have h_q_isWeak :=
    Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      (d := d) hfq i
  have h_p_loc : LocallyIntegrable
      (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' p i f Ω)
      (volume.restrict Ω) :=
    (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      (d := d) hfp i).locallyIntegrable hp
  have h_q_loc : LocallyIntegrable
      (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial' q i f Ω)
      (volume.restrict Ω) :=
    (Poincare.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      (d := d) hfq i).locallyIntegrable hq
  exact Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv.ae_eq hΩ_open h_p_isWeak h_q_isWeak
    h_p_loc h_q_loc

open Poincare.Analysis.Sobolev.Euclidean in
theorem wkpNorm_succ_eq
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) :
    iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω =
      eLpNorm u p (volume.restrict Ω) +
        ∑ i : Fin d,
          iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartial' p i u Ω) Ω := by
  classical
  unfold iteratedWeakSobolevNorm
  rw [Finset.sum_range_succ' (n := k + 1)
      (f := fun j =>
        ∑ α : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω))]
  have h_zero_term :
      (∑ α : Fin 0 → Fin d,
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω)) =
        eLpNorm u p (volume.restrict Ω) := by
    have hUniq : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) := fun α => by
      funext i; exact i.elim0
    have : Unique (Fin 0 → Fin d) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (hUniq α).symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α : Fin 0 → Fin d =>
            eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω))]
    simp [iterWeakPartial_zero]
  rw [h_zero_term, add_comm]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  have h_unfold : ∀ α : Fin (j + 1) → Fin d,
      iterWeakPartial (d := d) p (j + 1) α u Ω =
        iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ)
          (chosenWeakPartial' p (α 0) u Ω) Ω :=
    fun α => iterWeakPartial_succ p j α u Ω
  let e : Fin d × (Fin j → Fin d) ≃ (Fin (j + 1) → Fin d) :=
    { toFun := fun p => Fin.cons p.1 p.2
      invFun := fun α => (α 0, fun i : Fin j => α i.succ)
      left_inv := fun p => by
        refine Prod.ext ?_ ?_
        · simp
        · funext i
          change (Fin.cons p.1 p.2 : Fin (j + 1) → Fin d) i.succ = p.2 i
          rw [Fin.cons_succ]
      right_inv := fun α => by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro k
          change (Fin.cons (α 0) (fun i : Fin j => α i.succ) : Fin (j + 1) → Fin d) k.succ
            = α k.succ
          rw [Fin.cons_succ] }
  rw [show
      ∑ α : Fin (j + 1) → Fin d,
        eLpNorm (iterWeakPartial (d := d) p (j + 1) α u Ω) p (volume.restrict Ω) =
      ∑ p' : Fin d × (Fin j → Fin d),
        eLpNorm (iterWeakPartial (d := d) p (j + 1) (e p') u Ω) p (volume.restrict Ω) from
    (Fintype.sum_equiv e
      (fun p' => eLpNorm (iterWeakPartial (d := d) p (j + 1) (e p') u Ω) p
        (volume.restrict Ω))
      (fun α => eLpNorm (iterWeakPartial (d := d) p (j + 1) α u Ω) p
        (volume.restrict Ω))
      (fun _ => rfl)).symm]
  rw [show
      ∑ p' : Fin d × (Fin j → Fin d),
        eLpNorm (iterWeakPartial (d := d) p (j + 1) (e p') u Ω) p (volume.restrict Ω) =
      ∑ i : Fin d, ∑ α' : Fin j → Fin d,
        eLpNorm (iterWeakPartial (d := d) p (j + 1) (e (i, α')) u Ω) p (volume.restrict Ω) from
    Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro α' _
  have hcons_zero : (Fin.cons i α' : Fin (j + 1) → Fin d) 0 = i := Fin.cons_zero _ _
  have hcons_succ : ∀ k : Fin j, (Fin.cons i α' : Fin (j + 1) → Fin d) k.succ = α' k :=
    fun k => Fin.cons_succ _ _ _
  have hiter_eq :
      iterWeakPartial (d := d) p (j + 1) (e (i, α')) u Ω =
        iterWeakPartial (d := d) p j α' (chosenWeakPartial' p i u Ω) Ω := by
    change iterWeakPartial (d := d) p (j + 1) (Fin.cons i α') u Ω =
      iterWeakPartial (d := d) p j α' (chosenWeakPartial' p i u Ω) Ω
    rw [iterWeakPartial_succ]
    have h_tail : (fun k : Fin j => (Fin.cons i α' : Fin (j + 1) → Fin d) k.succ) = α' := by
      funext k; exact hcons_succ k
    rw [h_tail, hcons_zero]
  rw [hiter_eq]

open Poincare.Analysis.Sobolev.Euclidean in
theorem wkpNorm_chosenWeakPartial_le_wkpNorm_succ
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) (i : Fin d) :
    iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartial' p i u Ω) Ω ≤
      iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω := by
  classical
  rw [wkpNorm_succ_eq (d := d) k p u Ω]
  have h_single : iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartial' p i u Ω) Ω ≤
      ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartial' p i u Ω) Ω :=
    Finset.single_le_sum
      (f := fun i : Fin d =>
        iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartial' p i u Ω) Ω)
      (s := (Finset.univ : Finset (Fin d)))
      (fun _ _ => zero_le)
      (Finset.mem_univ i)
  exact le_trans h_single (le_add_self)

open Poincare.Analysis.Sobolev.Euclidean in
theorem eLpNorm_le_wkpNorm
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) :
    eLpNorm u p (volume.restrict Ω) ≤ iteratedWeakSobolevNorm (d := d) k p u Ω := by
  have h := wkpNorm_mono_order (d := d) (Nat.zero_le k) (p := p) (f := u) (Ω := Ω)
  rwa [wkpNorm_zero] at h

end EuclideanIterated
namespace TowerStep

variable {d : ℕ} [NeZero d]

def pOne (d : ℕ) (p : ℝ) : ℝ := (d : ℝ) * p / ((d : ℝ) - p)

lemma pOne_pos {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) :
    0 < pOne d p := by
  unfold pOne
  have hp_pos : 0 < p := by linarith
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hd_p_pos : 0 < (d : ℝ) - p := by linarith
  exact div_pos (mul_pos hd_pos hp_pos) hd_p_pos

lemma pOne_ge_p {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) :
    p ≤ pOne d p := by
  unfold pOne
  have hp_pos : 0 < p := by linarith
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hd_p_pos : 0 < (d : ℝ) - p := by linarith
  rw [le_div_iff₀ hd_p_pos]
  nlinarith [hp_pos]

lemma pOne_ge_one {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) :
    1 ≤ pOne d p :=
  le_trans hp_one (pOne_ge_p hp_one hp_dim)

noncomputable def subcriticalConstantBase (d : ℕ) [NeZero d] (p : ℝ) : ℝ :=
  Poincare.Analysis.Sobolev.Weak.CGns d p * (d : ℝ)

lemma subcriticalConstantBase_nonneg (d : ℕ) [NeZero d] (p : ℝ) :
    0 ≤ subcriticalConstantBase d p := by
  unfold subcriticalConstantBase
  exact mul_nonneg (Poincare.Analysis.Sobolev.Weak.C_gns_nonneg d p) (Nat.cast_nonneg _)

noncomputable def subcriticalConstant : ∀ (_k : ℕ) (d : ℕ) [NeZero d] (_p : ℝ), ℝ
  | 0,     d, _, p => subcriticalConstantBase d p
  | k + 1, d, _, p => subcriticalConstantBase d p + (d : ℝ) * subcriticalConstant k d p

lemma subcriticalConstant_zero (d : ℕ) [NeZero d] (p : ℝ) :
    subcriticalConstant 0 d p = subcriticalConstantBase d p := rfl

lemma subcriticalConstant_succ (k d : ℕ) [NeZero d] (p : ℝ) :
    subcriticalConstant (k + 1) d p =
      subcriticalConstantBase d p + (d : ℝ) * subcriticalConstant k d p := rfl

lemma subcriticalConstant_nonneg (k d : ℕ) [NeZero d] (p : ℝ) :
    0 ≤ subcriticalConstant k d p := by
  induction k with
  | zero => exact subcriticalConstantBase_nonneg d p
  | succ k ih =>
      rw [subcriticalConstant_succ]
      exact add_nonneg (subcriticalConstantBase_nonneg d p)
        (mul_nonneg (Nat.cast_nonneg _) ih)

local notation "EuN" => EuclideanSpace ℝ (Fin d)

open Poincare.Analysis.Sobolev.Euclidean
  EuclideanSubcritical EuclideanIterated

theorem MemWkp_subcritical_iterated
    (k : ℕ) {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) :
    ∀ {f : EuN → ℝ},
      HasCompactSupport f → tsupport f ⊆ Ω →
      MemWkp (d := d) (k + 1) (ENNReal.ofReal p) f Ω →
      MemWkp (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ∧
        iteratedWeakSobolevNorm (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ≤
          ENNReal.ofReal (subcriticalConstant k d p) *
            iteratedWeakSobolevNorm (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  classical
  set p_enn : ℝ≥0∞ := ENNReal.ofReal p with hp_enn_def
  set p_1_enn : ℝ≥0∞ := ENNReal.ofReal (pOne d p) with hp_1_enn_def
  have hp_pos : 0 < p := by linarith
  have hp_1_pos : 0 < pOne d p := pOne_pos hp_one hp_dim
  have hp_1_one : 1 ≤ pOne d p := pOne_ge_one hp_one hp_dim
  have hp_enn_one : (1 : ℝ≥0∞) ≤ p_enn := by
    rw [hp_enn_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_one
  have hp_1_enn_one : (1 : ℝ≥0∞) ≤ p_1_enn := by
    rw [hp_1_enn_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_1_one
  induction k with
  | zero =>
      intro f hf_compact hf_supp hf
      have h_subcritical :
          eLpNorm f p_1_enn (volume.restrict Ω) ≤
            ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) * (d : ℝ≥0∞) *
              iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω := by
        have h := eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp (d := d)
          hp_one hp_dim hΩ_open (f := f) hf hf_compact hf_supp
        change eLpNorm f (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)))
          (volume.restrict Ω) ≤ _ at h
        have hpOne_eq : pOne d p = (d : ℝ) * p / ((d : ℝ) - p) := rfl
        rw [show p_1_enn = ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)) from by
          rw [hp_1_enn_def, hpOne_eq]]
        exact h
      have hf_W1p : Poincare.Analysis.Sobolev.Weak.MemW1p p_enn f Ω := MemWkp.one_iff_memW1p.mp hf
      have hf_aem : AEStronglyMeasurable f (volume.restrict Ω) := hf.memLp.aestronglyMeasurable
      have h_eLp_lt_top : eLpNorm f p_1_enn (volume.restrict Ω) < ⊤ := by
        refine lt_of_le_of_lt h_subcritical ?_
        have h_wkp_lt_top : iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω < ⊤ :=
          wkpNorm_lt_top_of_memWkp hf
        have h_first : (ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) : ℝ≥0∞) ≠ ⊤ := ENNReal.ofReal_ne_top
        have h_d_top : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        refine ENNReal.mul_lt_top ?_ h_wkp_lt_top
        exact ENNReal.mul_lt_top h_first.lt_top h_d_top.lt_top
      have hf_memLp_p1 : MemLp f p_1_enn (volume.restrict Ω) :=
        ⟨hf_aem, h_eLp_lt_top⟩
      refine ⟨?_, ?_⟩
      · rw [MemWkp_zero]
        exact hf_memLp_p1
      · rw [wkpNorm_zero]
        rw [subcriticalConstant_zero]
        unfold subcriticalConstantBase
        have hC_nn : 0 ≤ Poincare.Analysis.Sobolev.Weak.CGns d p := Poincare.Analysis.Sobolev.Weak.C_gns_nonneg d p
        have hd_nn : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        rw [show ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p * (d : ℝ)) =
            ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) * (d : ℝ≥0∞) from by
          rw [ENNReal.ofReal_mul hC_nn, ENNReal.ofReal_natCast]]
        exact h_subcritical
  | succ k ih =>
      intro f hf_compact hf_supp hf
      set K : Set EuN := tsupport f with hK_def
      have hK_compact : IsCompact K := hf_compact
      have hK_closed : IsClosed K := isClosed_tsupport f
      have hKΩ : K ⊆ Ω := hf_supp
      have hf_W1p : Poincare.Analysis.Sobolev.Weak.MemW1p p_enn f Ω := hf.memW1p
      have h_base :
          MemWkp (d := d) 0 p_1_enn f Ω ∧
            iteratedWeakSobolevNorm (d := d) 0 p_1_enn f Ω ≤
              ENNReal.ofReal (subcriticalConstant 0 d p) *
                iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω := by
        have hf1 : MemWkp (d := d) 1 p_enn f Ω :=
          MemWkp.le_of_le (Nat.succ_le_succ (Nat.zero_le _)) hf
        have h_subcritical :
            eLpNorm f p_1_enn (volume.restrict Ω) ≤
              ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) * (d : ℝ≥0∞) *
                iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω := by
          have h := eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp (d := d)
            hp_one hp_dim hΩ_open (f := f) hf1 hf_compact hf_supp
          change eLpNorm f (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)))
            (volume.restrict Ω) ≤ _ at h
          have hpOne_eq : pOne d p = (d : ℝ) * p / ((d : ℝ) - p) := rfl
          rw [show p_1_enn = ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)) from by
            rw [hp_1_enn_def, hpOne_eq]]
          exact h
        have hf_aem : AEStronglyMeasurable f (volume.restrict Ω) :=
          hf.memLp.aestronglyMeasurable
        have h_eLp_lt_top : eLpNorm f p_1_enn (volume.restrict Ω) < ⊤ := by
          refine lt_of_le_of_lt h_subcritical ?_
          have h_wkp_lt_top : iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω < ⊤ :=
            wkpNorm_lt_top_of_memWkp hf1
          refine ENNReal.mul_lt_top ?_ h_wkp_lt_top
          exact ENNReal.mul_lt_top
            (ENNReal.ofReal_lt_top) (ENNReal.natCast_lt_top _)
        refine ⟨?_, ?_⟩
        · rw [MemWkp_zero]; exact ⟨hf_aem, h_eLp_lt_top⟩
        · rw [wkpNorm_zero, subcriticalConstant_zero]
          unfold subcriticalConstantBase
          have hC_nn : 0 ≤ Poincare.Analysis.Sobolev.Weak.CGns d p := Poincare.Analysis.Sobolev.Weak.C_gns_nonneg d p
          rw [show ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p * (d : ℝ)) =
              ENNReal.ofReal (Poincare.Analysis.Sobolev.Weak.CGns d p) * (d : ℝ≥0∞) from by
            rw [ENNReal.ofReal_mul hC_nn, ENNReal.ofReal_natCast]]
          exact h_subcritical
      let g : Fin d → EuN → ℝ :=
        fun i => K.indicator (chosenWeakPartial' p_enn i f Ω)
      have hg_eq_iter : ∀ i,
          g i = iteratedZeroExtension (d := d) p_enn Ω K 1 (fun _ : Fin 1 => i) f := by
        intro i
        change K.indicator (chosenWeakPartial' p_enn i f Ω) = _
        rw [iteratedZeroExtension_one]
      have hg_supp : ∀ i, tsupport (g i) ⊆ K := by
        intro i
        rw [hg_eq_iter i]
        exact tsupport_iteratedZeroExtension_subset (d := d) hK_closed
          (subset_refl K) 1 (fun _ : Fin 1 => i)
      have hg_compact : ∀ i, HasCompactSupport (g i) := by
        intro i
        exact hK_compact.of_isClosed_subset (isClosed_tsupport _) (hg_supp i)
      have hg_supp_Ω : ∀ i, tsupport (g i) ⊆ Ω := fun i => (hg_supp i).trans hKΩ
      have hf_chosen_mem : ∀ i,
          MemWkp (d := d) (k + 1) p_enn (chosenWeakPartial' p_enn i f Ω) Ω :=
        fun i => hf.chosenWeakPartial_mem i
      have h_iterWP_one : ∀ i,
          iterWeakPartial (d := d) p_enn 1 (fun _ : Fin 1 => i) f Ω
            = chosenWeakPartial' p_enn i f Ω := by
        intro i
        rw [iterWeakPartial_succ]
        simp [iterWeakPartial_zero]
      have hg_ae : ∀ i,
          g i =ᵐ[volume.restrict Ω] chosenWeakPartial' p_enn i f Ω := by
        intro i
        rw [hg_eq_iter i]
        have h := iteratedZeroExtension_ae_eq_iterWeakPartial (d := d) hp_enn_one
          hΩ_open hK_closed 1 (k + 1 + 1) (by omega : 1 ≤ k + 1 + 1)
          (fun _ : Fin 1 => i) (u := f) hf (subset_refl _)
        rw [h_iterWP_one] at h
        exact h
      have hg_mem_kplus1 : ∀ i,
          MemWkp (d := d) (k + 1) p_enn (g i) Ω := by
        intro i
        exact (MemWkp_congr_ae (d := d) hp_enn_one hΩ_open (hg_ae i)).mpr (hf_chosen_mem i)
      have h_ih_g : ∀ i,
          MemWkp (d := d) k p_1_enn (g i) Ω ∧
            iteratedWeakSobolevNorm (d := d) k p_1_enn (g i) Ω ≤
              ENNReal.ofReal (subcriticalConstant k d p) *
                iteratedWeakSobolevNorm (d := d) (k + 1) p_enn (g i) Ω :=
        fun i => ih (hg_compact i) (hg_supp_Ω i) (hg_mem_kplus1 i)
      have hf_chosen_mem_p1 : ∀ i,
          MemWkp (d := d) k p_1_enn (chosenWeakPartial' p_enn i f Ω) Ω := by
        intro i
        exact (MemWkp_congr_ae (d := d) hp_1_enn_one hΩ_open (hg_ae i)).mp (h_ih_g i).1
      have h_wkp_eq : ∀ i,
          iteratedWeakSobolevNorm (d := d) k p_1_enn (chosenWeakPartial' p_enn i f Ω) Ω =
            iteratedWeakSobolevNorm (d := d) k p_1_enn (g i) Ω := fun i =>
        (wkpNorm_congr_ae (d := d) hp_1_enn_one hΩ_open (hg_ae i)).symm
      have h_wkp_eq_p : ∀ i,
          iteratedWeakSobolevNorm (d := d) (k + 1) p_enn (chosenWeakPartial' p_enn i f Ω) Ω =
            iteratedWeakSobolevNorm (d := d) (k + 1) p_enn (g i) Ω := fun i =>
        (wkpNorm_congr_ae (d := d) hp_enn_one hΩ_open (hg_ae i)).symm
      have hf_W1p_p1 : Poincare.Analysis.Sobolev.Weak.MemW1p p_1_enn f Ω := by
        refine ⟨?_, ?_⟩
        · exact h_base.1
        · intro i
          refine ⟨chosenWeakPartial' p_enn i f Ω, ?_, ?_⟩
          · exact (hf_chosen_mem_p1 i).memLp
          · exact chosenWeakPartial'_isWeakPartial_of_mem hf_W1p i
      have hf_mem_p1 : MemWkp (d := d) (k + 1) p_1_enn f Ω := by
        rw [MemWkp_succ]
        refine ⟨hf_W1p_p1, ?_⟩
        intro i
        have h_cross : chosenWeakPartial' p_1_enn i f Ω
            =ᵐ[volume.restrict Ω] chosenWeakPartial' p_enn i f Ω :=
          chosenWeakPartial'_cross_exponent_ae_eq (d := d)
            hp_1_enn_one hp_enn_one hΩ_open hf_W1p_p1 hf_W1p i
        exact (MemWkp_congr_ae (d := d) hp_1_enn_one hΩ_open h_cross).mpr (hf_chosen_mem_p1 i)
      refine ⟨hf_mem_p1, ?_⟩
      rw [wkpNorm_succ_eq (d := d) k p_1_enn f Ω]
      have h_eLp_bound :
          eLpNorm f p_1_enn (volume.restrict Ω) ≤
            ENNReal.ofReal (subcriticalConstantBase d p) *
              iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω := by
        have h := h_base.2
        rw [wkpNorm_zero, subcriticalConstant_zero] at h
        exact h
      have h_sum_term_bound : ∀ i,
          iteratedWeakSobolevNorm (d := d) k p_1_enn (chosenWeakPartial' p_1_enn i f Ω) Ω ≤
            ENNReal.ofReal (subcriticalConstant k d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω := by
        intro i
        have h_cross : chosenWeakPartial' p_1_enn i f Ω
            =ᵐ[volume.restrict Ω] chosenWeakPartial' p_enn i f Ω :=
          chosenWeakPartial'_cross_exponent_ae_eq (d := d)
            hp_1_enn_one hp_enn_one hΩ_open hf_W1p_p1 hf_W1p i
        rw [wkpNorm_congr_ae (d := d) hp_1_enn_one hΩ_open h_cross]
        rw [h_wkp_eq i]
        refine le_trans (h_ih_g i).2 ?_
        rw [← h_wkp_eq_p i]
        gcongr
        exact wkpNorm_chosenWeakPartial_le_wkpNorm_succ (d := d)
          (k + 1) p_enn f Ω i
      have h_sum_bound :
          ∑ i : Fin d,
            iteratedWeakSobolevNorm (d := d) k p_1_enn (chosenWeakPartial' p_1_enn i f Ω) Ω ≤
          ∑ _i : Fin d,
            ENNReal.ofReal (subcriticalConstant k d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω :=
        Finset.sum_le_sum (fun i _ => h_sum_term_bound i)
      have h_sum_const :
          ∑ _i : Fin d,
            ENNReal.ofReal (subcriticalConstant k d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω =
            (d : ℝ≥0∞) *
              (ENNReal.ofReal (subcriticalConstant k d p) *
                iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul]
      have h_eLp_full : eLpNorm f p_1_enn (volume.restrict Ω) ≤
          ENNReal.ofReal (subcriticalConstantBase d p) *
            iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω := by
        refine le_trans h_eLp_bound ?_
        gcongr
        exact wkpNorm_mono_order (d := d) (by omega : 1 ≤ k + 1 + 1)
          (p := p_enn) (f := f) (Ω := Ω)
      calc
        eLpNorm f p_1_enn (volume.restrict Ω) +
            ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) k p_1_enn
              (chosenWeakPartial' p_1_enn i f Ω) Ω
          ≤ ENNReal.ofReal (subcriticalConstantBase d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω +
              ∑ _i : Fin d,
                ENNReal.ofReal (subcriticalConstant k d p) *
                  iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω :=
            add_le_add h_eLp_full h_sum_bound
        _ = ENNReal.ofReal (subcriticalConstantBase d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω +
              (d : ℝ≥0∞) *
                (ENNReal.ofReal (subcriticalConstant k d p) *
                  iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω) := by
              rw [h_sum_const]
        _ = (ENNReal.ofReal (subcriticalConstantBase d p) +
              (d : ℝ≥0∞) * ENNReal.ofReal (subcriticalConstant k d p)) *
            iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω := by
              rw [add_mul, mul_assoc]
        _ = ENNReal.ofReal (subcriticalConstant (k + 1) d p) *
            iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω := by
              rw [subcriticalConstant_succ]
              rw [ENNReal.ofReal_add (subcriticalConstantBase_nonneg d p)
                (mul_nonneg (Nat.cast_nonneg _) (subcriticalConstant_nonneg k d p))]
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
              rw [ENNReal.ofReal_natCast]

theorem MemWkp_succ_subcritical_step
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ}
    (hf_compact : HasCompactSupport f) (hf_supp : tsupport f ⊆ Ω)
    (hf : MemWkp (d := d) (k + 1) (ENNReal.ofReal p) f Ω) :
    MemWkp (d := d) k (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := d) k
            (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ≤
          ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  obtain ⟨h_mem, h_norm⟩ :=
    MemWkp_subcritical_iterated (d := d) k hp_one hp_dim hΩ_open
      hf_compact hf_supp hf
  have hpOne_eq : pOne d p = (d : ℝ) * p / ((d : ℝ) - p) := rfl
  refine ⟨?_, ?_⟩
  · rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_mem
  · refine ⟨subcriticalConstant k d p, subcriticalConstant_nonneg k d p, ?_⟩
    rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_norm

end TowerStep
namespace IterationCalc

private lemma kp1_gt_n_of_kp1p_gt_n
    (n : ℝ) (k : ℕ) (p : ℝ) (hp_pos : 0 < p) (hp_dim : p < n)
    (hkp : n < (k + 1 : ℝ) * p) :
    n < (k : ℝ) * (n * p / (n - p)) := by
  have hn_pos : 0 < n := lt_of_lt_of_le hp_pos hp_dim.le
  have hn_p_pos : 0 < n - p := by linarith
  have hkp_gt : (k : ℝ) * p > n - p := by
    have : (k + 1 : ℝ) * p = (k : ℝ) * p + p := by ring
    linarith [hkp]
  have h_eq : (k : ℝ) * (n * p / (n - p)) = n * ((k : ℝ) * p) / (n - p) := by
    field_simp
  rw [h_eq]
  rw [lt_div_iff₀ hn_p_pos]
  have h_factor : n * ((k : ℝ) * p) - n * (n - p) = n * ((k : ℝ) * p - (n - p)) := by
    ring
  nlinarith [hkp_gt, hn_pos]

lemma kp1_real_gt_d_of_kp1p_gt_d
    (d : ℕ) (k : ℕ) (p : ℝ) (hp_pos : 0 < p) (hp_dim : p < (d : ℝ))
    (hkp : (d : ℝ) < (k + 1 : ℝ) * p) :
    (d : ℝ) < (k : ℝ) * ((d : ℝ) * p / ((d : ℝ) - p)) :=
  kp1_gt_n_of_kp1p_gt_n (d : ℝ) k p hp_pos hp_dim hkp

end IterationCalc
namespace RegularExponent

def IsRegular (n : ℝ) (p : ℝ) (k : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ k → ((m : ℝ) * p ≠ n)

lemma IsRegular.zero (n : ℝ) (p : ℝ) : IsRegular n p 0 := by
  intro m hm hm_le
  exact absurd hm_le (by omega)

lemma IsRegular.le_of_succ {n p : ℝ} {k : ℕ}
    (h : IsRegular n p (k + 1)) : IsRegular n p k := by
  intro m hm hm_le
  exact h m hm (by omega)

lemma IsRegular.p_ne_n_of_one_le {n p : ℝ} {k : ℕ}
    (h : IsRegular n p k) (hk : 1 ≤ k) : p ≠ n := by
  intro hp_eq
  have h1 : ((1 : ℕ) : ℝ) * p ≠ n := h 1 (le_refl 1) hk
  have : (1 : ℝ) * p = p := by ring
  rw [Nat.cast_one] at h1
  rw [this] at h1
  exact h1 hp_eq

lemma IsRegular.tower_step
    {n p : ℝ} {k : ℕ}
    (hp_one : 1 ≤ p) (hp_lt : p < n) (h : IsRegular n p (k + 1)) :
    IsRegular n (n * p / (n - p)) k := by
  intro m hm hm_le
  have hp_pos : 0 < p := by linarith
  have hd_pos : 0 < n := lt_of_lt_of_le hp_pos hp_lt.le
  have hd_p_pos : 0 < n - p := by linarith
  have h_succ : ((m + 1 : ℕ) : ℝ) * p ≠ n := h (m + 1) (by omega) (by omega)
  intro h_eq
  have h_eq' : (m : ℝ) * (n * p) = n * (n - p) := by
    have : (m : ℝ) * (n * p / (n - p)) * (n - p) = n * (n - p) := by
      rw [h_eq]
    rw [show (m : ℝ) * (n * p / (n - p)) * (n - p) =
        (m : ℝ) * (n * p) by
      field_simp] at this
    exact this
  have h_eq2 : ((m + 1 : ℕ) : ℝ) * p = n := by
    have h_mul : (m : ℝ) * (n * p) = n * (n - p) := h_eq'
    have hn_ne : n ≠ 0 := hd_pos.ne'
    push_cast
    have : (m : ℝ) * (n * p) + n * p = n * (n - p) + n * p := by rw [h_mul]
    nlinarith [hn_ne]
  exact h_succ h_eq2

end RegularExponent
namespace RegularExponent

private noncomputable def borderlineSet (n : ℝ) (k : ℕ) : Finset ℝ :=
  (Finset.Icc 1 k).image (fun m : ℕ => n / (m : ℝ))

private lemma isRegular_iff_notMem_borderlineSet
    {n p : ℝ} {k : ℕ} :
    IsRegular n p k ↔ p ∉ borderlineSet n k := by
  classical
  unfold IsRegular borderlineSet
  refine ⟨fun h hmem => ?_, fun hnot m hm_one hm_le hmp_eq => ?_⟩
  · rw [Finset.mem_image] at hmem
    obtain ⟨m, hm_mem, hm_eq⟩ := hmem
    rw [Finset.mem_Icc] at hm_mem
    obtain ⟨hm_one, hm_le⟩ := hm_mem
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hjp : (m : ℝ) * p = n := by
      have hp_eq : p = n / (m : ℝ) := hm_eq.symm
      rw [hp_eq]; field_simp
    exact h m hm_one hm_le hjp
  · apply hnot
    rw [Finset.mem_image]
    refine ⟨m, ?_, ?_⟩
    · rw [Finset.mem_Icc]; exact ⟨hm_one, hm_le⟩
    · have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      field_simp
      linarith [hmp_eq]

private lemma exists_notMem_finset_in_open_interval
    {lb p : ℝ} (hlb_lt_p : lb < p) (S : Finset ℝ) :
    ∃ p' : ℝ, lb < p' ∧ p' < p ∧ p' ∉ S := by
  classical
  set T : Finset ℝ := S.filter (fun x => lb < x ∧ x < p) with hT_def
  by_cases hT : T = ∅
  · refine ⟨(lb + p) / 2, by linarith, by linarith, ?_⟩
    intro hmem
    have : (lb + p) / 2 ∈ T := by
      rw [hT_def, Finset.mem_filter]
      exact ⟨hmem, by linarith, by linarith⟩
    rw [hT] at this
    exact (Finset.notMem_empty _) this
  · have hT_nonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
    set M : ℝ := T.max' hT_nonempty with hM_def
    have hM_mem : M ∈ T := T.max'_mem hT_nonempty
    have hM_lt_p : M < p := (Finset.mem_filter.mp hM_mem).2.2
    have hM_gt_lb : lb < M := (Finset.mem_filter.mp hM_mem).2.1
    refine ⟨(M + p) / 2, by linarith, by linarith, ?_⟩
    intro hmem
    have h_in_T : (M + p) / 2 ∈ T := by
      rw [hT_def, Finset.mem_filter]
      exact ⟨hmem, by linarith, by linarith⟩
    have h_le : (M + p) / 2 ≤ M := T.le_max' _ h_in_T
    linarith

lemma exists_regular_exponent_below
    (n : ℝ) (k : ℕ) (hk : 1 ≤ k) {p : ℝ} (hp_one : 1 < p)
    (hkp : n < (k : ℝ) * p) :
    ∃ p' : ℝ, 1 ≤ p' ∧ p' < p ∧ n < (k : ℝ) * p' ∧
      IsRegular n p' k := by
  classical
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  set lb : ℝ := max 1 (n / (k : ℝ)) with hlb_def
  have hnk_lt_p : n / (k : ℝ) < p := by
    rw [div_lt_iff₀ hk_pos]; linarith
  have hlb_lt_p : lb < p := by
    rw [hlb_def, max_lt_iff]; exact ⟨hp_one, hnk_lt_p⟩
  obtain ⟨p', hp'_lb, hp'_lt, hp'_notMem⟩ :=
    exists_notMem_finset_in_open_interval hlb_lt_p (borderlineSet n k)
  refine ⟨p', ?_, hp'_lt, ?_, ?_⟩
  · have h1_le_lb : (1 : ℝ) ≤ lb := by rw [hlb_def]; exact le_max_left _ _
    linarith
  · have hnk_le_lb : n / (k : ℝ) ≤ lb := by rw [hlb_def]; exact le_max_right _ _
    have h_n_lt_kp' : n / (k : ℝ) < p' := lt_of_le_of_lt hnk_le_lb hp'_lb
    rw [div_lt_iff₀ hk_pos] at h_n_lt_kp'; linarith
  · exact (isRegular_iff_notMem_borderlineSet (n := n) (p := p') (k := k)).mpr
      hp'_notMem

end RegularExponent

namespace EuclideanIteratedMonoExp

variable {d : ℕ} [NeZero d]

local notation "EuN" => EuclideanSpace ℝ (Fin d)

open Poincare.Analysis.Sobolev.Euclidean

omit [NeZero d] in
private lemma diff_K_subset_diff_subset
    {S K Ω : Set EuN} (hSK : S ⊆ K) :
    Ω \ K ⊆ Ω \ S := fun _ ⟨hx_Ω, hx_notK⟩ =>
  ⟨hx_Ω, fun h => hx_notK (hSK h)⟩

omit [NeZero d] in
private lemma ae_eq_indicator_of_ae_zero_off_subset
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) {S K : Set EuN} (hSK : S ⊆ K)
    (hK_meas : MeasurableSet K)
    {g : EuN → ℝ}
    (hg_ae_zero : g =ᵐ[(MeasureTheory.volume :
        MeasureTheory.Measure EuN).restrict (Ω \ S)] (fun _ : EuN => (0 : ℝ))) :
    g =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω]
      K.indicator g := by
  classical
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hΩK_meas : MeasurableSet (Ω \ K) := hΩ_meas.diff hK_meas
  have h_ae_zero_diffK : ∀ᵐ x ∂((MeasureTheory.volume :
      MeasureTheory.Measure EuN).restrict (Ω \ K)), g x = 0 := by
    have h := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (s := Ω \ K) (t := Ω \ S)
      (diff_K_subset_diff_subset (Ω := Ω) hSK) hg_ae_zero
    exact h
  rw [MeasureTheory.ae_restrict_iff' hΩK_meas] at h_ae_zero_diffK
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hΩ_meas]
  filter_upwards [h_ae_zero_diffK] with x hx hx_Ω
  by_cases h_in_K : x ∈ K
  · simp [Set.indicator_of_mem h_in_K]
  · have hx_diff : x ∈ Ω \ K := ⟨hx_Ω, h_in_K⟩
    have : g x = 0 := hx hx_diff
    simp [Set.indicator_of_notMem h_in_K, this]

omit [NeZero d] in
private lemma chosenWeakPartial'_ae_eq_indicator_of_tsupport_subset
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {K : Set EuN} (hK_meas : MeasurableSet K)
    {f : EuN → ℝ}
    (hf_W1p : Poincare.Analysis.Sobolev.Weak.MemW1p p f Ω)
    (hf_supp : tsupport f ⊆ K) (i : Fin d) :
    chosenWeakPartial' (d := d) p i f Ω
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω]
      K.indicator (chosenWeakPartial' (d := d) p i f Ω) := by
  have h_ae_zero_sdiff :
      chosenWeakPartial' (d := d) p i f Ω
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict
          (Ω \ tsupport f)] (fun _ : EuN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_on_sdiff_tsupport (d := d) hp_one hΩ_open
      hf_W1p i
  exact ae_eq_indicator_of_ae_zero_off_subset (Ω := Ω) hΩ_open
    (S := tsupport f) (K := K) hf_supp hK_meas h_ae_zero_sdiff

omit [NeZero d] in
theorem memWkp_mono_exponent_of_tsupport_subset
    (k : ℕ) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {K : Set EuN} (hK_closed : IsClosed K)
    (hK_meas_lt_top : MeasureTheory.volume K ≠ ⊤)
    {p p' : ℝ≥0∞} (hp'_one : 1 ≤ p') (hp'_le_p : p' ≤ p)
    {f : EuN → ℝ}
    (hf_supp : tsupport f ⊆ K)
    (hfp : MemWkp (d := d) k p f Ω) :
    MemWkp (d := d) k p' f Ω := by
  have hp_one : (1 : ℝ≥0∞) ≤ p := le_trans hp'_one hp'_le_p
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  have hKΩ_meas_lt_top :
      ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) K ≠ ⊤ :=
    ne_top_of_le_ne_top hK_meas_lt_top
      (MeasureTheory.Measure.restrict_apply_le _ _)
  have memLp_mono : ∀ {q q' : ℝ≥0∞} (_hq_le : q' ≤ q) {h : EuN → ℝ},
      h =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω]
        K.indicator h →
      MeasureTheory.MemLp h q
        ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) →
      MeasureTheory.MemLp h q'
        ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) := by
    intro q q' hq_le h h_eq h_memLp
    have h_zero_off : ∀ x, x ∉ K → K.indicator h x = 0 := fun x hx =>
      Set.indicator_of_notMem hx _
    have h_clean_memLp_q : MeasureTheory.MemLp (K.indicator h) q
        ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) :=
      (MeasureTheory.memLp_congr_ae h_eq).mp h_memLp
    have h_clean_memLp_q' : MeasureTheory.MemLp (K.indicator h) q'
        ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) :=
      h_clean_memLp_q.mono_exponent_of_measure_support_ne_top h_zero_off
        hKΩ_meas_lt_top hq_le
    exact (MeasureTheory.memLp_congr_ae h_eq).mpr h_clean_memLp_q'
  have indicator_tsupport_subset : ∀ (g : EuN → ℝ),
      tsupport (K.indicator g) ⊆ K := by
    intro g
    have h_supp_sub : Function.support (K.indicator g) ⊆ K := by
      intro x hx
      by_contra hxK
      have h_zero : K.indicator g x = 0 := Set.indicator_of_notMem hxK _
      exact (Function.mem_support.mp hx) h_zero
    calc tsupport (K.indicator g)
        = closure (Function.support (K.indicator g)) := rfl
      _ ⊆ closure K := closure_mono h_supp_sub
      _ = K := hK_closed.closure_eq
  have ae_eq_indicator_of_tsupport : ∀ {h : EuN → ℝ}, tsupport h ⊆ K →
      h =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω]
        K.indicator h := by
    intro h hh_supp
    refine MeasureTheory.ae_of_all _ ?_
    intro x
    by_cases h_in_K : x ∈ K
    · rw [Set.indicator_of_mem h_in_K]
    · have hx_not_supp : x ∉ tsupport h := fun hsx => h_in_K (hh_supp hsx)
      have hh_x_zero : h x = 0 := image_eq_zero_of_notMem_tsupport hx_not_supp
      rw [Set.indicator_of_notMem h_in_K, hh_x_zero]
  induction k generalizing f with
  | zero =>
      rw [MemWkp_zero] at hfp ⊢
      exact memLp_mono hp'_le_p (ae_eq_indicator_of_tsupport hf_supp) hfp
  | succ k ih =>
      rw [MemWkp_succ] at hfp ⊢
      obtain ⟨hf_W1p, hf_recursive⟩ := hfp
      have hf_ae_eq_indicator := ae_eq_indicator_of_tsupport hf_supp
      have hf_W1p' : Poincare.Analysis.Sobolev.Weak.MemW1p p' f Ω := by
        refine ⟨memLp_mono hp'_le_p hf_ae_eq_indicator hf_W1p.1, ?_⟩
        intro i
        set g : EuN → ℝ := chosenWeakPartial' (d := d) p i f Ω with hg_def
        have hg_memLp_p : MeasureTheory.MemLp g p
            ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) :=
          chosenWeakPartial'_memLp_of_mem (d := d) hf_W1p i
        have hg_weak : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i g f Ω :=
          chosenWeakPartial'_isWeakPartial_of_mem (d := d) hf_W1p i
        have hg_ae_eq_indicator : g =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure EuN).restrict Ω] K.indicator g :=
          chosenWeakPartial'_ae_eq_indicator_of_tsupport_subset
            (d := d) hp_one hΩ_open hK_meas hf_W1p hf_supp i
        exact ⟨g, memLp_mono hp'_le_p hg_ae_eq_indicator hg_memLp_p, hg_weak⟩
      refine ⟨hf_W1p', ?_⟩
      intro i
      set g_p : EuN → ℝ := chosenWeakPartial' (d := d) p i f Ω with hg_p_def
      have hg_p_mem : MemWkp (d := d) k p g_p Ω := hf_recursive i
      have hg_p_ae_eq_indicator : g_p =ᵐ[(MeasureTheory.volume :
          MeasureTheory.Measure EuN).restrict Ω] K.indicator g_p :=
        chosenWeakPartial'_ae_eq_indicator_of_tsupport_subset
          (d := d) hp_one hΩ_open hK_meas hf_W1p hf_supp i
      have h_indicator_tsupport : tsupport (K.indicator g_p) ⊆ K :=
        indicator_tsupport_subset g_p
      have h_indicator_memWkp_p : MemWkp (d := d) k p (K.indicator g_p) Ω :=
        (MemWkp_congr_ae (d := d) hp_one hΩ_open hg_p_ae_eq_indicator).mp hg_p_mem
      have h_indicator_memWkp_p' : MemWkp (d := d) k p' (K.indicator g_p) Ω :=
        ih h_indicator_tsupport h_indicator_memWkp_p
      have hg_p_memWkp_p' : MemWkp (d := d) k p' g_p Ω :=
        (MemWkp_congr_ae (d := d) hp'_one hΩ_open hg_p_ae_eq_indicator).mpr
          h_indicator_memWkp_p'
      have h_cross_ae : chosenWeakPartial' (d := d) p' i f Ω
          =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω] g_p :=
        Analysis.Sobolev.EuclideanEmbedding.EuclideanIterated.chosenWeakPartial'_cross_exponent_ae_eq
          (d := d) hp'_one hp_one hΩ_open hf_W1p' hf_W1p i
      exact (MemWkp_congr_ae (d := d) hp'_one hΩ_open h_cross_ae).mpr hg_p_memWkp_p'

end EuclideanIteratedMonoExp

end Poincare.Analysis.Sobolev.EuclideanEmbedding
