import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Charts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture
namespace TerminalNeck

private theorem contDiff_spatial_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => iteratedFDeriv ℝ m (fun x => f (p.1, x)) p.2) := by
  induction m with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp hf
  | succ m ih =>
    have hg : ContDiff ℝ ∞ (fun p : (ℝ × E) × E =>
        iteratedFDeriv ℝ m (fun x => f (p.1.1, x)) p.2) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd := hg.fderiv
      (f := fun (p : ℝ × E) y => iteratedFDeriv ℝ m (fun x => f (p.1, x)) y)
      (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × E → E))
      (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).symm.contDiff.comp hd

private theorem finite_spatial_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {f : ι → ℝ × E → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j, j ≤ m → ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ j (fun y => f i (s, y)) x‖ ≤ C := by
  classical
  choose A hA using fun i : ι × Fin (m + 1) =>
    (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      (contDiff_spatial_iteratedFDeriv (hf i.1) (i.2 : ℕ)).continuous.continuousOn
  let C : ℝ := ∑ i : ι × Fin (m + 1), max (A i) 0
  refine ⟨C, Finset.sum_nonneg fun i _ => le_max_right _ _, ?_⟩
  intro i j hj s hs x hx
  let k : ι × Fin (m + 1) := (i, ⟨j, Nat.lt_succ_of_le hj⟩)
  exact (hA k (s, x) ⟨hs, hx⟩).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun i _ => le_max_right (A i) 0) (Finset.mem_univ k)))

private theorem contDiff_matrix_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ}
    (hA : ∀ a b, ContDiff ℝ ∞ (fun x => A x a b)) :
    ContDiff ℝ ∞ (fun x => (A x).det) := by
  have heq : (fun x => (A x).det) = fun x =>
      ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℝ) * ∏ i, A x (σ i) i := by
    funext x
    simp [Matrix.det_apply, Units.smul_def]
  rw [heq]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hA (σ i) i)

private theorem contDiff_matrix_inv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ}
    (hA : ∀ a b, ContDiff ℝ ∞ (fun x => A x a b))
    (hdet : ∀ x, (A x).det ≠ 0) (a b : ι) :
    ContDiff ℝ ∞ (fun x => (A x)⁻¹ a b) := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_apply]
  apply ((contDiff_matrix_det hA).inv hdet).mul
  apply contDiff_matrix_det
  intro i j
  by_cases hi : i = b
  · subst i
    simpa only [Matrix.updateRow_self] using
      (contDiff_const (c := (Pi.single a (1 : ℝ) : ι → ℝ) j) :
        ContDiff ℝ ∞ (fun _ : E => (Pi.single a (1 : ℝ) : ι → ℝ) j))
  · simpa only [Matrix.updateRow_ne hi] using hA i j

private theorem contDiff_backward_Gram (q : UnitTwoSphere) (a b : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × RoundCylinderCoordinates =>
      roundCylinderGram (-p.1 ^ 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q) p.2 a b) := by
  simp_rw [roundCylinderGram_eq_stereographic_formula]
  have hs : ContDiff ℝ ∞ (fun p : ℝ × RoundCylinderCoordinates =>
      16 / (‖p.2.1‖ ^ 2 + 4) ^ 2) :=
    contDiff_const.div
      ((((contDiff_norm_sq ℝ).comp contDiff_snd.fst).add contDiff_const).pow 2)
      (fun p => by positivity)
  exact ((contDiff_const.mul (contDiff_const.sub (contDiff_fst.pow 2).neg)).mul hs
    |>.mul contDiff_const).add contDiff_const

private theorem contDiff_backward_Gram_inv (q : UnitTwoSphere) (a b : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × RoundCylinderCoordinates =>
      (roundCylinderGram (-p.1 ^ 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q) p.2)⁻¹ a b) :=
  contDiff_matrix_inv (contDiff_backward_Gram q)
    (fun p => roundCylinderGram_det_ne_zero (by nlinarith [sq_nonneg p.1]) q p.2) a b

private theorem contDiff_backward_Christoffel (q : UnitTwoSphere) (a b d : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × RoundCylinderCoordinates =>
      roundCylinderChristoffel (-p.1 ^ 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q) p.2 a b d) := by
  have hd (i j k : Fin 3) : ContDiff ℝ ∞ (fun p : ℝ × RoundCylinderCoordinates =>
      fderiv ℝ (fun x => roundCylinderGram (-p.1 ^ 2)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) x i j) p.2 (roundCylinderCoordinateBasis k)) := by
    have hg := (contDiff_backward_Gram q i j).comp
      ((contDiff_fst.fst : ContDiff ℝ ∞ (fun p : (ℝ × RoundCylinderCoordinates) ×
        RoundCylinderCoordinates => p.1.1)).prodMk contDiff_snd)
    exact (hg.fderiv contDiff_snd (by simp)).clm_apply contDiff_const
  unfold roundCylinderChristoffel
  exact contDiff_const.mul (ContDiff.sum fun j _ =>
    (contDiff_backward_Gram_inv q a j).mul ((hd d j b).add (hd b j d) |>.sub (hd b d j)))

theorem exists_evolvingChristoffel_spatialJet_bound
    (q : UnitTwoSphere) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (-1 : ℝ) 0, ∀ j, j ≤ m →
      ∀ a b d : Fin 3, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b d) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := finite_spatial_jet_bound
    (f := fun a : Fin 3 × Fin 3 × Fin 3 => fun p : ℝ × RoundCylinderCoordinates =>
      roundCylinderChristoffel (-p.1 ^ 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        p.2 a.1 a.2.1 a.2.2)
    (fun a => contDiff_backward_Christoffel q a.1 a.2.1 a.2.2) hK m
  refine ⟨C, hC, ?_⟩
  intro u hu j hj a b d x hx
  have hs : Real.sqrt (-u) ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, (Real.sqrt_le_one).2 (by linarith [hu.1])⟩
  have heq : -(Real.sqrt (-u)) ^ 2 = u := by rw [Real.sq_sqrt (by linarith [hu.2])]; ring
  simpa only [heq] using hbound (a, b, d) j hj (Real.sqrt (-u)) hs x hx

theorem exists_evolvingInverseGram_bound
    (q : UnitTwoSphere) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (-1 : ℝ) 0, ∀ a b : Fin 3, ∀ x ∈ K,
      ‖(roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) x)⁻¹ a b‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := finite_spatial_jet_bound
    (f := fun a : Fin 3 × Fin 3 => fun p : ℝ × RoundCylinderCoordinates =>
      (roundCylinderGram (-p.1 ^ 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q) p.2)⁻¹ a.1 a.2)
    (fun a => contDiff_backward_Gram_inv q a.1 a.2) hK 0
  refine ⟨C, hC, ?_⟩
  intro u hu a b x hx
  have hs : Real.sqrt (-u) ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, (Real.sqrt_le_one).2 (by linarith [hu.1])⟩
  have heq : -(Real.sqrt (-u)) ^ 2 = u := by rw [Real.sq_sqrt (by linarith [hu.2])]; ring
  simpa only [heq, norm_iteratedFDeriv_zero] using
    hbound (a, b) 0 (le_refl _) (Real.sqrt (-u)) hs x hx

end TerminalNeck
end PoincareConjecture
