import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.IntegerMatrix
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Lifts.Affine
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PeriodCircleLoop

set_option autoImplicit false

open scoped unitInterval

namespace PoincareConjecture.M76.LinearTorus

variable (p : ℝ)

def integerPeriodLoop (n : ℤ) : Path (0 : AddCircle p) 0 where
  toFun t := n • AddCircle.periodLoop p t
  continuous_toFun := (AddCircle.periodLoop p).continuous.zsmul n
  source' := by simp
  target' := by simp

theorem integerPeriodLoop_eq_zero_of_homotopic_refl (hp : 0 < p) (n : ℤ)
    (h : (integerPeriodLoop p n).Homotopic (Path.refl (0 : AddCircle p))) : n = 0 := by
  let : Fact (0 < p) := ⟨hp⟩
  let cov := AddCircle.isCoveringMap_coe p
  let f : C(unitInterval, ℝ) :=
    ⟨fun t => (n : ℝ) * ((t : ℝ) * p),
      continuous_const.mul (continuous_subtype_val.mul_const p)⟩
  have h0 : (integerPeriodLoop p n) 0 = ((0 : ℝ) : AddCircle p) := by
    simp only [Path.source, AddCircle.coe_zero]
  have h1 : (Path.refl (0 : AddCircle p)) 0 = ((0 : ℝ) : AddCircle p) := rfl
  have hf : f = cov.liftPath (integerPeriodLoop p n).toContinuousMap 0 h0 := by
    apply (cov.eq_liftPath_iff' h0).mpr
    constructor
    · funext t
      change (((n : ℝ) * ((t : ℝ) * p) : ℝ) : AddCircle p) =
        n • (((t : ℝ) * p : ℝ) : AddCircle p)
      simp [← zsmul_eq_mul]
    · change (n : ℝ) * (0 * p) = 0
      simp
  have hc : cov.liftPath (Path.refl (0 : AddCircle p)).toContinuousMap 0 h1 =
      ContinuousMap.const unitInterval (0 : ℝ) := cov.liftPath_const rfl
  have he := cov.liftPath_apply_one_eq_of_homotopicRel h 0 h0 h1
  rw [← hf, hc] at he
  have hn : (n : ℝ) * p = 0 := by simpa [f] using he
  exact Int.cast_eq_zero.mp ((mul_eq_zero.mp hn).resolve_right hp.ne')

variable (A : Matrix (Fin 2) (Fin 2) ℤ)

theorem integer_kernel_eq_zero_of_fundamentalGroup_map_injective (hp : 0 < p)
    (hinj : Function.Injective (FundamentalGroup.map (integerMatrixMap p A) 0))
    (n m : ℤ) (h0 : A 0 0 * n + A 0 1 * m = 0)
    (h1 : A 1 0 * n + A 1 1 * m = 0) : n = 0 ∧ m = 0 := by
  let γ : Path (0 : AddCircle p × AddCircle p) 0 :=
    (integerPeriodLoop p n).prod (integerPeriodLoop p m)
  have hkill : γ.map (integerMatrixMap p A).continuous =
      Path.refl (integerMatrixMap p A 0) := by
    apply Path.ext
    funext t
    change (A 0 0 • (n • AddCircle.periodLoop p t) +
        A 0 1 • (m • AddCircle.periodLoop p t),
      A 1 0 • (n • AddCircle.periodLoop p t) +
        A 1 1 • (m • AddCircle.periodLoop p t)) =
      (A 0 0 • (0 : AddCircle p) + A 0 1 • 0, A 1 0 • 0 + A 1 1 • 0)
    simp only [smul_smul, ← add_smul, h0, h1, zero_smul,
      smul_zero, add_zero]
  have hγ : γ.Homotopic (Path.refl 0) := by
    apply Path.Homotopic.Quotient.exact
    apply hinj
    change Path.Homotopic.Quotient.mk (γ.map (integerMatrixMap p A).continuous) =
      Path.Homotopic.Quotient.mk ((Path.refl 0).map (integerMatrixMap p A).continuous)
    rw [hkill]
    rfl
  constructor
  · apply integerPeriodLoop_eq_zero_of_homotopic_refl p hp n
    exact hγ.map ContinuousMap.fst
  · apply integerPeriodLoop_eq_zero_of_homotopic_refl p hp m
    exact hγ.map ContinuousMap.snd

theorem det_ne_zero_of_fundamentalGroup_map_injective (hp : 0 < p)
    (hinj : Function.Injective (FundamentalGroup.map (integerMatrixMap p A) 0)) :
    A.det ≠ 0 := by
  intro hdet
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 0 := by
    simpa only [Matrix.det_fin_two] using hdet
  have hrow := integer_kernel_eq_zero_of_fundamentalGroup_map_injective p A hp hinj
    (A 0 1) (-A 0 0) (by ring) (by nlinarith [hd])
  have h00 : A 0 0 = 0 := neg_eq_zero.mp hrow.2
  have hrow' := integer_kernel_eq_zero_of_fundamentalGroup_map_injective p A hp hinj
    (A 1 1) (-A 1 0) (by rw [h00, hrow.1]; ring) (by ring)
  have h10 : A 1 0 = 0 := neg_eq_zero.mp hrow'.2
  have hone := integer_kernel_eq_zero_of_fundamentalGroup_map_injective p A hp hinj
    1 0 (by simp [h00]) (by simp [h10])
  exact one_ne_zero hone.1

theorem det_ne_zero_of_affine_fundamentalGroup_map_injective (hp : 0 < p)
    (c : AddCircle p × AddCircle p)
    (hinj : Function.Injective (FundamentalGroup.map (affineIntegerMatrixMap p A c) 0)) :
    A.det ≠ 0 := by
  apply det_ne_zero_of_fundamentalGroup_map_injective p A hp
  intro u v huv
  apply hinj
  let tr : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p) :=
    ⟨fun x => c + x, continuous_const.add continuous_id⟩
  change Path.Homotopic.Quotient.map u (tr.comp (integerMatrixMap p A)) =
    Path.Homotopic.Quotient.map v (tr.comp (integerMatrixMap p A))
  rw [Path.Homotopic.Quotient.map_comp, Path.Homotopic.Quotient.map_comp]
  exact congrArg (fun q => Path.Homotopic.Quotient.map q tr) huv

end PoincareConjecture.M76.LinearTorus
