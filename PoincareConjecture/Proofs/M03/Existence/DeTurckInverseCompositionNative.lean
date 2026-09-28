import PoincareConjecture.Proofs.M03.Existence.DeTurckTameCompositionNative
import PoincareConjecture.Proofs.M03.Existence.FrameDeTurckDerivativeNative
import PoincareConjecture.Proofs.M03.Existence.CoordinateEllipticityNative
import Mathlib.Geometry.Manifold.BumpFunction








set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.DeTurckInverseCompositionNative

open TensorProbeNative DeTurckTameCompositionNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type*} [Fintype iota]

theorem directionalWord_neg (F : iota → SmoothField (n := n) (M := M))
    (w : List iota) (f : M → ℝ) :
    directionalWord F w (fun x => -f x) = fun x => -directionalWord F w f x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [directionalWord_cons, ih, scalarDirectional_neg]

private theorem smooth_sum {jota : Type*} (s : Finset jota) (f : jota → M → ℝ)
    (hf : ∀ j ∈ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => ∑ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contMDiff_const (c := (0 : ℝ)))
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).add
      (ih (fun a ha => hf a (Finset.mem_insert_of_mem ha)))

private theorem scalarDirectional_sum {jota : Type*} (s : Finset jota)
    (V : SmoothField (n := n) (M := M)) (f : jota → M → ℝ)
    (hf : ∀ j ∈ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j)) (x : M) :
    scalarDirectional V (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, scalarDirectional V (f j) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x (V x) = 0
    rw [mfderiv_const, ContinuousLinearMap.zero_apply]
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have ht := smooth_sum s f (fun a ha => hf a (Finset.mem_insert_of_mem ha))
    have hd := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (V x))
      (mfderiv_add ((hf j (Finset.mem_insert_self j s)).mdifferentiable (by simp) x)
        (ht.mdifferentiable (by simp) x))
    change scalarDirectional V (fun y => f j y + ∑ a ∈ s, f a y) x =
      scalarDirectional V (f j) x + scalarDirectional V (fun y => ∑ a ∈ s, f a y) x at hd
    rw [hd, ih (fun a ha => hf a (Finset.mem_insert_of_mem ha))]

theorem directionalWord_sum {jota : Type*} (s : Finset jota)
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota)
    (f : jota → M → ℝ)
    (hf : ∀ j ∈ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j)) (x : M) :
    directionalWord F w (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, directionalWord F w (f j) x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    have heq : directionalWord F w (fun y => ∑ j ∈ s, f j y) =
        fun y => ∑ j ∈ s, directionalWord F w (f j) y := funext ih
    rw [directionalWord_cons, heq, scalarDirectional_sum]
    · rfl
    · exact fun j hj => directionalWord_contMDiff F w (hf j hj)

private theorem norm_list_sum_le {jota : Type*} (l : List jota) (f : jota → ℝ)
    {C : ℝ} (hf : ∀ j ∈ l, ‖f j‖ ≤ C) :
    ‖(l.map f).sum‖ ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h := (norm_add_le (f j) ((l.map f).sum)).trans
      (add_le_add (hf j List.mem_cons_self)
        (ih (fun a ha => hf a (List.mem_cons_of_mem j ha))))
    nlinarith only [h]

theorem norm_directionalWord_mul_le
    (F : iota → SmoothField (n := n) (M := M)) (k : ℕ) (w : List iota)
    (hw : w.length ≤ k) {f g : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ v : List iota, v.length ≤ k → ∀ x, ‖directionalWord F v f x‖ ≤ A)
    (hgbound : ∀ v : List iota, v.length ≤ k → ∀ x, ‖directionalWord F v g x‖ ≤ B)
    (x : M) :
    ‖directionalWord F w (fun y => f y * g y) x‖ ≤ (2 : ℝ) ^ k * A * B := by
  rw [directionalWord_mul F w hf hg x]
  have hterm (p : List iota × List iota) (hp : p ∈ splitDirectionalWord w) :
      ‖directionalWord F p.1 f x * directionalWord F p.2 g x‖ ≤ A * B := by
    have hlength := splitDirectionalWord_order w p hp
    rw [norm_mul]
    exact mul_le_mul (hfbound p.1 (by omega) x) (hgbound p.2 (by omega) x)
      (norm_nonneg _) hA
  have hsum := norm_list_sum_le (splitDirectionalWord w)
    (fun p => directionalWord F p.1 f x * directionalWord F p.2 g x) hterm
  rw [splitDirectionalWord_length, Nat.cast_pow, Nat.cast_ofNat] at hsum
  apply hsum.trans
  have hp : (2 : ℝ) ^ w.length ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hw
  nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hA hB)]

theorem inverse_entry_contMDiff (G : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x a b => G x a b))
    (hdet : ∀ x, (G x).det ≠ 0) (i j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => (G x)⁻¹ i j) := by
  intro x
  have hinv : ContMDiffAt 𝓘(ℝ, Fin n → Fin n → ℝ)
      𝓘(ℝ, Fin n → Fin n → ℝ) ∞ DeTurckNative.matrixInverseEntries
      (fun a b => G x a b) :=
    (DeTurckNative.contDiffAt_matrixInverseEntries_infty _ (hdet x)).contMDiffAt
  have hc := hinv.comp (f := fun y a b => G y a b) x (hG x)
  exact contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hc i) j


theorem matrix_inv_sub_inv_entry
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (i j : Fin n) :
    A⁻¹ i j - B⁻¹ i j =
      ∑ u, ∑ v, A⁻¹ i u * (B u v - A u v) * B⁻¹ v j := by
  have hUA : IsUnit A := A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hA)
  have hUB : IsUnit B := B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hB)
  have hmat := Matrix.inv_sub_inv (A := A) (B := B)
    (show IsUnit A ↔ IsUnit B from ⟨fun _ => hUB, fun _ => hUA⟩)
  calc
    _ = (A⁻¹ * (B - A) * B⁻¹) i j :=
      congrArg (fun C : Matrix (Fin n) (Fin n) ℝ => C i j) hmat
    _ = ∑ v, ∑ u, A⁻¹ i u * (B u v - A u v) * B⁻¹ v j := by
      simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
    _ = _ := Finset.sum_comm

theorem directionalWord_inverse_append
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota) (a : iota)
    (G : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j))
    (hdet : ∀ x, (G x).det ≠ 0) (i j : Fin n) (x : M) :
    directionalWord F (w ++ [a]) (fun y => (G y)⁻¹ i j) x =
      -∑ u, ∑ v, directionalWord F w
        (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun z => G z u v) y *
          (G y)⁻¹ v j) x := by
  have hentry (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => G y u v) :=
    fun y => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hG y) u) v
  have heq : directionalWord F [a] (fun y => (G y)⁻¹ i j) =
      fun y => -∑ u, ∑ v, (G y)⁻¹ i u *
        scalarDirectional (F a) (fun z => G z u v) y * (G y)⁻¹ v j := by
    funext y
    exact DeTurckNative.mvfderiv_matrix_inv_entry G ((hG y).of_le (by simp))
      (hdet y) (F a y) i j
  have hterm (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun z => G z u v) y *
        (G y)⁻¹ v j) :=
    ((inverse_entry_contMDiff G hG hdet i u).mul
      (contMDiff_directional (hentry u v) (F a))).mul
        (inverse_entry_contMDiff G hG hdet v j)
  rw [directionalWord_append, heq, directionalWord_neg]
  apply congrArg Neg.neg
  calc
    _ = ∑ u, directionalWord F w
        (fun y => ∑ v, (G y)⁻¹ i u *
          scalarDirectional (F a) (fun z => G z u v) y * (G y)⁻¹ v j) x :=
      directionalWord_sum Finset.univ F w _
        (fun u _ => smooth_sum Finset.univ _ (fun v _ => hterm u v)) x
    _ = _ := Finset.sum_congr rfl
      (fun u _ => directionalWord_sum Finset.univ F w _ (fun v _ => hterm u v) x)


def inverseSupBound (n k : ℕ) (A I : ℝ) : ℝ :=
  match k with
  | 0 => I
  | q + 1 => inverseSupBound n q A I +
      (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * q) * A * inverseSupBound n q A I ^ 2

theorem inverseSupBound_nonneg (n k : ℕ) {A I : ℝ} (hA : 0 ≤ A) (hI : 0 ≤ I) :
    0 ≤ inverseSupBound n k A I := by
  induction k with
  | zero => exact hI
  | succ k ih => dsimp only [inverseSupBound]; positivity

theorem norm_directionalWord_inverse_le
    (F : iota → SmoothField (n := n) (M := M)) (k : ℕ)
    (G : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j))
    (hdet : ∀ x, (G x).det ≠ 0) {A I : ℝ} (hA : 0 ≤ A) (hI : 0 ≤ I)
    (hGbound : ∀ w : List iota, w.length ≤ k → ∀ (u v : Fin n) (x : M),
      ‖directionalWord F w (fun y => G y u v) x‖ ≤ A)
    (hInv : ∀ (u v : Fin n) (x : M), ‖(G x)⁻¹ u v‖ ≤ I) :
    ∀ w : List iota, w.length ≤ k → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => (G y)⁻¹ i j) x‖ ≤ inverseSupBound n k A I := by
  induction k with
  | zero =>
    intro w hw i j x
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    simpa [hw0, inverseSupBound] using hInv i j x
  | succ k ih =>
    have hprev := ih (fun w hw => hGbound w (by omega))
    let J := inverseSupBound n k A I
    have hJ : 0 ≤ J := inverseSupBound_nonneg n k hA hI
    have hstep : J ≤ inverseSupBound n (k + 1) A I := by
      dsimp only [inverseSupBound]
      have hpos : 0 ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * k) * A * J ^ 2 := by positivity
      exact le_add_of_nonneg_right hpos
    intro w hw i j x
    induction w using List.reverseRecOn with
    | nil => exact (hprev [] (by simp) i j x).trans hstep
    | append_singleton w a _ =>
      have hwk : w.length ≤ k := by
        simp only [List.length_append, List.length_singleton] at hw
        omega
      have hentry (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => G y u v) :=
        fun y => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hG y) u) v
      have hderiv (u v : Fin n) (z : List iota) (hz : z.length ≤ k) (y : M) :
          ‖directionalWord F z (scalarDirectional (F a) (fun z => G z u v)) y‖ ≤ A := by
        have h := hGbound (z ++ [a]) (by simp only [List.length_append, List.length_singleton]; omega)
          u v y
        simpa only [directionalWord_append, directionalWord_cons, directionalWord_nil] using h
      have hterm (u v : Fin n) :
          ‖directionalWord F w
            (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun z => G z u v) y *
              (G y)⁻¹ v j) x‖ ≤ (2 : ℝ) ^ (2 * k) * A * J ^ 2 := by
        have hleft : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
            (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun z => G z u v) y) :=
          (inverse_entry_contMDiff G hG hdet i u).mul
            (contMDiff_directional (hentry u v) (F a))
        have hleftBound (z : List iota) (hz : z.length ≤ k) (y : M) :
            ‖directionalWord F z
              (fun p => (G p)⁻¹ i u * scalarDirectional (F a) (fun t => G t u v) p) y‖ ≤
              (2 : ℝ) ^ k * J * A :=
          norm_directionalWord_mul_le F k z hz
            (inverse_entry_contMDiff G hG hdet i u)
            (contMDiff_directional (hentry u v) (F a)) hJ hA
            (fun z hz y => hprev z hz i u y) (hderiv u v) y
        have h := norm_directionalWord_mul_le F k w hwk hleft
          (inverse_entry_contMDiff G hG hdet v j) (by positivity) hJ hleftBound
          (fun z hz y => hprev z hz v j y) x
        rw [show 2 * k = k + k by omega, pow_add]
        convert h using 1 <;> ring
      rw [directionalWord_inverse_append F w a G hG hdet i j x, norm_neg]
      calc
        _ ≤ ∑ u : Fin n, ∑ v : Fin n,
            ‖directionalWord F w
              (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun z => G z u v) y *
                (G y)⁻¹ v j) x‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u _ => norm_sum_le _ _))
        _ ≤ ∑ _u : Fin n, ∑ _v : Fin n, (2 : ℝ) ^ (2 * k) * A * J ^ 2 :=
          Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hterm u v))
        _ ≤ inverseSupBound n (k + 1) A I := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          change (n : ℝ) * ((n : ℝ) * ((2 : ℝ) ^ (2 * k) * A * J ^ 2)) ≤
            J + (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * k) * A * J ^ 2
          nlinarith only [hJ]


theorem directionalWord_inverse_sub
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota)
    (G H : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j))
    (hH : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => H x i j))
    (hGdet : ∀ x, (G x).det ≠ 0) (hHdet : ∀ x, (H x).det ≠ 0)
    (i j : Fin n) (x : M) :
    directionalWord F w (fun y => (G y)⁻¹ i j - (H y)⁻¹ i j) x =
      ∑ u, ∑ v, directionalWord F w
        (fun y => (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j) x := by
  have hdiff (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => H y u v - G y u v) :=
    ContMDiff.sub
      (fun y => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hH y) u) v)
      (fun y => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hG y) u) v)
  have hterm (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j) :=
    ((inverse_entry_contMDiff G hG hGdet i u).mul (hdiff u v)).mul
      (inverse_entry_contMDiff H hH hHdet v j)
  have heq : (fun y => (G y)⁻¹ i j - (H y)⁻¹ i j) =
      (fun y => ∑ u, ∑ v, (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j) :=
    funext (fun y => matrix_inv_sub_inv_entry (hGdet y) (hHdet y) i j)
  rw [heq]
  calc
    _ = ∑ u, directionalWord F w
        (fun y => ∑ v, (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j) x :=
      directionalWord_sum Finset.univ F w _
        (fun u _ => smooth_sum Finset.univ _ (fun v _ => hterm u v)) x
    _ = _ := Finset.sum_congr rfl
      (fun u _ => directionalWord_sum Finset.univ F w _ (fun v _ => hterm u v) x)


theorem norm_directionalWord_inverse_sub_le
    (F : iota → SmoothField (n := n) (M := M)) (k : ℕ)
    (G H : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j))
    (hH : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => H x i j))
    (hGdet : ∀ x, (G x).det ≠ 0) (hHdet : ∀ x, (H x).det ≠ 0)
    {J d : ℝ} (hJ : 0 ≤ J) (hd : 0 ≤ d)
    (hIG : ∀ w : List iota, w.length ≤ k → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => (G y)⁻¹ i j) x‖ ≤ J)
    (hIH : ∀ w : List iota, w.length ≤ k → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => (H y)⁻¹ i j) x‖ ≤ J)
    (hD : ∀ w : List iota, w.length ≤ k → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => H y i j - G y i j) x‖ ≤ d) :
    ∀ w : List iota, w.length ≤ k → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => (G y)⁻¹ i j - (H y)⁻¹ i j) x‖ ≤
        (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * k) * J ^ 2 * d := by
  intro w hw i j x
  have hdiff (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => H y u v - G y u v) :=
    ContMDiff.sub
      (fun y => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hH y) u) v)
      (fun y => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hG y) u) v)
  have hterm (u v : Fin n) :
      ‖directionalWord F w
        (fun y => (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j) x‖ ≤
        (2 : ℝ) ^ (2 * k) * J ^ 2 * d := by
    have hleft : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => (G y)⁻¹ i u * (H y u v - G y u v)) :=
      (inverse_entry_contMDiff G hG hGdet i u).mul (hdiff u v)
    have hleftBound (z : List iota) (hz : z.length ≤ k) (y : M) :
        ‖directionalWord F z
          (fun p => (G p)⁻¹ i u * (H p u v - G p u v)) y‖ ≤
          (2 : ℝ) ^ k * J * d :=
      norm_directionalWord_mul_le F k z hz
        (inverse_entry_contMDiff G hG hGdet i u) (hdiff u v) hJ hd
        (fun z hz y => hIG z hz i u y) (fun z hz y => hD z hz u v y) y
    have h := norm_directionalWord_mul_le F k w hw hleft
      (inverse_entry_contMDiff H hH hHdet v j) (by positivity) hJ hleftBound
      (fun z hz y => hIH z hz v j y) x
    rw [show 2 * k = k + k by omega, pow_add]
    convert h using 1 <;> ring
  rw [directionalWord_inverse_sub F w G H hG hH hGdet hHdet i j x]
  calc
    _ ≤ ∑ u : Fin n, ∑ v : Fin n, ‖directionalWord F w
        (fun y => (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j) x‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u _ => norm_sum_le _ _))
    _ ≤ ∑ _u : Fin n, ∑ _v : Fin n, (2 : ℝ) ^ (2 * k) * J ^ 2 * d :=
      Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hterm u v))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

section InverseL2

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsFiniteMeasure μ]

private theorem memLp_continuous {f : M → ℝ} (hf : Continuous f) : MemLp f 2 μ :=
  ContinuousMap.memLp (p := 2) (μ := μ) ℝ (⟨f, hf⟩ : C(M, ℝ))

private theorem lpNorm_le_sup {f : M → ℝ} {J : ℝ} (hJ : 0 ≤ J)
    (hf : ∀ x, ‖f x‖ ≤ J) :
    lpNorm f 2 μ ≤ J * lpNorm (fun _ : M => (1 : ℝ)) 2 μ := by
  calc
    _ ≤ lpNorm (fun _ : M => J) 2 μ := by
      apply lpNorm_mono_real (memLp_const J)
      exact hf
    _ = _ := by
      have heq : (fun _ : M => J) = J • (fun _ : M => (1 : ℝ)) := by
        funext x
        simp
      rw [heq, lpNorm_const_smul]
      simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hJ]

private theorem lpNorm_native_mul_le
    (F : iota → SmoothField (n := n) (M := M)) (k : ℕ) (w : List iota)
    (hw : w.length ≤ k) {f g : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ g)
    {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfLow : ∀ v : List iota, v.length ≤ k / 2 → ∀ x, ‖directionalWord F v f x‖ ≤ a)
    (hgLow : ∀ v : List iota, v.length ≤ k / 2 → ∀ x, ‖directionalWord F v g x‖ ≤ b)
    (hfHigh : ∀ v : List iota, v.length ≤ k → lpNorm (directionalWord F v f) 2 μ ≤ A)
    (hgHigh : ∀ v : List iota, v.length ≤ k → lpNorm (directionalWord F v g) 2 μ ≤ B) :
    lpNorm (directionalWord F w (fun x => f x * g x)) 2 μ ≤
      (2 : ℝ) ^ k * (a * B + b * A) := by
  apply (lpNorm_directionalWord_mul_le μ F k w hw hf hg ha hb hA hB
    hfLow hgLow hfHigh hgHigh).trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw)
    (add_nonneg (mul_nonneg ha hB) (mul_nonneg hb hA))

private theorem lpNorm_fintype_sum_le {jota : Type*} [Fintype jota]
    (f : jota → M → ℝ) (hf : ∀ j, Continuous (f j)) :
    lpNorm (fun x => ∑ j, f j x) 2 μ ≤ ∑ j, lpNorm (f j) 2 μ := by
  have h := lpNorm_sum_le (s := Finset.univ)
    (fun j _ => memLp_continuous μ (hf j)) (by norm_num : (1 : ENNReal) ≤ 2)
  have heq : (fun x => ∑ j, f j x) = ∑ j, f j := by
    funext x
    simp only [Finset.sum_apply]
  rw [heq]
  exact h

def inverseL2Bound (n k : ℕ) (A J : ℝ) : ℝ :=
  match k with
  | 0 => J
  | q + 1 => inverseL2Bound n q A J +
      (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * q) *
        (2 * A * J * inverseL2Bound n q A J + J ^ 2)

theorem inverseL2Bound_nonneg (n k : ℕ) {A J : ℝ} (hA : 0 ≤ A) (hJ : 0 ≤ J) :
    0 ≤ inverseL2Bound n k A J := by
  induction k with
  | zero => exact hJ
  | succ k ih => dsimp only [inverseL2Bound]; positivity


theorem lpNorm_directionalWord_inverse_le_of_low
    (F : iota → SmoothField (n := n) (M := M)) (k : ℕ)
    (G : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j))
    (hdet : ∀ x, (G x).det ≠ 0) {A J H : ℝ}
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hH : 0 ≤ H)
    (hGLow : ∀ w : List iota, w.length ≤ k / 2 + 1 → ∀ (u v : Fin n) (x : M),
      ‖directionalWord F w (fun y => G y u v) x‖ ≤ A)
    (hILow : ∀ w : List iota, w.length ≤ k / 2 + 1 → ∀ (u v : Fin n) (x : M),
      ‖directionalWord F w (fun y => (G y)⁻¹ u v) x‖ ≤ J)
    (hGHigh : ∀ w : List iota, w.length ≤ k → ∀ u v : Fin n,
      lpNorm (directionalWord F w (fun y => G y u v)) 2 μ ≤ H) :
    ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (G y)⁻¹ i j)) 2 μ ≤
        inverseL2Bound n k A J * (lpNorm (fun _ : M => (1 : ℝ)) 2 μ + H) := by
  let U := lpNorm (fun _ : M => (1 : ℝ)) 2 μ + H
  have hU : 0 ≤ U := add_nonneg lpNorm_nonneg hH
  have hHU : H ≤ U := le_add_of_nonneg_left lpNorm_nonneg
  have hentry (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => G y u v) :=
    fun y => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hG y) u) v
  have hall (q : ℕ) : q ≤ k → ∀ w : List iota, w.length ≤ q → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (G y)⁻¹ i j)) 2 μ ≤
        inverseL2Bound n q A J * U := by
    induction q with
    | zero =>
      intro _ w hw i j
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp only [hw0, directionalWord_nil, inverseL2Bound]
      exact (lpNorm_le_sup μ hJ (hILow [] (by simp) i j)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hH) hJ)
    | succ q ih =>
      intro hq w hw i j
      let K := inverseL2Bound n q A J
      have hK : 0 ≤ K := inverseL2Bound_nonneg n q hA hJ
      have hprev := ih (by omega)
      have hstep : K * U ≤ inverseL2Bound n (q + 1) A J * U := by
        apply mul_le_mul_of_nonneg_right _ hU
        change K ≤ K + _
        apply le_add_of_nonneg_right
        positivity
      induction w using List.reverseRecOn with
      | nil => exact (hprev [] (by simp) i j).trans hstep
      | append_singleton w a _ =>
        have hwq : w.length ≤ q := by
          simp only [List.length_append, List.length_singleton] at hw
          omega
        have hIL (u v : Fin n) (z : List iota) (hz : z.length ≤ q / 2) (x : M) :
            ‖directionalWord F z (fun y => (G y)⁻¹ u v) x‖ ≤ J :=
          hILow z (by omega) u v x
        have hDL (u v : Fin n) (z : List iota) (hz : z.length ≤ q / 2) (x : M) :
            ‖directionalWord F z (scalarDirectional (F a) (fun y => G y u v)) x‖ ≤ A := by
          have h := hGLow (z ++ [a])
            (by simp only [List.length_append, List.length_singleton]; omega) u v x
          simpa only [directionalWord_append, directionalWord_cons, directionalWord_nil] using h
        have hDH (u v : Fin n) (z : List iota) (hz : z.length ≤ q) :
            lpNorm (directionalWord F z (scalarDirectional (F a) (fun y => G y u v))) 2 μ ≤ H := by
          have h := hGHigh (z ++ [a])
            (by simp only [List.length_append, List.length_singleton]; omega) u v
          simpa only [directionalWord_append, directionalWord_cons, directionalWord_nil] using h
        have hterm (u v : Fin n) :
            lpNorm (directionalWord F w
              (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun z => G z u v) y *
                (G y)⁻¹ v j)) 2 μ ≤
              ((2 : ℝ) ^ (2 * q) * (2 * A * J * K + J ^ 2)) * U := by
          have hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
              (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun z => G z u v) y) :=
            (inverse_entry_contMDiff G hG hdet i u).mul
              (contMDiff_directional (hentry u v) (F a))
          have hlow (z : List iota) (hz : z.length ≤ q / 2) (x : M) :
              ‖directionalWord F z
                (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun p => G p u v) y) x‖ ≤
                (2 : ℝ) ^ q * J * A := by
            apply (norm_directionalWord_mul_le F (q / 2) z hz
              (inverse_entry_contMDiff G hG hdet i u)
              (contMDiff_directional (hentry u v) (F a)) hJ hA
              (hIL i u) (hDL u v) x).trans
            have hp : (2 : ℝ) ^ (q / 2) ≤ 2 ^ q :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hJ) hA
          have hhigh (z : List iota) (hz : z.length ≤ q) :
              lpNorm (directionalWord F z
                (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun p => G p u v) y)) 2 μ ≤
                ((2 : ℝ) ^ q * (J + A * K)) * U := by
            have ht := lpNorm_native_mul_le μ F q z hz
              (inverse_entry_contMDiff G hG hdet i u)
              (contMDiff_directional (hentry u v) (F a)) hJ hA
              (mul_nonneg hK hU) hH (hIL i u) (hDL u v)
              (fun z hz => hprev z hz i u) (hDH u v)
            apply ht.trans
            have hjh := mul_le_mul_of_nonneg_left hHU hJ
            nlinarith [mul_le_mul_of_nonneg_left hjh (show 0 ≤ (2 : ℝ) ^ q by positivity)]
          have ht := lpNorm_native_mul_le μ F q w hwq hsmooth
            (inverse_entry_contMDiff G hG hdet v j) (by positivity) hJ
            (by positivity) (mul_nonneg hK hU) hlow (hIL v j) hhigh
            (fun z hz => hprev z hz v j)
          rw [show 2 * q = q + q by omega, pow_add]
          convert ht using 1 <;> ring
        have htermSmooth (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
            (directionalWord F w (fun y => (G y)⁻¹ i u *
              scalarDirectional (F a) (fun z => G z u v) y * (G y)⁻¹ v j)) :=
          directionalWord_contMDiff F w
            (((inverse_entry_contMDiff G hG hdet i u).mul
              (contMDiff_directional (hentry u v) (F a))).mul
                (inverse_entry_contMDiff G hG hdet v j))
        have heq : directionalWord F (w ++ [a]) (fun y => (G y)⁻¹ i j) =
            fun x => -∑ u, ∑ v, directionalWord F w
              (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun z => G z u v) y *
                (G y)⁻¹ v j) x :=
          funext (directionalWord_inverse_append F w a G hG hdet i j)
        rw [heq, lpNorm_fun_neg]
        calc
          _ ≤ ∑ u : Fin n, ∑ v : Fin n, lpNorm (directionalWord F w
                (fun y => (G y)⁻¹ i u * scalarDirectional (F a) (fun z => G z u v) y *
                  (G y)⁻¹ v j)) 2 μ := by
            apply (lpNorm_fintype_sum_le μ _
              (fun u => (smooth_sum Finset.univ _ (fun v _ => htermSmooth u v)).continuous)).trans
            exact Finset.sum_le_sum (fun u _ => lpNorm_fintype_sum_le μ _
              (fun v => (htermSmooth u v).continuous))
          _ ≤ ∑ _u : Fin n, ∑ _v : Fin n,
              ((2 : ℝ) ^ (2 * q) * (2 * A * J * K + J ^ 2)) * U :=
            Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hterm u v))
          _ ≤ inverseL2Bound n (q + 1) A J * U := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            change (n : ℝ) * ((n : ℝ) *
                (((2 : ℝ) ^ (2 * q) * (2 * A * J * K + J ^ 2)) * U)) ≤
              (K + (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * q) * (2 * A * J * K + J ^ 2)) * U
            nlinarith only [mul_nonneg hK hU]
  exact hall k le_rfl



theorem lpNorm_directionalWord_inverse_le
    (F : iota → SmoothField (n := n) (M := M)) (k : ℕ)
    (G : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j))
    (hdet : ∀ x, (G x).det ≠ 0) {A I H : ℝ}
    (hA : 0 ≤ A) (hI : 0 ≤ I) (hH : 0 ≤ H)
    (hGLow : ∀ w : List iota, w.length ≤ k / 2 + 1 → ∀ (u v : Fin n) (x : M),
      ‖directionalWord F w (fun y => G y u v) x‖ ≤ A)
    (hInv : ∀ (u v : Fin n) (x : M), ‖(G x)⁻¹ u v‖ ≤ I)
    (hGHigh : ∀ w : List iota, w.length ≤ k → ∀ u v : Fin n,
      lpNorm (directionalWord F w (fun y => G y u v)) 2 μ ≤ H) :
    ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (G y)⁻¹ i j)) 2 μ ≤
        inverseL2Bound n k A (inverseSupBound n (k / 2 + 1) A I) *
          (lpNorm (fun _ : M => (1 : ℝ)) 2 μ + H) :=
  lpNorm_directionalWord_inverse_le_of_low μ F k G hG hdet hA
    (inverseSupBound_nonneg n (k / 2 + 1) hA hI) hH hGLow
    (norm_directionalWord_inverse_le F (k / 2 + 1) G hG hdet hA hI hGLow hInv) hGHigh


theorem lpNorm_directionalWord_inverse_sub_le_of_bounds
    (F : iota → SmoothField (n := n) (M := M)) (k : ℕ)
    (G H : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j))
    (hH : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => H x i j))
    (hGdet : ∀ x, (G x).det ≠ 0) (hHdet : ∀ x, (H x).det ≠ 0)
    {J d D UG UH : ℝ} (hJ : 0 ≤ J) (hd : 0 ≤ d) (hD : 0 ≤ D)
    (hUG : 0 ≤ UG) (hUH : 0 ≤ UH)
    (hIGLow : ∀ w : List iota, w.length ≤ k / 2 → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => (G y)⁻¹ i j) x‖ ≤ J)
    (hIHLow : ∀ w : List iota, w.length ≤ k / 2 → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => (H y)⁻¹ i j) x‖ ≤ J)
    (hDLow : ∀ w : List iota, w.length ≤ k / 2 → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => H y i j - G y i j) x‖ ≤ d)
    (hIGHigh : ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (G y)⁻¹ i j)) 2 μ ≤ UG)
    (hIHHigh : ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (H y)⁻¹ i j)) 2 μ ≤ UH)
    (hDHigh : ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => H y i j - G y i j)) 2 μ ≤ D) :
    ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (G y)⁻¹ i j - (H y)⁻¹ i j)) 2 μ ≤
        (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * k) * (J ^ 2 * D + J * d * (UG + UH)) := by
  intro w hw i j
  have hdiff (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => H y u v - G y u v) :=
    ContMDiff.sub
      (fun y => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hH y) u) v)
      (fun y => contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hG y) u) v)
  have hterm (u v : Fin n) :
      lpNorm (directionalWord F w
        (fun y => (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j)) 2 μ ≤
        (2 : ℝ) ^ (2 * k) * (J ^ 2 * D + J * d * (UG + UH)) := by
    have hleft : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => (G y)⁻¹ i u * (H y u v - G y u v)) :=
      (inverse_entry_contMDiff G hG hGdet i u).mul (hdiff u v)
    have hleftLow (z : List iota) (hz : z.length ≤ k / 2) (x : M) :
        ‖directionalWord F z
          (fun y => (G y)⁻¹ i u * (H y u v - G y u v)) x‖ ≤
          (2 : ℝ) ^ k * J * d := by
      apply (norm_directionalWord_mul_le F (k / 2) z hz
        (inverse_entry_contMDiff G hG hGdet i u) (hdiff u v) hJ hd
        (fun z hz x => hIGLow z hz i u x) (fun z hz x => hDLow z hz u v x) x).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (by omega : k / 2 ≤ k)) hJ) hd
    have hleftHigh (z : List iota) (hz : z.length ≤ k) :
        lpNorm (directionalWord F z
          (fun y => (G y)⁻¹ i u * (H y u v - G y u v))) 2 μ ≤
          (2 : ℝ) ^ k * (J * D + d * UG) :=
      lpNorm_native_mul_le μ F k z hz
        (inverse_entry_contMDiff G hG hGdet i u) (hdiff u v) hJ hd hUG hD
        (fun z hz x => hIGLow z hz i u x) (fun z hz x => hDLow z hz u v x)
        (fun z hz => hIGHigh z hz i u) (fun z hz => hDHigh z hz u v)
    have h := lpNorm_native_mul_le μ F k w hw hleft
      (inverse_entry_contMDiff H hH hHdet v j) (by positivity) hJ
      (by positivity) hUH hleftLow (fun z hz x => hIHLow z hz v j x)
      hleftHigh (fun z hz => hIHHigh z hz v j)
    rw [show 2 * k = k + k by omega, pow_add]
    convert h using 1 <;> ring
  have htermSmooth (u v : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (directionalWord F w
        (fun y => (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j)) :=
    directionalWord_contMDiff F w
      (((inverse_entry_contMDiff G hG hGdet i u).mul (hdiff u v)).mul
        (inverse_entry_contMDiff H hH hHdet v j))
  have heq : directionalWord F w (fun y => (G y)⁻¹ i j - (H y)⁻¹ i j) =
      fun x => ∑ u, ∑ v, directionalWord F w
        (fun y => (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j) x :=
    funext (directionalWord_inverse_sub F w G H hG hH hGdet hHdet i j)
  rw [heq]
  calc
    _ ≤ ∑ u : Fin n, ∑ v : Fin n, lpNorm (directionalWord F w
        (fun y => (G y)⁻¹ i u * (H y u v - G y u v) * (H y)⁻¹ v j)) 2 μ := by
      apply (lpNorm_fintype_sum_le μ _
        (fun u => (smooth_sum Finset.univ _ (fun v _ => htermSmooth u v)).continuous)).trans
      exact Finset.sum_le_sum (fun u _ => lpNorm_fintype_sum_le μ _
        (fun v => (htermSmooth u v).continuous))
    _ ≤ ∑ _u : Fin n, ∑ _v : Fin n,
        (2 : ℝ) ^ (2 * k) * (J ^ 2 * D + J * d * (UG + UH)) :=
      Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hterm u v))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring


theorem lpNorm_directionalWord_inverse_sub_le
    (F : iota → SmoothField (n := n) (M := M)) (k : ℕ)
    (G H : M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => G x i j))
    (hH : ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞ (fun x i j => H x i j))
    (hGdet : ∀ x, (G x).det ≠ 0) (hHdet : ∀ x, (H x).det ≠ 0)
    {A I HG HH d D : ℝ} (hA : 0 ≤ A) (hI : 0 ≤ I)
    (hHG : 0 ≤ HG) (hHH : 0 ≤ HH) (hd : 0 ≤ d) (hD : 0 ≤ D)
    (hGLow : ∀ w : List iota, w.length ≤ k / 2 + 1 → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => G y i j) x‖ ≤ A)
    (hHLow : ∀ w : List iota, w.length ≤ k / 2 + 1 → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => H y i j) x‖ ≤ A)
    (hGInv : ∀ (i j : Fin n) (x : M), ‖(G x)⁻¹ i j‖ ≤ I)
    (hHInv : ∀ (i j : Fin n) (x : M), ‖(H x)⁻¹ i j‖ ≤ I)
    (hGHigh : ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => G y i j)) 2 μ ≤ HG)
    (hHHigh : ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => H y i j)) 2 μ ≤ HH)
    (hDLow : ∀ w : List iota, w.length ≤ k / 2 → ∀ (i j : Fin n) (x : M),
      ‖directionalWord F w (fun y => H y i j - G y i j) x‖ ≤ d)
    (hDHigh : ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => H y i j - G y i j)) 2 μ ≤ D) :
    let J := inverseSupBound n (k / 2 + 1) A I
    let C := inverseL2Bound n k A J
    ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (G y)⁻¹ i j - (H y)⁻¹ i j)) 2 μ ≤
        (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * k) *
          (J ^ 2 * D + J * d * C *
            (2 * lpNorm (fun _ : M => (1 : ℝ)) 2 μ + HG + HH)) := by
  dsimp only
  let J := inverseSupBound n (k / 2 + 1) A I
  let C := inverseL2Bound n k A J
  let V := lpNorm (fun _ : M => (1 : ℝ)) 2 μ
  have hJ : 0 ≤ J := inverseSupBound_nonneg n (k / 2 + 1) hA hI
  have hC : 0 ≤ C := inverseL2Bound_nonneg n k hA hJ
  have hV : 0 ≤ V := lpNorm_nonneg
  have hIGLow := norm_directionalWord_inverse_le F (k / 2 + 1) G hG hGdet
    hA hI hGLow hGInv
  have hIHLow := norm_directionalWord_inverse_le F (k / 2 + 1) H hH hHdet
    hA hI hHLow hHInv
  have hIGHigh : ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (G y)⁻¹ i j)) 2 μ ≤ C * (V + HG) :=
    lpNorm_directionalWord_inverse_le μ F k G hG hGdet hA hI hHG hGLow hGInv hGHigh
  have hIHHigh : ∀ w : List iota, w.length ≤ k → ∀ i j : Fin n,
      lpNorm (directionalWord F w (fun y => (H y)⁻¹ i j)) 2 μ ≤ C * (V + HH) :=
    lpNorm_directionalWord_inverse_le μ F k H hH hHdet hA hI hHH hHLow hHInv hHHigh
  intro w hw i j
  have h := lpNorm_directionalWord_inverse_sub_le_of_bounds μ F k G H hG hH hGdet hHdet
    hJ hd hD (mul_nonneg hC (add_nonneg hV hHG)) (mul_nonneg hC (add_nonneg hV hHH))
    (fun w hw i j x => hIGLow w (by omega) i j x)
    (fun w hw i j x => hIHLow w (by omega) i j x)
    hDLow hIGHigh hIHHigh hDHigh w hw i j
  change _ ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ (2 * k) *
    (J ^ 2 * D + J * d * C * (2 * V + HG + HH))
  convert h using 1 <;> ring

end InverseL2

section PositiveExtension


def positiveMatrixExtension (chi : M → ℝ) (G : M → Matrix (Fin n) (Fin n) ℝ)
    (x : M) : Matrix (Fin n) (Fin n) ℝ :=
  chi x • G x + (1 - chi x) • 1

theorem positiveMatrixExtension_posDef (chi : M → ℝ)
    (G : M → Matrix (Fin n) (Fin n) ℝ)
    (hzero : ∀ x, 0 ≤ chi x) (hone : ∀ x, chi x ≤ 1)
    (hG : ∀ x, chi x ≠ 0 → (G x).PosDef) (x : M) :
    (positiveMatrixExtension chi G x).PosDef := by
  by_cases hx : chi x = 0
  · simpa only [positiveMatrixExtension, hx, zero_smul, sub_zero, one_smul, zero_add]
      using (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef)
  · exact ((hG x hx).smul (lt_of_le_of_ne (hzero x) (Ne.symm hx))).add_posSemidef
      ((Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef).smul
        (sub_nonneg.mpr (hone x)))


theorem positiveMatrixExtension_contMDiff (chi : M → ℝ)
    (G : M → Matrix (Fin n) (Fin n) ℝ) {U : Set M} (hU : IsOpen U)
    (hchi : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ chi) (hsupp : tsupport chi ⊆ U)
    (hG : ∀ i j : Fin n,
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => G x i j) U) :
    ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => positiveMatrixExtension chi G x i j) := by
  have hprod (i j : Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => chi x * G x i j) := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxU := hsupp (tsupport_mul_subset_left hx)
    exact (hchi x).mul ((hG i j).contMDiffAt (hU.mem_nhds hxU))
  intro x
  apply contMDiffAt_pi_space.mpr
  intro i
  apply contMDiffAt_pi_space.mpr
  intro j
  change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
    (fun y => chi y * G y i j + (1 - chi y) * (1 : Matrix (Fin n) (Fin n) ℝ) i j) x
  exact (hprod i j x).add ((contMDiffAt_const.sub (hchi x)).mul contMDiffAt_const)

theorem positiveMatrixExtension_sub (chi : M → ℝ)
    (G H : M → Matrix (Fin n) (Fin n) ℝ) (x : M) :
    positiveMatrixExtension chi G x - positiveMatrixExtension chi H x =
      chi x • (G x - H x) := by
  simp only [positiveMatrixExtension, smul_sub]
  abel

theorem directionalWord_positiveMatrixExtension_sub
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota) (chi : M → ℝ)
    (G H : M → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    directionalWord F w
        (fun x => (positiveMatrixExtension chi G x - positiveMatrixExtension chi H x) i j) =
      directionalWord F w (fun x => chi x * (G x i j - H x i j)) := by
  congr 1
  funext x
  rw [positiveMatrixExtension_sub]
  rfl

theorem positiveMatrixExtension_eq_of_one (chi : M → ℝ)
    (G : M → Matrix (Fin n) (Fin n) ℝ) {x : M} (hx : chi x = 1) :
    positiveMatrixExtension chi G x = G x := by
  simp only [positiveMatrixExtension, hx, one_smul, sub_self, zero_smul, add_zero]

theorem positiveMatrixExtension_eventuallyEq (chi : M → ℝ)
    (G : M → Matrix (Fin n) (Fin n) ℝ) {x : M}
    (hchi : chi =ᶠ[𝓝 x] 1) : positiveMatrixExtension chi G =ᶠ[𝓝 x] G := by
  filter_upwards [hchi] with y hy
  exact positiveMatrixExtension_eq_of_one chi G hy


theorem directionalWord_eventuallyEq (F : iota → SmoothField (n := n) (M := M))
    (w : List iota) {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    directionalWord F w f =ᶠ[𝓝 x] directionalWord F w g := by
  induction w with
  | nil => exact h
  | cons a w ih =>
    filter_upwards [ih.eventuallyEq_nhds] with y hy
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (directionalWord F w f) y (F a y) =
      mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (directionalWord F w g) y (F a y)
    exact congrArg (fun L => L (F a y))
      (hy.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))

theorem directionalWord_positiveMatrixExtension_eq
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota)
    (chi : M → ℝ) (G : M → Matrix (Fin n) (Fin n) ℝ) {x : M}
    (hchi : chi =ᶠ[𝓝 x] 1) (i j : Fin n) :
    directionalWord F w (fun y => positiveMatrixExtension chi G y i j) x =
      directionalWord F w (fun y => G y i j) x := by
  apply (directionalWord_eventuallyEq F w ?_).eq_of_nhds
  filter_upwards [positiveMatrixExtension_eventuallyEq chi G hchi] with y hy
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hy

theorem directionalWord_positiveMatrixExtension_inv_eq
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota)
    (chi : M → ℝ) (G : M → Matrix (Fin n) (Fin n) ℝ) {x : M}
    (hchi : chi =ᶠ[𝓝 x] 1) (i j : Fin n) :
    directionalWord F w (fun y => (positiveMatrixExtension chi G y)⁻¹ i j) x =
      directionalWord F w (fun y => (G y)⁻¹ i j) x := by
  apply (directionalWord_eventuallyEq F w ?_).eq_of_nhds
  filter_upwards [positiveMatrixExtension_eventuallyEq chi G hchi] with y hy
  rw [hy]

section ChartMetric

variable [T2Space M]


def cutoffChartMetric (g : RiemannianMetric n M) (p : M)
    (b : SmoothBumpFunction (𝓡 n) p) : M → Matrix (Fin n) (Fin n) ℝ :=
  positiveMatrixExtension b
    (fun x => (DeTurckNative.frameMetricJet g (DeTurckNative.chartFrame p) x).value)

theorem cutoffChartMetric_posDef (g : RiemannianMetric n M) (p : M)
    (b : SmoothBumpFunction (𝓡 n) p) (x : M) : (cutoffChartMetric g p b x).PosDef := by
  apply positiveMatrixExtension_posDef b _ (fun _ => b.nonneg) (fun _ => b.le_one)
  intro y hy
  have hychart := b.tsupport_subset_chartAt_source (subset_tsupport b hy)
  exact DeTurckNative.frameMetricJet_value_posDef g (DeTurckNative.chartFrame p) y
    (DeTurckNative.chartFrameBasis p y hychart) (DeTurckNative.chartFrame_eq_basis p y hychart)

theorem cutoffChartMetric_det_ne_zero (g : RiemannianMetric n M) (p : M)
    (b : SmoothBumpFunction (𝓡 n) p) (x : M) : (cutoffChartMetric g p b x).det ≠ 0 :=
  ne_of_gt (cutoffChartMetric_posDef g p b x).det_pos

theorem cutoffChartMetric_contMDiff (g : RiemannianMetric n M) (p : M)
    (b : SmoothBumpFunction (𝓡 n) p) :
    ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => cutoffChartMetric g p b x i j) := by
  apply positiveMatrixExtension_contMDiff b _
    (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source b.contMDiff
    b.tsupport_subset_chartAt_source
  intro i j x hx
  have hvalue := DeTurckNative.frameMetricJet_value_contMDiffAt g
    (DeTurckNative.chartFrame p) (fun a =>
      (DeTurckNative.chartFrame_contMDiffOn p a).contMDiffAt
        ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hx))
  exact (contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp hvalue i) j).contMDiffWithinAt

theorem cutoffChartMetric_inverse_contMDiff (g : RiemannianMetric n M) (p : M)
    (b : SmoothBumpFunction (𝓡 n) p) (i j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => (cutoffChartMetric g p b x)⁻¹ i j) :=
  inverse_entry_contMDiff (cutoffChartMetric g p b) (cutoffChartMetric_contMDiff g p b)
    (cutoffChartMetric_det_ne_zero g p b) i j

theorem cutoffChartMetric_eventuallyEq (g : RiemannianMetric n M) (p : M)
    (b : SmoothBumpFunction (𝓡 n) p) :
    cutoffChartMetric g p b =ᶠ[𝓝 p]
      (fun x => (DeTurckNative.frameMetricJet g (DeTurckNative.chartFrame p) x).value) :=
  positiveMatrixExtension_eventuallyEq b _ b.eventuallyEq_one

theorem directionalWord_cutoffChartMetric_eq
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota)
    (g : RiemannianMetric n M) (p : M) (b : SmoothBumpFunction (𝓡 n) p)
    {x : M} (hb : (b : M → ℝ) =ᶠ[𝓝 x] 1) (i j : Fin n) :
    directionalWord F w (fun y => cutoffChartMetric g p b y i j) x =
      directionalWord F w (fun y =>
        g.inner y (DeTurckNative.chartFrame p i y) (DeTurckNative.chartFrame p j y)) x :=
  directionalWord_positiveMatrixExtension_eq F w b _ hb i j

theorem directionalWord_cutoffChartMetric_inv_eq
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota)
    (g : RiemannianMetric n M) (p : M) (b : SmoothBumpFunction (𝓡 n) p)
    {x : M} (hb : (b : M → ℝ) =ᶠ[𝓝 x] 1) (i j : Fin n) :
    directionalWord F w (fun y => (cutoffChartMetric g p b y)⁻¹ i j) x =
      directionalWord F w (fun y =>
        (DeTurckNative.frameMetricJet g (DeTurckNative.chartFrame p) y).value⁻¹ i j) x :=
  directionalWord_positiveMatrixExtension_inv_eq F w b _ hb i j

theorem cutoffChartMetric_sub_entry (g h : RiemannianMetric n M) (p : M)
    (b : SmoothBumpFunction (𝓡 n) p) (x : M) (i j : Fin n) :
    (cutoffChartMetric g p b x - cutoffChartMetric h p b x) i j =
      b x * (g.inner x (DeTurckNative.chartFrame p i x) (DeTurckNative.chartFrame p j x) -
        h.inner x (DeTurckNative.chartFrame p i x) (DeTurckNative.chartFrame p j x)) := by
  unfold cutoffChartMetric
  rw [positiveMatrixExtension_sub]
  rfl

end ChartMetric

section UniformInverse

open scoped Matrix.Norms.Elementwise


theorem exists_uniform_inverse_perturbation [CompactSpace M]
    (G : M → Matrix (Fin n) (Fin n) ℝ) (hG : Continuous G)
    (hpos : ∀ x, (G x).PosDef) :
    ∃ rho I : ℝ, 0 < rho ∧ 0 < I ∧
      ∀ D : M → Matrix (Fin n) (Fin n) ℝ,
        (∀ x, (D x).IsSymm) → (∀ x, ‖D x‖ ≤ rho) →
        ∀ x, (G x + D x).PosDef ∧ ∀ i j : Fin n, ‖(G x + D x)⁻¹ i j‖ ≤ I := by
  obtain ⟨rho, hrho, hpositive⟩ := DeTurckNative.exists_uniform_posDef_perturbation
    G (K := Set.univ) isCompact_univ hG.continuousOn (fun x _ => hpos x)
  let A : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {D | D.IsSymm} ∩ Metric.closedBall 0 rho
  have hclosed : IsClosed {D : Matrix (Fin n) (Fin n) ℝ | D.IsSymm} :=
    isClosed_eq continuous_id.matrix_transpose continuous_id
  have hA : IsCompact A := (isCompact_closedBall _ _).inter_left hclosed
  let f : M × Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun q => G q.1 + q.2
  let S := f '' (Set.univ ×ˢ A)
  have hf : Continuous f := (hG.comp continuous_fst).add continuous_snd
  have hS : IsCompact S := (isCompact_univ.prod hA).image hf
  have hSpos : ∀ B ∈ S, B.PosDef := by
    rintro B ⟨⟨x, D⟩, ⟨_, hD⟩, rfl⟩
    apply hpositive x (mem_univ x) (G x + D)
    · exact (show (G x).IsSymm by
        simpa only [Matrix.isHermitian_iff_isSymm] using (hpos x).isHermitian).add hD.1
    · simpa only [add_sub_cancel_left, Metric.mem_closedBall, dist_zero_right] using hD.2
  have hinv : ContinuousOn (fun B : Matrix (Fin n) (Fin n) ℝ => B⁻¹) S :=
    DeTurckNative.continuousOn_inverse_posDef (fun B => B) continuous_id.continuousOn hSpos
  obtain ⟨I, hI, hbound⟩ := (hS.image_of_continuousOn hinv).isBounded.exists_pos_norm_le
  refine ⟨rho, I, hrho, hI, ?_⟩
  intro D hsymm hsmall x
  have hmem : G x + D x ∈ S := by
    refine ⟨(x, D x), ⟨mem_univ x, hsymm x, ?_⟩, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hsmall x
  refine ⟨hSpos _ hmem, fun i j => ?_⟩
  exact (Matrix.norm_entry_le_entrywise_sup_norm _).trans (hbound _ ⟨_, hmem, rfl⟩)


theorem exists_cutoffChartMetric_inverse_perturbation [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) (p : M) (b : SmoothBumpFunction (𝓡 n) p) :
    ∃ rho I : ℝ, 0 < rho ∧ 0 < I ∧
      ∀ D : M → Matrix (Fin n) (Fin n) ℝ,
        (∀ x, (D x).IsSymm) → (∀ x, ‖D x‖ ≤ rho) →
        ∀ x, (cutoffChartMetric g p b x + D x).PosDef ∧
          ∀ i j : Fin n, ‖(cutoffChartMetric g p b x + D x)⁻¹ i j‖ ≤ I :=
  exists_uniform_inverse_perturbation (cutoffChartMetric g p b)
    (cutoffChartMetric_contMDiff g p b).continuous (cutoffChartMetric_posDef g p b)

end UniformInverse

end PositiveExtension

end PoincareConjecture.DeTurckInverseCompositionNative
