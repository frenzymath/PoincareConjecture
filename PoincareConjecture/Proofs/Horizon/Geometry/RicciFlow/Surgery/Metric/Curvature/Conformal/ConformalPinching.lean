import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Curvature.StandardCapTransfer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Curvature.CurvaturePinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.CurvatureTrace
import Mathlib.Data.Real.Pointwise










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology Pointwise

universe u v

namespace PoincareConjecture.MetricSurgery

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem leastSectionalCurvature_le_sectional_of_orthonormal
    (D : LeviCivitaData g) (x : M) {a b : TangentSpace (𝓡 3) x}
    (hab : LeviCivitaData.IsOrthonormalPair g x a b) :
    D.leastSectionalCurvature x ≤ D.sectionalCurvature x a b := by
  let S : Set ℝ := {k | ∃ v w : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x v w ∧ k = D.curvatureTensor x v w v w}
  have hS : BddBelow S := by
    refine ⟨-D.curvatureTensorNorm x, ?_⟩
    rintro k ⟨v, w, hvw, rfl⟩
    rw [← sectional_eq_tensor_of_orthonormal D x hvw]
    exact (abs_le.mp (D.abs_sectionalCurvature_le_curvatureTensorNorm x v w)).1
  change sInf S ≤ D.sectionalCurvature x a b
  rw [sectional_eq_tensor_of_orthonormal D x hab]
  exact csInf_le hS ⟨a, b, hab, rfl⟩



theorem neg_negativeCurvaturePart_le_sectional_of_orthonormal
    (D : LeviCivitaData g) (x : M) {a b : TangentSpace (𝓡 3) x}
    (hab : LeviCivitaData.IsOrthonormalPair g x a b) :
    -D.negativeCurvaturePart x ≤ D.sectionalCurvature x a b := by
  have hleast := leastSectionalCurvature_le_sectional_of_orthonormal D x hab
  have hmax := le_max_left (-D.leastSectionalCurvature x) (0 : ℝ)
  unfold LeviCivitaData.negativeCurvaturePart
  linarith only [hleast, hmax]



theorem negativeCurvaturePart_le_of_sectional_lower_bound
    (D : LeviCivitaData g) (x : M) {xi : ℝ} (hxi : 0 ≤ xi)
    (hbound : ∀ a b : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x a b → -xi ≤ D.sectionalCurvature x a b) :
    D.negativeCurvaturePart x ≤ xi := by
  let S : Set ℝ := {k | ∃ v w : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x v w ∧ k = D.curvatureTensor x v w v w}
  have hleast : -xi ≤ D.leastSectionalCurvature x := by
    change -xi ≤ sInf S
    by_cases hS : S.Nonempty
    · apply le_csInf hS
      rintro k ⟨v, w, hvw, rfl⟩
      rw [← sectional_eq_tensor_of_orthonormal D x hvw]
      exact hbound v w hvw
    · rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sInf_empty]
      exact neg_nonpos.mpr hxi
  exact max_le (by linarith only [hleast]) hxi



theorem positiveScaling_exp_orthonormal_base (g : RiemannianMetric 3 M)
    (F : M → ℝ) (hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F) (x : M)
    (a b : TangentSpace (𝓡 3) x)
    (hab : LeviCivitaData.IsOrthonormalPair
      (positiveScaling g (fun y => Real.exp (-2 * F y))
        (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)) x a b) :
    LeviCivitaData.IsOrthonormalPair g x
      (Real.exp (-F x) • a) (Real.exp (-F x) • b) := by
  have he : Real.exp (-F x) * Real.exp (-F x) = Real.exp (-2 * F x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm (v w : TangentSpace (𝓡 3) x) :
      g.inner x (Real.exp (-F x) • v) (Real.exp (-F x) • w) =
        (positiveScaling g (fun y => Real.exp (-2 * F y))
          (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)).inner x v w := by
    change g.inner x (Real.exp (-F x) • v) (Real.exp (-F x) • w) =
      Real.exp (-2 * F x) * g.inner x v w
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, he]
  exact ⟨(hm a a).trans hab.1, (hm b b).trans hab.2.1, (hm a b).trans hab.2.2⟩




theorem negativeCurvaturePart_positiveScaling_profile_le_of_split
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (F : M → ℝ) (hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling g (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    (s : M → ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : M)
    (hs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y))
    (B kappa : ℝ) (hp : 0 ≤ deriv phi (s x)) (ht : 0 ≤ deriv (deriv phi) (s x))
    (hH : ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 → -B ≤ D.hessian s x v v)
    (hG : g.inner x (D.gradient s x) (D.gradient s x) ≤ 2)
    (herr : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 ≤
      deriv (deriv phi) (s x) / 4)
    (hgap : ∀ a b : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x a b →
      (mvfderiv (𝓡 3) s x a) ^ 2 + (mvfderiv (𝓡 3) s x b) ^ 2 < 1 / 2 →
        kappa ≤ D.sectionalCurvature x a b)
    (hsmall : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 ≤ kappa)
    (hamp : 2 * D.negativeCurvaturePart x * phi (s x) ≤ deriv (deriv phi) (s x) / 4) :
    D'.negativeCurvaturePart x ≤ D.negativeCurvaturePart x := by
  have hxi : 0 ≤ D.negativeCurvaturePart x := le_max_right _ _
  apply negativeCurvaturePart_le_of_sectional_lower_bound D' x hxi
  intro a b hab
  have hbase := positiveScaling_exp_orthonormal_base g F hF x a b hab
  have hK := neg_negativeCurvaturePart_le_sectional_of_orthonormal D x hbase
  have hnew := sectionalCurvature_positiveScaling_profile_lower_of_split
    g D F hF D' s phi hphi x hs heq (Real.exp (-F x) • a) (Real.exp (-F x) • b)
    hbase.1 hbase.2.1 hbase.2.2 B kappa (D.negativeCurvaturePart x) hp ht
    (hH _ hbase.1) (hH _ hbase.2.1) hG herr (hgap _ _ hbase) hsmall hxi hK hamp
  rw [sectionalCurvature_smul_pair D' x a b
    (Real.exp_ne_zero (-F x)) (Real.exp_ne_zero (-F x))] at hnew
  exact hnew




theorem sectionalCurvature_positiveScaling_profile_orthonormal_pos_of_split
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (F : M → ℝ) (hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling g (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    (s : M → ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : M)
    (hs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y))
    (B kappa : ℝ) (hp : 0 ≤ deriv phi (s x)) (ht : 0 ≤ deriv (deriv phi) (s x))
    (hH : ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 → -B ≤ D.hessian s x v v)
    (hG : g.inner x (D.gradient s x) (D.gradient s x) ≤ 2)
    (herr : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 ≤
      deriv (deriv phi) (s x) / 4)
    (hgap : ∀ a b : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x a b →
      (mvfderiv (𝓡 3) s x a) ^ 2 + (mvfderiv (𝓡 3) s x b) ^ 2 < 1 / 2 →
        kappa ≤ D.sectionalCurvature x a b)
    (hsmall : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 < kappa)
    (hpositive : ∀ a b : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x a b →
      0 < D.sectionalCurvature x a b)
    (a b : TangentSpace (𝓡 3) x)
    (hab : LeviCivitaData.IsOrthonormalPair
      (positiveScaling g (fun y => Real.exp (-2 * F y))
        (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)) x a b) :
    0 < D'.sectionalCurvature x a b := by
  have hbase := positiveScaling_exp_orthonormal_base g F hF x a b hab
  have hnew := sectionalCurvature_positiveScaling_profile_pos_of_split
    g D F hF D' s phi hphi x hs heq (Real.exp (-F x) • a) (Real.exp (-F x) • b)
    hbase.1 hbase.2.1 hbase.2.2 B kappa hp ht (hH _ hbase.1) (hH _ hbase.2.1)
    hG herr (hgap _ _ hbase) hsmall (hpositive _ _ hbase)
  rw [sectionalCurvature_smul_pair D' x a b
    (Real.exp_ne_zero (-F x)) (Real.exp_ne_zero (-F x))] at hnew
  exact hnew




theorem sectionalCurvature_positiveScaling_profile_orthonormal_pos_of_gain
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (F : M → ℝ) (hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling g (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    (s : M → ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : M)
    (hs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y))
    (B kappa : ℝ) (hp : 0 ≤ deriv phi (s x)) (ht : 0 ≤ deriv (deriv phi) (s x))
    (hH : ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 → -B ≤ D.hessian s x v v)
    (hG : g.inner x (D.gradient s x) (D.gradient s x) ≤ 2)
    (herr : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 ≤
      deriv (deriv phi) (s x) / 4)
    (hgap : ∀ a b : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x a b →
      (mvfderiv (𝓡 3) s x a) ^ 2 + (mvfderiv (𝓡 3) s x b) ^ 2 < 1 / 2 →
        kappa ≤ D.sectionalCurvature x a b)
    (hsmall : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 < kappa)
    (hgain : D.negativeCurvaturePart x < deriv (deriv phi) (s x) / 4)
    (a b : TangentSpace (𝓡 3) x)
    (hab : LeviCivitaData.IsOrthonormalPair
      (positiveScaling g (fun y => Real.exp (-2 * F y))
        (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)) x a b) :
    0 < D'.sectionalCurvature x a b := by
  let v := Real.exp (-F x) • a
  let w := Real.exp (-F x) • b
  let p := deriv phi (s x)
  let t := deriv (deriv phi) (s x)
  let A := (mvfderiv (𝓡 3) s x v) ^ 2 + (mvfderiv (𝓡 3) s x w) ^ 2
  have hbase : LeviCivitaData.IsOrthonormalPair g x v w :=
    positiveScaling_exp_orthonormal_base g F hF x a b hab
  have hK := neg_negativeCurvaturePart_le_sectional_of_orthonormal D x hbase
  have hA0 : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hL := sectionalCurvature_positiveScaling_profile_lower_bound g D F hF D'
    s phi hphi x hs heq v w hbase.1 hbase.2.1 hbase.2.2 B 2 hp
    (hH v hbase.1) (hH w hbase.2.1) hG
  change 0 ≤ t at ht
  change 2 * B * p + 2 * p ^ 2 ≤ t / 4 at herr
  change 2 * B * p + 2 * p ^ 2 < kappa at hsmall
  change D.negativeCurvaturePart x < t / 4 at hgain
  change Real.exp (2 * phi (s x)) *
    (D.sectionalCurvature x v w + t * A - 2 * B * p - 2 * p ^ 2) ≤
      D'.sectionalCurvature x v w at hL
  have hbracket : 0 < D.sectionalCurvature x v w + t * A - 2 * B * p - 2 * p ^ 2 := by
    by_cases hA : 1 / 2 ≤ A
    · have hta := mul_le_mul_of_nonneg_left hA ht
      nlinarith only [hK, hgain, herr, hta]
    · have hbasegap := hgap v w hbase (lt_of_not_ge hA)
      nlinarith only [hbasegap, hsmall, mul_nonneg ht hA0]
  have hpos := (mul_pos (Real.exp_pos (2 * phi (s x))) hbracket).trans_le hL
  dsimp only [v, w] at hpos
  rwa [sectionalCurvature_smul_pair D' x a b
    (Real.exp_ne_zero (-F x)) (Real.exp_ne_zero (-F x))] at hpos



theorem positiveScaling_const_orthonormal_iff (g : RiemannianMetric 3 M)
    {c : ℝ} (hc : 0 < c) (x : M) (a b : TangentSpace (𝓡 3) x) :
    LeviCivitaData.IsOrthonormalPair
      (positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc)) x a b ↔
        LeviCivitaData.IsOrthonormalPair g x (Real.sqrt c • a) (Real.sqrt c • b) := by
  have hm (v w : TangentSpace (𝓡 3) x) :
      g.inner x (Real.sqrt c • v) (Real.sqrt c • w) =
        (positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc)).inner x v w := by
    change g.inner x (Real.sqrt c • v) (Real.sqrt c • w) = c * g.inner x v w
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, Real.mul_self_sqrt hc.le]
  unfold LeviCivitaData.IsOrthonormalPair
  rw [hm, hm, hm]



theorem sectionalCurvature_positiveScaling_const_of_orthonormal
    (D : LeviCivitaData g) {c : ℝ} (hc : 0 < c)
    (D' : LeviCivitaData (positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc)))
    (x : M) {a b : TangentSpace (𝓡 3) x}
    (hab : LeviCivitaData.IsOrthonormalPair g x a b) :
    D'.sectionalCurvature x a b = c⁻¹ * D.sectionalCurvature x a b := by
  let F : M → ℝ := fun _ => -Real.log c / 2
  have hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F := contMDiff_const
  have hmetric : positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc) =
      positiveScaling g (fun y => Real.exp (-2 * F y))
        (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _) := by
    have he : (fun y => Real.exp (-2 * F y)) = fun _ => c := by
      funext y
      change Real.exp (-2 * (-Real.log c / 2)) = c
      rw [show -2 * (-Real.log c / 2) = Real.log c by ring, Real.exp_log hc]
    congr 1
    exact he.symm
  revert D'
  rw [hmetric]
  intro D'
  have he : Real.exp (2 * (-Real.log c / 2)) = c⁻¹ := by
    rw [show 2 * (-Real.log c / 2) = -Real.log c by ring, Real.exp_neg, Real.exp_log hc]
  have hK := sectionalCurvature_positiveScaling_profile g D F hF D'
    (fun _ => 0) (fun _ => -Real.log c / 2) contDiff_const x contMDiffAt_const
    (Filter.Eventually.of_forall (fun _ => rfl)) a b hab.1 hab.2.1 hab.2.2
  simpa only [deriv_const', deriv_const, he, zero_mul, zero_pow (by decide : 2 ≠ 0),
    add_zero, zero_add, sub_zero] using hK



theorem leastSectionalCurvature_positiveScaling_const
    (D : LeviCivitaData g) {c : ℝ} (hc : 0 < c)
    (D' : LeviCivitaData (positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc)))
    (x : M) : D'.leastSectionalCurvature x = c⁻¹ * D.leastSectionalCurvature x := by
  let H := positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc)
  let S : Set ℝ := {k | ∃ a b : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x a b ∧ k = D.curvatureTensor x a b a b}
  let S' : Set ℝ := {k | ∃ a b : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair H x a b ∧ k = D'.curvatureTensor x a b a b}
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hp (a b : TangentSpace (𝓡 3) x) :
      LeviCivitaData.IsOrthonormalPair H x a b ↔
        LeviCivitaData.IsOrthonormalPair g x (Real.sqrt c • a) (Real.sqrt c • b) :=
    positiveScaling_const_orthonormal_iff g hc x a b
  have hK (a b : TangentSpace (𝓡 3) x)
      (hab : LeviCivitaData.IsOrthonormalPair H x a b) :
      D'.curvatureTensor x a b a b = c⁻¹ * D.curvatureTensor x
        (Real.sqrt c • a) (Real.sqrt c • b) (Real.sqrt c • a) (Real.sqrt c • b) := by
    have hbase := (hp a b).mp hab
    have hsec := sectionalCurvature_positiveScaling_const_of_orthonormal D hc D' x hbase
    rw [sectionalCurvature_smul_pair D' x a b hs hs,
      sectional_eq_tensor_of_orthonormal D x hbase,
      sectional_eq_tensor_of_orthonormal D' x hab] at hsec
    exact hsec
  have hsurj : Function.Surjective (fun a : TangentSpace (𝓡 3) x => Real.sqrt c • a) := by
    intro a
    exact ⟨(Real.sqrt c)⁻¹ • a, by simp only [smul_smul, mul_inv_cancel₀ hs, one_smul]⟩
  have hsets : S' = c⁻¹ • S := by
    ext k
    constructor
    · rintro ⟨a, b, hab, rfl⟩
      exact Set.mem_smul_set.mpr ⟨_, ⟨Real.sqrt c • a, Real.sqrt c • b,
        (hp a b).mp hab, rfl⟩, (hK a b hab).symm⟩
    · intro hk
      obtain ⟨z, ⟨a, b, hab, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hk
      obtain ⟨a', rfl⟩ := hsurj a
      obtain ⟨b', rfl⟩ := hsurj b
      have hab' := (hp a' b').mpr hab
      exact ⟨a', b', hab', (hK a' b' hab').symm⟩
  change sInf S' = c⁻¹ * sInf S
  rw [hsets]
  exact Real.sInf_smul_of_nonneg (inv_nonneg.mpr hc.le) S



theorem negativeCurvaturePart_positiveScaling_const
    (D : LeviCivitaData g) {c : ℝ} (hc : 0 < c)
    (D' : LeviCivitaData (positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc)))
    (x : M) : D'.negativeCurvaturePart x = c⁻¹ * D.negativeCurvaturePart x := by
  unfold LeviCivitaData.negativeCurvaturePart
  rw [leastSectionalCurvature_positiveScaling_const D hc D' x,
    mul_max_of_nonneg _ _ (inv_nonneg.mpr hc.le)]
  simp only [mul_neg, mul_zero]

section LocalIsometry

variable {X : Type v} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
  {h : RiemannianMetric 3 X}




theorem leastSectionalCurvature_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → X} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 3) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y a) (mfderiv (𝓡 3) (𝓡 3) f y b))
    {x : M} (hx : x ∈ U) :
    D.leastSectionalCurvature x = D'.leastSectionalCurvature (f x) := by
  let L := mfderiv (𝓡 3) (𝓡 3) f x
  have hp (a b : TangentSpace (𝓡 3) x) :
      LeviCivitaData.IsOrthonormalPair g x a b ↔
        LeviCivitaData.IsOrthonormalPair h (f x) (L a) (L b) := by
    unfold LeviCivitaData.IsOrthonormalPair
    rw [hmetric x hx, hmetric x hx, hmetric x hx]
  have hsurj : Function.Surjective L :=
    (g.mfderiv_bijective_of_pullback_eq h x (fun a b => (hmetric x hx a b).symm)).2
  have hK (a b : TangentSpace (𝓡 3) x) :
      D.curvatureTensor x a b a b = D'.curvatureTensor (f x) (L a) (L b) (L a) (L b) :=
    D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx a b a b
  unfold LeviCivitaData.leastSectionalCurvature
  congr 1
  ext k
  constructor
  · rintro ⟨a, b, hab, hk⟩
    exact ⟨L a, L b, (hp a b).mp hab, hk.trans (hK a b)⟩
  · rintro ⟨a, b, hab, hk⟩
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    exact ⟨a', b', (hp a' b').mpr hab, hk.trans (hK a' b').symm⟩



theorem negativeCurvaturePart_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → X} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 3) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y a) (mfderiv (𝓡 3) (𝓡 3) f y b))
    {x : M} (hx : x ∈ U) :
    D.negativeCurvaturePart x = D'.negativeCurvaturePart (f x) := by
  unfold LeviCivitaData.negativeCurvaturePart
  rw [leastSectionalCurvature_eq_of_local_isometry D D' hU hf hmetric hx]

end LocalIsometry


end PoincareConjecture.MetricSurgery
