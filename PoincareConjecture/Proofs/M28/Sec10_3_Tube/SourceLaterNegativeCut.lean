import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeMinimizerOverlapAssembly










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe v

namespace PoincareConjecture.M28

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem adjacent_later_negative_cut (N Q : EpsilonNeck g)
    (hwithin : N.carrier ∩ Q.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2)) :
    Disjoint Q.carrier (N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) := by
  refine Set.disjoint_left.mpr fun y hyQ hyN => ?_
  have h := (hwithin ⟨hyN.1, hyQ⟩).1.2.1
  exact absurd hyN.2.2 (not_lt.mpr h.le)

set_option maxHeartbeats 800000 in



theorem later_negative_cut_of_minimizer
    (N P : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    (hA : 1000 ≤ N.epsilon⁻¹) (heq : P.epsilon = N.epsilon)
    (hratio : P.scale ≤ (1.1 : ℝ) * N.scale)
    {U : Set M} (hNU : N.carrier ⊆ U) (hPU : P.carrier ⊆ U)
    {γ : ℝ → M} {t₁ tN tP : ℝ} (h₁ : t₁ < tN) (hNP : tN < tP)
    (_hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc t₁ tP))
    (_hcN : γ tN = N.center) (hcP : γ tP = P.center)
    (hmin : ∀ a b, t₁ ≤ a → a ≤ b → b ≤ tP →
      g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hadd : g.pathELength γ t₁ tP =
      g.pathELength γ t₁ tN + g.pathELength γ tN tP)
    (hanchor : g.pathELength γ t₁ tN =
      ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹))
    (hsign : (N.coordinate_inverse (γ t₁)).2 ≤
      -((0.292 : ℝ) * N.epsilon⁻¹))
    (hz₁ : γ t₁ ∈ N.carrier)
    (hfar : ENNReal.ofReal ((1.9 : ℝ) * N.scale * N.epsilon⁻¹) ≤
      g.pathELength γ tN tP) :
    Disjoint P.carrier (N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2)) := by
  let A : ℝ := N.epsilon⁻¹
  have hApos : 0 < A := inv_pos.mpr N.epsilon_pos
  have hrootN : Real.sqrt (1 + N.epsilon) ≤ (1.0005 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hrootP : Real.sqrt (1 + P.epsilon) ≤ (1.0005 : ℝ) := by
    simpa only [heq] using hrootN
  have hconst : Real.sqrt 2 * (Real.pi + 1) ≤ (7.1 : ℝ) := by
    have hs2 : Real.sqrt 2 ≤ (1.415 : ℝ) := by
      have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
      nlinarith [Real.sqrt_nonneg 2]
    have hmul := mul_le_mul hs2
      (show Real.pi + 1 ≤ (5 : ℝ) by nlinarith [Real.pi_le_four])
      (add_nonneg Real.pi_pos.le (by norm_num))
      (by norm_num : (0 : ℝ) ≤ 1.415)
    nlinarith [hmul]
  have haxial_bound (R : EpsilonNeck g) (hRU : R.carrier ⊆ U)
      (hroot : Real.sqrt (1 + R.epsilon) ≤ (1.0005 : ℝ))
      {x y : M} (hx : x ∈ R.carrier) (hy : y ∈ R.carrier)
      {C : ℝ} (hcoord : |(R.coordinate_inverse y).2 -
        (R.coordinate_inverse x).2| ≤ C * A) :
      intrinsicEDist g U x y ≤
        ENNReal.ofReal (R.scale * (1.0005 : ℝ) * (C * A + 7.1)) := by
    have hsum : |(R.coordinate_inverse y).2 -
          (R.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1) ≤
        C * A + 7.1 := by
      linarith [hcoord, hconst]
    have hinner0 : 0 ≤ |(R.coordinate_inverse y).2 -
        (R.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1) := by
      exact add_nonneg (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
        (add_nonneg Real.pi_pos.le (by norm_num)))
    have hreal : R.scale * Real.sqrt (1 + R.epsilon) *
          (|(R.coordinate_inverse y).2 - (R.coordinate_inverse x).2| +
            Real.sqrt 2 * (Real.pi + 1)) ≤
        R.scale * (1.0005 : ℝ) * (C * A + 7.1) := by
      have hstep := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hroot hinner0) R.scale_pos.le
      have hstep' : R.scale * Real.sqrt (1 + R.epsilon) *
            (|(R.coordinate_inverse y).2 - (R.coordinate_inverse x).2| +
              Real.sqrt 2 * (Real.pi + 1)) ≤
          R.scale * (1.0005 : ℝ) *
            (|(R.coordinate_inverse y).2 - (R.coordinate_inverse x).2| +
              Real.sqrt 2 * (Real.pi + 1)) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hstep
      have hstep'' := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg R.scale_pos.le (by norm_num : (0 : ℝ) ≤ 1.0005))
      have hstep''' : R.scale * (1.0005 : ℝ) *
            (|(R.coordinate_inverse y).2 - (R.coordinate_inverse x).2| +
              Real.sqrt 2 * (Real.pi + 1)) ≤
          R.scale * (1.0005 : ℝ) * (C * A + 7.1) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hstep''
      exact hstep'.trans hstep'''
    apply (intrinsicEDist_mono_of_subset (g := g) hRU).trans
    apply (R.intrinsicEDist_le_axial_add hx hy).trans
    exact ENNReal.ofReal_le_ofReal hreal
  have hPcenter : P.center ∈ P.carrier :=
    P.central_sphere_subset P.center_on_central_sphere
  have hPcoord0 : (P.coordinate_inverse P.center).2 = 0 :=
    (P.mem_central_sphere_iff_of_mem_carrier hPcenter).mp
      P.center_on_central_sphere
  have hpathLower : ENNReal.ofReal ((2.2 : ℝ) * N.scale * A) ≤
      g.pathELength γ t₁ tP := by
    have ha : 0 ≤ (0.3 : ℝ) * N.scale * A :=
      mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le
    have hb : 0 ≤ (1.9 : ℝ) * N.scale * A :=
      mul_nonneg (mul_nonneg (by norm_num) N.scale_pos.le) hApos.le
    have hsum : ENNReal.ofReal ((0.3 : ℝ) * N.scale * A +
          (1.9 : ℝ) * N.scale * A) ≤ g.pathELength γ t₁ tP := by
      rw [ENNReal.ofReal_add ha hb]
      calc
        ENNReal.ofReal ((0.3 : ℝ) * N.scale * A) +
            ENNReal.ofReal ((1.9 : ℝ) * N.scale * A) ≤
          g.pathELength γ t₁ tN + g.pathELength γ tN tP := by
          exact add_le_add (by simpa [A] using hanchor.symm.le) hfar
        _ = g.pathELength γ t₁ tP := hadd.symm
    have hcoef : (2.2 : ℝ) * N.scale * A =
        (0.3 : ℝ) * N.scale * A + (1.9 : ℝ) * N.scale * A := by ring
    rw [hcoef]
    exact hsum
  refine Set.disjoint_left.mpr fun y hyP hyN => ?_
  have hyNc := N.coordinate_inverse_mem y hyN.1
  have hyPc := P.coordinate_inverse_mem y hyP
  have hz₁c := N.coordinate_inverse_mem (γ t₁) hz₁
  have hdiffN : |(N.coordinate_inverse y).2 -
      (N.coordinate_inverse (γ t₁)).2| ≤ (0.708 : ℝ) * A := by
    rw [abs_le]
    constructor
    · nlinarith only [hyN.2.1, hsign, hApos]
    · nlinarith only [hyN.2.2, hz₁c.2.1, hApos]
  have hdiffP : |(P.coordinate_inverse P.center).2 -
      (P.coordinate_inverse y).2| ≤ A := by
    rw [hPcoord0, zero_sub, abs_le]
    constructor
    · have h : (P.coordinate_inverse y).2 ≤ A := by
        simpa [A, heq] using hyPc.2.2.le
      nlinarith
    · have h : -A < (P.coordinate_inverse y).2 := by
        simpa [A, heq] using hyPc.2.1
      nlinarith
  have hNcost := haxial_bound N hNU hrootN hz₁ hyN.1 hdiffN
  have hdiffP' : |(P.coordinate_inverse y).2 -
      (P.coordinate_inverse P.center).2| ≤ A := by
    simpa only [abs_sub_comm] using hdiffP
  have hdiffP'' : |(P.coordinate_inverse y).2 -
      (P.coordinate_inverse P.center).2| ≤ (1 : ℝ) * A := by
    simpa using hdiffP'
  have hPcost := haxial_bound P hPU hrootP hPcenter hyP (C := 1) hdiffP''
  have hPcost' : intrinsicEDist g U y P.center ≤
      ENNReal.ofReal (P.scale * (1.0005 : ℝ) * (A + 7.1)) := by
    rw [intrinsicEDist_comm_set]
    simpa using hPcost
  have htri := intrinsicEDist_triangle_set (g := g) (U := U)
    (p := γ t₁) (q := y) (r := P.center)
  have hcomp := htri.trans (add_le_add hNcost hPcost')
  have hpathUpper : g.pathELength γ t₁ tP ≤
      ENNReal.ofReal (N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1)) +
        ENNReal.ofReal (P.scale * (1.0005 : ℝ) * (A + 7.1)) := by
    rw [hmin t₁ tP le_rfl (h₁.le.trans hNP.le) le_rfl]
    simpa [hcP] using hcomp
  have hupper := hpathUpper
  have hbad := hpathLower.trans hupper
  have hNterm : 0 ≤ N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) := by
    exact mul_nonneg (mul_nonneg N.scale_pos.le (by norm_num)) (by nlinarith [hApos])
  have hPterm : 0 ≤ P.scale * (1.0005 : ℝ) * (A + 7.1) := by
    exact mul_nonneg (mul_nonneg P.scale_pos.le (by norm_num)) (by nlinarith [hApos])
  have hbad' : (2.2 : ℝ) * N.scale * A ≤
      N.scale * (1.0005 : ℝ) * ((0.708 : ℝ) * A + 7.1) +
        P.scale * (1.0005 : ℝ) * (A + 7.1) := by
    rw [← ENNReal.ofReal_add hNterm hPterm] at hbad
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hNterm hPterm)).mp hbad
  nlinarith only [hbad', hratio, hA, N.scale_pos, P.scale_pos, hApos]

end PoincareConjecture.M28
