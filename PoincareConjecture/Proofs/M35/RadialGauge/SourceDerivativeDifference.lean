import PoincareConjecture.Proofs.M35.RadialGauge.SourceDerivative










set_option autoImplicit false

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "D" => V →L[ℝ] ℝ



noncomputable def sourceDerivativeJet (b : V) (db : V →L[ℝ] V)
    (p : D) (H : V →L[ℝ] D) (gx : D) (gz : ℝ) : D :=
  p.comp db + H.flip b + (dualSquaredDifferential p).comp H + gx + gz • p

theorem graph_derivative_eq (q : (V × ℝ) →L[ℝ] ℝ) (p : D) :
    q.comp ((ContinuousLinearMap.id ℝ V).prod p) =
      q.comp (ContinuousLinearMap.inl ℝ V ℝ) + q (0, 1) • p := by
  ext v
  change q (v, p v) = q (v, 0) + q (0, 1) * p v
  have hp : (v, p v) = (v, 0) + (p v) • (0, (1 : ℝ)) := by ext <;> simp
  rw [hp, map_add, map_smul]
  simp only [smul_eq_mul]
  ring


theorem gaugeSource_fderiv_eq_jet
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ} {x : V}
    (hb : DifferentiableAt ℝ b x) (hu : DifferentiableAt ℝ u x)
    (hdu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hG : DifferentiableAt ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x)) :
    fderiv ℝ (gaugeSource b G u) x = sourceDerivativeJet (b x) (fderiv ℝ b x)
      (fderiv ℝ u x) (fderiv ℝ (fderiv ℝ u) x)
      ((fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x)).comp
        (ContinuousLinearMap.inl ℝ V ℝ))
      (fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x) (0, 1)) := by
  rw [gaugeSource_fderiv_eq hb hu hdu hG, graph_derivative_eq]
  simp only [sourceDerivativeJet, add_assoc]


theorem sourceDerivativeJet_sub (b : V) (db : V →L[ℝ] V) (p q : D)
    (H K : V →L[ℝ] D) (gx hx : D) (gz hz : ℝ) :
    sourceDerivativeJet b db p H gx gz - sourceDerivativeJet b db q K hx hz =
      (p - q).comp db + (H - K).flip b + (dualSquaredDifferential p).comp (H - K) +
      (dualSquaredDifferential (p - q)).comp K + (gx - hx) +
      (gz • (p - q) + (gz - hz) • q) := by
  have hsquare : (dualSquaredDifferential (p - q)).comp K =
      (dualSquaredDifferential p).comp K - (dualSquaredDifferential q).comp K := by
    rw [← dualSquaredDifferential_sub, ContinuousLinearMap.sub_comp]
  have hflip : (H - K).flip b = H.flip b - K.flip b := by
    ext v
    rfl
  rw [sourceDerivativeJet, sourceDerivativeJet, hsquare, hflip,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  simp only [sub_eq_add_neg, add_smul, smul_add, smul_neg, neg_smul]
  abel



theorem sourceDerivativeJet_norm_sub_le (b : V) (db : V →L[ℝ] V) (p q : D)
    (H K : V →L[ℝ] D) (gx hx : D) (gz hz : ℝ) :
    ‖sourceDerivativeJet b db p H gx gz - sourceDerivativeJet b db q K hx hz‖ ≤
      (‖b‖ + 2 * ‖p‖) * ‖H - K‖ +
      (‖db‖ + 2 * ‖K‖ + |gz|) * ‖p - q‖ + ‖gx - hx‖ + |gz - hz| * ‖q‖ := by
  rw [sourceDerivativeJet_sub]
  have h1 := (p - q).opNorm_comp_le db
  have h2 : ‖(H - K).flip b‖ ≤ ‖H - K‖ * ‖b‖ := by
    simpa only [ContinuousLinearMap.opNorm_flip] using (H - K).flip.le_opNorm b
  have h3 := ((dualSquaredDifferential p).opNorm_comp_le (H - K)).trans
    (mul_le_mul_of_nonneg_right (dualSquaredDifferential_norm_le p) (norm_nonneg _))
  have h4 := ((dualSquaredDifferential (p - q)).opNorm_comp_le K).trans
    (mul_le_mul_of_nonneg_right (dualSquaredDifferential_norm_le (p - q)) (norm_nonneg _))
  have h5 : ‖gz • (p - q) + (gz - hz) • q‖ ≤
      |gz| * ‖p - q‖ + |gz - hz| * ‖q‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using
      norm_add_le (gz • (p - q)) ((gz - hz) • q)
  have hsum := norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
      (norm_add_le_of_le h1 h2) h3) h4) (le_refl ‖gx - hx‖)) h5
  exact hsum.trans_eq (by ring)



theorem sourceDerivativeJet_weighted_norm_sub_le
    (b : V) (db : V →L[ℝ] V) (p q : D) (H K : V →L[ℝ] D)
    (gx hx : D) (gz hz : ℝ) {w eta B B1 L Hmax E d Lx Lz : ℝ}
    (hw : 1 ≤ w) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1)
    (hL : 0 ≤ L) (hHmax : 0 ≤ Hmax)
    (hb : ‖b‖ ≤ B) (hdb : ‖db‖ ≤ B1) (hgz : |gz| ≤ L)
    (hp : w * ‖p‖ ≤ eta) (hq : w * ‖q‖ ≤ eta)
    (hK : w * ‖K‖ ≤ Hmax) (hHK : w * ‖H - K‖ ≤ E)
    (hpq : w * ‖p - q‖ ≤ d) (hxx : w * ‖gx - hx‖ ≤ Lx * d)
    (hzz : w * |gz - hz| ≤ Lz * d) :
    w * ‖sourceDerivativeJet b db p H gx gz - sourceDerivativeJet b db q K hx hz‖ ≤
      (B + 2 * eta) * E + (B1 + 2 * Hmax + L + Lx + Lz * eta) * d := by
  have hw0 : 0 ≤ w := le_trans zero_le_one hw
  have hpn : ‖p‖ ≤ eta := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (norm_nonneg p)]
  have hqn : ‖q‖ ≤ eta := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (norm_nonneg q)]
  have hKn : ‖K‖ ≤ Hmax := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (norm_nonneg K)]
  have hmain := mul_le_mul_of_nonneg_left
    (sourceDerivativeJet_norm_sub_le b db p q H K gx hx gz hz) hw0
  have h1 := mul_le_mul_of_nonneg_left hHK
    (show 0 ≤ B + 2 * eta by positivity)
  have h1a := mul_le_mul_of_nonneg_right (add_le_add hb
    (mul_le_mul_of_nonneg_left hpn (show (0 : ℝ) ≤ 2 by norm_num)))
      (mul_nonneg hw0 (norm_nonneg (H - K)))
  have h2 := mul_le_mul_of_nonneg_left hpq
    (show 0 ≤ B1 + 2 * Hmax + L by positivity)
  have h2a := mul_le_mul_of_nonneg_right
    (add_le_add (add_le_add hdb
      (mul_le_mul_of_nonneg_left hKn (show (0 : ℝ) ≤ 2 by norm_num))) hgz)
      (mul_nonneg hw0 (norm_nonneg (p - q)))
  have h3 := mul_le_mul_of_nonneg_left hzz heta
  have h3a := mul_le_mul_of_nonneg_left hqn (mul_nonneg hw0 (abs_nonneg (gz - hz)))
  nlinarith


noncomputable def forcingSpaceDeriv (G : V → ℝ → ℝ) (x : V) (z : ℝ) : D :=
  (fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, z)).comp
    (ContinuousLinearMap.inl ℝ V ℝ)


noncomputable def forcingScalarDeriv (G : V → ℝ → ℝ) (x : V) (z : ℝ) : ℝ :=
  fderiv ℝ (fun p : V × ℝ => G p.1 p.2) (x, z) (0, 1)




theorem gaugeSource_weighted_fderiv_sub_bound
    {b : V → V} {G : V → ℝ → ℝ} {u v : V → ℝ} {x : V}
    {eta B B1 L Hmax E d Lx Lz : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1) (hL : 0 ≤ L)
    (hHmax : 0 ≤ Hmax) (hLx : 0 ≤ Lx) (hLz : 0 ≤ Lz)
    (hb : DifferentiableAt ℝ b x) (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (hdu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (hdv : DifferentiableAt ℝ (fderiv ℝ v) x)
    (hGu : DifferentiableAt ℝ (fun p : V × ℝ => G p.1 p.2) (x, u x))
    (hGv : DifferentiableAt ℝ (fun p : V × ℝ => G p.1 p.2) (x, v x))
    (hbb : ‖b x‖ ≤ B) (hdb : ‖fderiv ℝ b x‖ ≤ B1)
    (hgz : |forcingScalarDeriv G x (u x)| ≤ L)
    (hGX : ‖forcingSpaceDeriv G x (u x) - forcingSpaceDeriv G x (v x)‖ ≤
      Lx * |u x - v x|)
    (hGZ : |forcingScalarDeriv G x (u x) - forcingScalarDeriv G x (v x)| ≤
      Lz * |u x - v x|)
    (hpu : (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ eta)
    (hpv : (1 + ‖x‖) * ‖fderiv ℝ v x‖ ≤ eta)
    (hHv : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ Hmax)
    (hHuv : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ u) x -
      fderiv ℝ (fderiv ℝ v) x‖ ≤ E)
    (huv : (1 + ‖x‖) * |u x - v x| ≤ d)
    (hpuv : (1 + ‖x‖) * ‖fderiv ℝ u x - fderiv ℝ v x‖ ≤ d) :
    (1 + ‖x‖) * ‖fderiv ℝ (gaugeSource b G u) x -
      fderiv ℝ (gaugeSource b G v) x‖ ≤
      (B + 2 * eta) * E + (B1 + 2 * Hmax + L + Lx + Lz * eta) * d := by
  rw [gaugeSource_fderiv_eq_jet hb hu hdu hGu, gaugeSource_fderiv_eq_jet hb hv hdv hGv]
  apply sourceDerivativeJet_weighted_norm_sub_le _ _ _ _ _ _ _ _ _ _
    (by linarith [norm_nonneg x]) heta hB hB1 hL hHmax hbb hdb hgz
    hpu hpv hHv hHuv hpuv
  · calc
      _ ≤ (1 + ‖x‖) * (Lx * |u x - v x|) :=
        mul_le_mul_of_nonneg_left hGX (by positivity)
      _ = Lx * ((1 + ‖x‖) * |u x - v x|) := by ring
      _ ≤ Lx * d := mul_le_mul_of_nonneg_left huv hLx
  · calc
      _ ≤ (1 + ‖x‖) * (Lz * |u x - v x|) :=
        mul_le_mul_of_nonneg_left hGZ (by positivity)
      _ = Lz * ((1 + ‖x‖) * |u x - v x|) := by ring
      _ ≤ Lz * d := mul_le_mul_of_nonneg_left huv hLz

end PoincareConjecture.M35.RadialGauge
