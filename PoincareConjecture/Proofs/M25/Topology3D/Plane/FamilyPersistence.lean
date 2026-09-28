import PoincareConjecture.Proofs.M25.Topology3D.Plane.Tube
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SmoothAbsolute










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_curve_embedding_margin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
    {a b : ℝ} (hab : a ≤ b)
    (hi : ∀ z ∈ Icc a b, Injective (c z))
    (hm : ∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (c z) q)) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ Ioo (a - m) (b + m),
      Injective (c z) ∧ ∀ q : sphere (0 : E) 1,
        Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (c z) q) := by
  obtain ⟨m, hm0, w, hw, _, htrack, hreg⟩ :=
    exists_uniform_curveAnnularNeighborhood o q0 c hc hab hi hm
  refine ⟨m, hm0, ?_⟩
  intro z hz
  have hmem (q : sphere (0 : E) 1) :
      (z, (q : E)) ∈ Ioo (a - m) (b + m) ×ˢ {x : E | |‖x‖ - 1| < w} := by
    refine ⟨hz, ?_⟩
    change |‖(q : E)‖ - 1| < w
    simpa only [norm_eq_of_mem_sphere q, sub_self, abs_zero] using hw
  constructor
  · intro q r heq
    have hh := htrack (hmem q) (hmem r) (Prod.ext rfl (by
      simpa only [curveAnnularExtension_apply_sphere] using heq))
    exact Subtype.ext (congrArg Prod.snd hh)
  · intro q
    let G : E → E := fun x => curveAnnularExtension o q0 c (z, x)
    have hG : DifferentiableAt ℝ G (q : E) :=
      (((hreg (z, (q : E)) (hmem q)).2.1).comp (q : E)
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have hGc (r : sphere (0 : E) 1) : G r = c z r :=
      curveAnnularExtension_apply_sphere o q0 c z r
    have hj : Injective (mvfderiv (𝓡 1) (c z) q) := by
      rw [mvfderiv_sphere_restriction q hG hGc]
      exact ((hreg (z, (q : E)) (hmem q)).2.2).comp
        (injective_mvfderiv_subtypeVal_sphere q)
    intro u v huv
    apply hj
    exact congrArg (NormedSpace.fromTangentSpace (c z q)) huv




theorem exists_smooth_interval_clamp {a b d : ℝ} (hab : a ≤ b) (hd : 0 < d) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧
      (∀ z, θ z ∈ Icc (a - d) (b + d)) ∧ ∀ z ∈ Icc a b, θ z = z := by
  let L := a - d
  let U := b + d
  have hLU : L < U := by dsimp [L, U]; linarith
  obtain ⟨ρ, hρ, _, hlip, htail, _, _⟩ := exists_smooth_absolute_rounding (half_pos hd)
  let θ : ℝ → ℝ := fun z => (L + U + ρ (z - L) - ρ (z - U)) / 2
  have hθ : ContDiff ℝ ∞ θ :=
    ((contDiff_const.add (hρ.comp (contDiff_id.sub contDiff_const))).sub
      (hρ.comp (contDiff_id.sub contDiff_const))).div_const 2
  refine ⟨θ, hθ, ?_, ?_⟩
  · intro z
    have hh := hlip.dist_le_mul (z - L) (z - U)
    rw [Real.dist_eq, Real.dist_eq,
      show (z - L) - (z - U) = U - L by ring,
      abs_of_pos (sub_pos.mpr hLU)] at hh
    simp only [NNReal.coe_one, one_mul] at hh
    have hb := abs_le.mp hh
    change L ≤ θ z ∧ θ z ≤ U
    dsimp only [θ]
    constructor <;> linarith [hb.1, hb.2]
  · intro z hz
    have hzL : 0 ≤ z - L := by dsimp [L]; linarith [hz.1]
    have hzU : z - U ≤ 0 := by dsimp [U]; linarith [hz.2]
    have hleft : ρ (z - L) = z - L := by
      rw [htail (z - L) (by rw [abs_of_nonneg hzL]; dsimp [L]; linarith [hz.1]),
        abs_of_nonneg hzL]
    have hright : ρ (z - U) = -(z - U) := by
      rw [htail (z - U) (by rw [abs_of_nonpos hzU]; dsimp [U]; linarith [hz.2]),
        abs_of_nonpos hzU]
    dsimp only [θ]
    rw [hleft, hright]
    ring

end PoincareConjecture.M25.Topology3D
