import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.RadialGraph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Body

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

theorem exists_radial_sphere_isotopy_with_annular_formula
    (a : S2 → Real) (ha : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ a) (δ : Real) :
    ∃ Φ : Real → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x, Φ 0 x = x) ∧
      ContDiff Real ∞ (fun z : Real × E3 => Φ z.1 z.2) ∧
      (∃ K : Set E3, IsCompact K ∧ ∀ t x, x ∉ K → Φ t x = x) ∧
      ∀ t ∈ Icc (0 : Real) 1, ∀ s ∈ Icc (-δ) δ, ∀ p : S2,
        Φ t (Real.exp s • (p : E3)) = Real.exp (t * a p + s) • (p : E3) := by
  let U : TopologicalSpace.Opens E3 := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let radial : U → S2 := fun x =>
    ⟨‖x.val‖⁻¹ • x.val, by simp [norm_smul, norm_ne_zero_iff.mpr x.property]⟩
  have hn : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞ (fun x : U => ‖x.val‖) := by
    intro x
    exact (contDiffAt_norm Real x.property).contMDiffAt.comp x (contMDiff_subtype_val x)
  have hr : ContMDiff (𝓡 3) (𝓡 2) ∞ radial :=
    ((hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul
      contMDiff_subtype_val).codRestrict_sphere _
  let V : E3 → E3 := fun x => if hx : x = 0 then 0 else a (radial ⟨x, hx⟩) • x
  have hV : ContDiffOn Real ∞ V U := by
    intro x hx
    have hs : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => V y.val) := by
      convert (ha.comp hr).smul contMDiff_subtype_val using 1
      funext y
      exact dif_neg y.property
    exact (contMDiffAt_subtype_iff.mp (hs ⟨x, hx⟩)).contDiffAt.contDiffWithinAt
  let g : Real × (Real × S2) → E3 := fun z =>
    Real.exp (z.1 * a z.2.2 + z.2.1) • (z.2.2 : E3)
  have hg : Continuous g :=
    ((continuous_fst.mul (ha.continuous.comp (continuous_snd.comp continuous_snd))).add
      (continuous_fst.comp continuous_snd)).rexp.smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  let K := g '' (Icc (0 : Real) 1 ×ˢ (Icc (-δ) δ ×ˢ (univ : Set S2)))
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_univ)).image hg
  have hgne (t s : Real) (p : S2) : g (t, s, p) ≠ 0 :=
    smul_ne_zero (Real.exp_pos _).ne' (ne_zero_of_mem_unit_sphere p)
  have hKU : K ⊆ U := by
    rintro x ⟨⟨t, s, p⟩, _, rfl⟩
    exact hgne t s p
  obtain ⟨W, hW, hWc, hWeq⟩ :=
    Poincare.Analysis.exists_contDiff_compactSupport_extension_on_compact hK U.isOpen hKU V hV
  obtain ⟨Φ, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support
      (fun z : Real × E3 => W z.2) (hW.comp contDiff_snd) hWc.isCompact
      (fun _ _ hx => image_eq_zero_of_notMem_tsupport hx)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hWc hW (by simp)
  refine ⟨Φ 0, hi 0, hs 0, ⟨tsupport W, hWc.isCompact, hfix 0⟩, ?_⟩
  intro t ht s hsδ p
  have hradial (u : Real) : radial ⟨g (u, s, p), hgne u s p⟩ = p := by
    apply Subtype.ext
    change ‖Real.exp (u * a p + s) • (p : E3)‖⁻¹ •
      (Real.exp (u * a p + s) • (p : E3)) = (p : E3)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_eq_of_mem_sphere p, mul_one, smul_smul, inv_mul_cancel₀ (Real.exp_pos _).ne', one_smul]
  have hvel (u : Real) (hu : u ∈ Icc (0 : Real) 1) :
      W (g (u, s, p)) = (Real.exp (u * a p + s) * a p) • (p : E3) := by
    rw [hWeq ⟨(u, s, p), ⟨hu, hsδ, mem_univ _⟩, rfl⟩]
    change (if hx : g (u, s, p) = 0 then 0 else a (radial ⟨g (u, s, p), hx⟩) •
      g (u, s, p)) = _
    rw [dif_neg (hgne u s p), hradial]
    simp only [g, smul_smul, mul_comm]
  have hder (u : Real) : HasDerivAt (fun u => g (u, s, p))
      ((Real.exp (u * a p + s) * a p) • (p : E3)) u := by
    simpa only [g, id_eq, one_mul] using
      ((((hasDerivAt_id u).mul_const (a p)).add_const s).exp).smul_const (p : E3)
  have heq := ODE_solution_unique (v := fun _ => W) (fun _ => hL)
    (f := fun u => Φ 0 u (Real.exp s • (p : E3))) (g := fun u => g (u, s, p))
    ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun u _ => (ho 0 (Real.exp s • (p : E3)) u).hasDerivWithinAt)
    (hg.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun u hu => by rw [hvel u (Ico_subset_Icc_self hu)]; exact (hder u).hasDerivWithinAt)
    (by simp [hi, g])
  exact heq ht

theorem exists_radial_sphere_extension_with_annular_formula
    (r : S2 → Real) (hr : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ r)
    (hpos : ∀ p, 0 < r p) (δ : Real) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∃ K : Set E3, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
      ∀ s ∈ Icc (-δ) δ, ∀ p : S2,
        F (Real.exp s • (p : E3)) = r p • (Real.exp s • (p : E3)) := by
  have hlog : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p => Real.log (r p)) := by
    intro p
    exact (Real.contDiffAt_log.mpr (hpos p).ne').contMDiffAt.comp p (hr p)
  obtain ⟨Φ, _, _, ⟨K, hK, hfix⟩, hmotion⟩ :=
    exists_radial_sphere_isotopy_with_annular_formula (fun p => Real.log (r p)) hlog δ
  refine ⟨Φ 1, ⟨K, hK, hfix 1⟩, ?_⟩
  intro s hs p
  simpa only [one_mul, Real.exp_add, Real.exp_log (hpos p), smul_smul] using
    hmotion 1 (by simp) s hs p

theorem exists_boundedCylinder_ambient_with_annular_formula (v : E3)
    {δ : Real} (hδ : 0 ≤ δ) :
    ∃ C : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∃ K : Set E3, IsCompact K ∧ ∀ x ∉ K, C x = x) ∧
      (∀ s ∈ Icc (-δ) δ, ∀ p : S2,
        C (Real.exp s • (p : E3)) = boundedCylinderRadius v p • (Real.exp s • (p : E3))) ∧
      (∀ s ∈ Icc (-δ) δ, ∀ p : S2, |inner Real v (p : E3)| ≤ 1 / 2 →
        C (Real.exp s • (p : E3)) =
          (Real.sqrt (1 - inner Real v (p : E3) ^ 2))⁻¹ • (Real.exp s • (p : E3))) ∧
      C '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ inner Real v p}) =
        boundedCylinderNorthernCap v := by
  obtain ⟨C, hsupport, hC⟩ := exists_radial_sphere_extension_with_annular_formula
    (boundedCylinderRadius v) (contMDiff_boundedCylinderRadius v) (boundedCylinderRadius_pos v) δ
  have hCs (p : S2) : C p = boundedCylinderRadius v p • (p : E3) := by
    simpa using hC 0 ⟨by linarith, hδ⟩ p
  refine ⟨C, hsupport, hC, ?_, ?_⟩
  · intro s hs p hp
    rw [hC s hs p, boundedCylinderRadius_of_abs_height_le v p hp]
  ext p
  constructor
  · rintro ⟨q, ⟨hq, hvq⟩, rfl⟩
    exact ⟨⟨q, hq⟩, hvq, (hCs ⟨q, hq⟩).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, ⟨q.property, hq⟩, hCs q⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps
