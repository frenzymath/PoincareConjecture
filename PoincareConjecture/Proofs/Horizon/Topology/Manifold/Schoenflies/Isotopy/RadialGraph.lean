import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Flow
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Extension.CompactSupport
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.SpecialFunctions.Log.Deriv



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩



theorem exists_radial_sphere_isotopy
    (a : S2 -> Real) (ha : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ a) :
    ∃ Phi : Real -> Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x, Phi 0 x = x) ∧
      ContDiff Real ∞ (fun z : Real × E3 => Phi z.1 z.2) ∧
      (∃ K : Set E3, IsCompact K ∧ ∀ t x, x ∉ K -> Phi t x = x) ∧
      ∀ t ∈ Icc (0 : Real) 1, ∀ p : S2,
        Phi t p = Real.exp (t * a p) • (p : E3) := by
  let U : TopologicalSpace.Opens E3 := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let radial : U -> S2 := fun x =>
    ⟨‖x.val‖⁻¹ • x.val, by simp [norm_smul, norm_ne_zero_iff.mpr x.property]⟩
  have hn : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞ (fun x : U => ‖x.val‖) := by
    intro x
    exact (contDiffAt_norm Real x.property).contMDiffAt.comp x (contMDiff_subtype_val x)
  have hr : ContMDiff (𝓡 3) (𝓡 2) ∞ radial :=
    ((hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul
      contMDiff_subtype_val).codRestrict_sphere _
  let V : E3 -> E3 := fun x => if hx : x = 0 then 0 else a (radial ⟨x, hx⟩) • x
  have hV : ContDiffOn Real ∞ V U := by
    intro x hx
    have hs : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => V y.val) := by
      convert (ha.comp hr).smul contMDiff_subtype_val using 1
      funext y
      exact dif_neg y.property
    exact (contMDiffAt_subtype_iff.mp (hs ⟨x, hx⟩)).contDiffAt.contDiffWithinAt
  let g : Real × S2 -> E3 := fun z => Real.exp (z.1 * a z.2) • (z.2 : E3)
  have hg : Continuous g :=
    (continuous_fst.mul (ha.continuous.comp continuous_snd)).rexp.smul
      (continuous_subtype_val.comp continuous_snd)
  let K := g '' (Icc (0 : Real) 1 ×ˢ (univ : Set S2))
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_univ).image hg
  have hgne (t : Real) (p : S2) : g (t, p) ≠ 0 :=
    smul_ne_zero (Real.exp_pos _).ne' (ne_zero_of_mem_unit_sphere p)
  have hKU : K ⊆ U := by
    rintro x ⟨⟨t, p⟩, _, rfl⟩
    exact hgne t p
  obtain ⟨W, hW, hWc, hWeq⟩ :=
    Poincare.Analysis.exists_contDiff_compactSupport_extension_on_compact hK U.isOpen hKU V hV
  obtain ⟨Phi, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support
      (fun z : Real × E3 => W z.2) (hW.comp contDiff_snd) hWc.isCompact
      (fun _ _ hx => image_eq_zero_of_notMem_tsupport hx)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hWc hW (by simp)
  refine ⟨Phi 0, hi 0, hs 0, ⟨tsupport W, hWc.isCompact, hfix 0⟩, ?_⟩
  intro t ht p
  have hradial (s : Real) : radial ⟨g (s, p), hgne s p⟩ = p := by
    apply Subtype.ext
    change ‖Real.exp (s * a p) • (p : E3)‖⁻¹ •
      (Real.exp (s * a p) • (p : E3)) = (p : E3)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_eq_of_mem_sphere p, mul_one, smul_smul, inv_mul_cancel₀ (Real.exp_pos _).ne', one_smul]
  have hvel (s : Real) (hs : s ∈ Icc (0 : Real) 1) :
      W (g (s, p)) = (Real.exp (s * a p) * a p) • (p : E3) := by
    rw [hWeq ⟨(s, p), ⟨hs, mem_univ _⟩, rfl⟩]
    change (if hx : g (s, p) = 0 then 0 else a (radial ⟨g (s, p), hx⟩) • g (s, p)) = _
    rw [dif_neg (hgne s p), hradial]
    simp only [g, smul_smul, mul_comm]
  have hder (s : Real) : HasDerivAt (fun s => g (s, p))
      ((Real.exp (s * a p) * a p) • (p : E3)) s := by
    simpa only [g, id_eq, one_mul] using
      (((hasDerivAt_id s).mul_const (a p)).exp).smul_const (p : E3)
  have heq := ODE_solution_unique (v := fun _ => W) (fun _ => hL)
    (f := fun s => Phi 0 s p) (g := fun s => g (s, p))
    ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun s _ => (ho 0 p s).hasDerivWithinAt)
    (hg.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun s hs => by rw [hvel s (Ico_subset_Icc_self hs)]; exact (hder s).hasDerivWithinAt)
    (by simp [hi, g])
  exact heq ht



theorem exists_radial_sphere_extension
    (r : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Real)
    (hr : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ r)
    (hpos : ∀ p, 0 < r p) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace Real (Fin 3)) (EuclideanSpace Real (Fin 3)) ∞,
      (∃ K : Set (EuclideanSpace Real (Fin 3)), IsCompact K ∧
        ∀ x ∉ K, F x = x) ∧
      ∀ p : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
        F p = r p • (p : EuclideanSpace Real (Fin 3)) := by
  have hlog : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p => Real.log (r p)) := by
    intro p
    exact (Real.contDiffAt_log.mpr (hpos p).ne').contMDiffAt.comp p (hr p)
  obtain ⟨Phi, _, _, ⟨K, hK, hfix⟩, hmotion⟩ :=
    exists_radial_sphere_isotopy (fun p => Real.log (r p)) hlog
  refine ⟨Phi 1, ⟨K, hK, hfix 1⟩, fun p => ?_⟩
  simpa [Real.exp_log (hpos p)] using hmotion 1 (by simp) p

end Poincare.Manifold.Schoenflies
