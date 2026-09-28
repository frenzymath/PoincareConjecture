import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Flow
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Extension.Compact
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

theorem exists_velocity_extension_of_compact_isotopy
    {a b : Real} {K : Set E} (hK : IsCompact K)
    (G : Real × E -> E) (hG : ContDiff Real ∞ G)
    (e : OpenPartialHomeomorph (Real × E) (Real × E))
    (he : Icc a b ×ˢ K ⊆ e.source)
    (hei : ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, Real × E) ∞ e.symm e.target)
    (hagree : ∀ t ∈ Icc a b, ∀ x ∈ K, e (t, x) = (t, G (t, x))) :
    ∃ W : Real × E -> E, ContDiff Real ∞ W ∧ HasCompactSupport W ∧
      ∀ t ∈ Icc a b, ∀ x ∈ K,
        W (t, G (t, x)) = fderiv Real G (t, x) (1, 0) := by
  let S := (fun p : Real × E => (p.1, G p)) '' (Icc a b ×ˢ K)
  have hS : IsCompact S := (isCompact_Icc.prod hK).image
    (continuous_fst.prodMk hG.continuous)
  have hStarget : S ⊆ e.target := by
    rintro p ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    change (t, G (t, x)) ∈ e.target
    rw [← hagree t ht x hx]
    exact e.map_source (he ⟨ht, hx⟩)
  let V : Real × E -> E := fun p => fderiv Real G p (1, 0)
  have hV : ContDiff Real ∞ V := (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hu : ContDiffOn Real ∞ (V ∘ e.symm) e.target := by
    intro p hp
    exact ((hV.contMDiff (e.symm p)).comp p
      ((hei p hp).contMDiffAt (e.open_target.mem_nhds hp))).contDiffAt.contDiffWithinAt
  obtain ⟨H, _, hH, _, hSH, _, heq⟩ :=
    Poincare.Analysis.exists_contDiff_extension_near_compact hS e.open_target hStarget
      (V ∘ e.symm) hu
  obtain ⟨r, hr, hSr⟩ := hS.isBounded.subset_ball_lt 0 (0 : Real × E)
  let chi : ContDiffBump (0 : Real × E) := ⟨r, r + 1, hr, lt_add_one r⟩
  refine ⟨fun p => chi p • H p, chi.contDiff.smul hH,
    chi.hasCompactSupport.smul_right, ?_⟩
  intro t ht x hx
  change chi (t, G (t, x)) • H (t, G (t, x)) = fderiv Real G (t, x) (1, 0)
  have hp : (t, G (t, x)) ∈ S := ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  rw [chi.one_of_mem_closedBall (ball_subset_closedBall (hSr hp)), one_smul,
    heq (hSH hp)]
  change V (e.symm (t, G (t, x))) = V (t, x)
  rw [← hagree t ht x hx, e.left_inv (he ⟨ht, hx⟩)]

theorem exists_ambient_isotopy_of_compact_isotopy
    {a b : Real} {K : Set E} (hK : IsCompact K)
    (G : Real × E -> E) (hG : ContDiff Real ∞ G)
    (e : OpenPartialHomeomorph (Real × E) (Real × E))
    (he : Icc a b ×ˢ K ⊆ e.source)
    (hei : ContMDiffOn 𝓘(Real, Real × E) 𝓘(Real, Real × E) ∞ e.symm e.target)
    (hagree : ∀ t ∈ Icc a b, ∀ x ∈ K, e (t, x) = (t, G (t, x))) :
    ∃ Phi : Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff Real ∞ (fun p : Real × E => Phi p.1 p.2) ∧
      (∃ S : Set E, IsCompact S ∧ ∀ t x, x ∉ S -> Phi t x = x) ∧
      ∀ t ∈ Icc a b, ∀ x ∈ K, Phi t (G (a, x)) = G (t, x) := by
  obtain ⟨W, hW, hWc, hWon⟩ :=
    exists_velocity_extension_of_compact_isotopy hK G hG e he hei hagree
  have hzero : ∀ t x, x ∉ Prod.snd '' tsupport W -> W (t, x) = 0 := by
    intro t x hx
    apply image_eq_zero_of_notMem_tsupport
    exact fun hp => hx ⟨(t, x), hp, rfl⟩
  obtain ⟨Phi, hi, hs, ho, hfix⟩ := exists_diffeomorph_evolution_of_compact_spatial_support
    W hW (hWc.isCompact.image continuous_snd) hzero
  refine ⟨Phi a, hi a, hs a,
    ⟨Prod.snd '' tsupport W, hWc.isCompact.image continuous_snd, hfix a⟩, ?_⟩
  intro t ht x hx
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hWc hW (by simp)
  have hLip (s : Real) : LipschitzWith L (fun y => W (s, y)) := by
    convert! hL.comp (LipschitzWith.prodMk_left s) using 1
    simp
  have hpath (s : Real) : HasDerivAt (fun r => G (r, x))
      (fderiv Real G (s, x) (1, 0)) s := by
    exact (hG.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have heq := ODE_solution_unique hLip
    (HasDerivAt.continuousOn (fun s _ => ho a (G (a, x)) s))
    (fun s _ => (ho a (G (a, x)) s).hasDerivWithinAt)
    (hG.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun s hs => by
      change HasDerivWithinAt (fun r => G (r, x)) (W (s, G (s, x))) (Ici s) s
      rw [hWon s (Ico_subset_Icc_self hs) x hx]
      exact (hpath s).hasDerivWithinAt)
    (hi a (G (a, x)))
  exact heq ht

end Poincare.Manifold.Schoenflies
