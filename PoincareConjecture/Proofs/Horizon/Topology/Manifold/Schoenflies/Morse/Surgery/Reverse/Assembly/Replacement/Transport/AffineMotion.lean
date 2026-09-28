import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.VerticalMotion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.CodimensionZero



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Reverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]



theorem exists_vertical_affine_motion_within
    {K O : Set (E × Real)} (hK : IsCompact K) (hO : IsOpen O)
    (d k : Real) (hk : 0 < k)
    (htrace : ∀ p ∈ K, ∀ t ∈ Icc (0 : Real) 1,
      (p.1, (1 - t) * p.2 + t * (d + k * p.2)) ∈ O) :
    ∃ J : Set (E × Real), IsCompact J ∧ J ⊆ O ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ p ∉ J, F p = p) ∧
        (∀ p, (F p).1 = p.1) ∧
        (∀ p ∈ K, F p = (p.1, d + k * p.2)) ∧
        ∀ x : E, StrictMono (fun z : Real => (F (x, z)).2) := by
  let H : Real × (E × Real) -> E × Real :=
    fun z => (z.2.1, (1 - z.1) * z.2.2 + z.1 * (d + k * z.2.2))
  have hH : ContDiff Real ∞ H := by fun_prop
  have hcoef (t : Real) (ht : t ∈ Icc (0 : Real) 1) : 0 < 1 - t + t * k := by
    by_cases ht0 : t = 0
    · simp [ht0]
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have := mul_pos htp hk
      linarith [ht.2]
  have hinj (t : Real) (ht : t ∈ Icc (0 : Real) 1) : Injective (fun p => H (t, p)) := by
    intro p q hpq
    have hf := congrArg Prod.fst hpq
    change p.1 = q.1 at hf
    have hs := congrArg Prod.snd hpq
    change (1 - t) * p.2 + t * (d + k * p.2) = (1 - t) * q.2 + t * (d + k * q.2) at hs
    apply Prod.ext hf
    apply (mul_left_cancel₀ (hcoef t ht).ne')
    nlinarith [hs]
  have hder (t : Real) (ht : t ∈ Icc (0 : Real) 1) (p : E × Real) :
      Bijective (fderiv Real (fun q => H (t, q)) p) := by
    let L : E × Real →L[Real] E × Real :=
      (ContinuousLinearMap.fst Real E Real).prod
        ((1 - t + t * k) • ContinuousLinearMap.snd Real E Real)
    have heq : (fun q => H (t, q)) = fun q => L q + (0, t * d) := by
      funext q
      ext
      · change q.1 = q.1 + 0
        exact (add_zero _).symm
      · change (1 - t) * q.2 + t * (d + k * q.2) = (1 - t + t * k) * q.2 + t * d
        ring
    rw [heq, (L.hasFDerivAt.add_const (0, t * d)).fderiv]
    have hLi : Injective L := by
      intro p q hpq
      have hf := congrArg Prod.fst hpq
      change p.1 = q.1 at hf
      have hs := congrArg Prod.snd hpq
      apply Prod.ext hf
      exact mul_left_cancel₀ (hcoef t ht).ne' hs
    exact ⟨hLi, LinearMap.injective_iff_surjective.mp hLi⟩
  obtain ⟨e, he, heq, _, hei⟩ := exists_spacetime_neighborhood_of_codimZero_isotopy
    (a := 0) (b := 1) hK H hH (fun t ht => (hinj t ht).injOn)
    (fun t ht p _ => hder t ht p)
  obtain ⟨W, hW, hWc, hWon⟩ := exists_velocity_extension_of_compact_isotopy
    hK H hH e he hei (fun t ht p hp => heq (he ⟨ht, hp⟩))
  let T : Set (E × Real) := H '' (Icc (0 : Real) 1 ×ˢ K)
  have hT : IsCompact T := (isCompact_Icc.prod hK).image hH.continuous
  have hTO : T ⊆ O := by
    rintro _ ⟨⟨t, p⟩, ⟨ht, hp⟩, rfl⟩
    exact htrace p hp t ht
  obtain ⟨J, hJ, hTJ, hJO⟩ := exists_compact_between hT hO hTO
  obtain ⟨chi, hchi, hchi0, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(Real, E × Real)
      hT.isClosed hTJ (n := ⊤)
  let Z : Real × (E × Real) -> E × Real := fun p => (0, chi p.2 * (W p).2)
  have hZ : ContDiff Real ∞ Z :=
    contDiff_const.prodMk ((chi.contMDiff.contDiff.comp contDiff_snd).mul hW.snd)
  have hZc : HasCompactSupport Z := by
    apply hWc.of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closure
    intro p hp
    by_contra hn
    exact hp (by simp only [Z, image_eq_zero_of_notMem_tsupport hn, Prod.snd_zero, mul_zero, Prod.mk_zero_zero])
  have hzero (t : Real) (p : E × Real) (hp : p ∉ J) : Z (t, p) = 0 := by
    simp only [Z, hchi0 p hp, zero_mul, Prod.mk_zero_zero]
  have hpath (t : Real) (p : E × Real) : HasDerivAt (fun r => H (r, p))
      (0, d + k * p.2 - p.2) t := by
    have hd := (hasDerivAt_const t p.1).prodMk
      ((((hasDerivAt_const t (1 : Real)).sub (hasDerivAt_id t)).mul_const p.2).add
        ((hasDerivAt_id t).mul_const (d + k * p.2)))
    convert! hd using 1
    simp
    ring
  have htime (t : Real) (p : E × Real) : fderiv Real H (t, p) (1, 0) =
      (0, d + k * p.2 - p.2) := by
    have hd := (hH.differentiable (by simp) (t, p)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t p))
    exact hd.unique (hpath t p)
  have hZon (t : Real) (ht : t ∈ Icc (0 : Real) 1) (p : E × Real) (hp : p ∈ K) :
      Z (t, H (t, p)) = (0, d + k * p.2 - p.2) := by
    have hm : H (t, p) ∈ T := ⟨(t, p), ⟨ht, hp⟩, rfl⟩
    simp only [Z, hchi.self_of_nhdsSet _ hm, one_mul, hWon t ht p hp, htime]
  obtain ⟨Phi, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support Z hZ hJ hzero
  have hfirst (s t : Real) (p : E × Real) : (Phi s t p).1 = p.1 := by
    have hd (r : Real) : HasDerivAt (fun r => (Phi s r p).1) 0 r :=
      (ContinuousLinearMap.fst Real E Real).hasFDerivAt.comp_hasDerivAt r (ho s p r)
    have he := is_const_of_deriv_eq_zero
      (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) t s
    simpa only [hi] using he
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hZc hZ (by simp)
  have hLip (s : Real) : LipschitzWith L (fun p => Z (s, p)) := by
    convert! hL.comp (LipschitzWith.prodMk_left s) using 1
    simp
  refine ⟨J, hJ, hJO, Phi 0 1, hfix 0 1, hfirst 0 1, ?_,
    strictMono_vertical_of_compact_support (Phi 0 1).toHomeomorph (hfirst 0 1) hJ (hfix 0 1)⟩
  intro p hp
  have he := ODE_solution_unique hLip
    (f := fun t => Phi 0 t p) (g := fun t => H (t, p))
    ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun t _ => (ho 0 p t).hasDerivWithinAt)
    (hH.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun t ht => by
      rw [hZon t ⟨ht.1, ht.2.le⟩ p hp]
      exact (hpath t p).hasDerivWithinAt)
    (by simp only [hi, H, sub_zero, one_mul, zero_mul, add_zero, Prod.eta])
  simpa only [H, sub_self, zero_mul, one_mul, zero_add]
    using he (show (1 : Real) ∈ Icc 0 1 by simp)

end Poincare.Manifold.Schoenflies.Reverse
