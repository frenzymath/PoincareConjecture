import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Push.Graph
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

theorem exists_vertical_translation_within
    {K O : Set (E × Real)} (hK : IsCompact K) (hO : IsOpen O) (d : Real)
    (htrace : ∀ p ∈ K, ∀ t ∈ Icc (0 : Real) 1, (p.1, p.2 + t * d) ∈ O) :
    ∃ J : Set (E × Real), IsCompact J ∧ J ⊆ O ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ p ∉ J, F p = p) ∧
        (∀ p, (F p).1 = p.1) ∧
        (∀ p ∈ K, F p = (p.1, p.2 + d)) ∧
        (∀ x : E, StrictMono (fun z : Real => (F (x, z)).2)) := by
  let T : Set (E × Real) :=
    (fun p : (E × Real) × Real => (p.1.1, p.1.2 + p.2 * d)) '' (K ×ˢ Icc 0 1)
  have hT : IsCompact T := (hK.prod isCompact_Icc).image (by fun_prop)
  have hTO : T ⊆ O := by
    rintro _ ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩
    exact htrace p hp t ht
  obtain ⟨J, hJ, hTJ, hJO⟩ := exists_compact_between hT hO hTO
  obtain ⟨chi, hchi, hchi0, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(Real, E × Real)
      hT.isClosed hTJ (n := ⊤)
  let V : E × Real → E × Real := fun p => (0, chi p * d)
  have hV : ContDiff Real ∞ V :=
    contDiff_const.prodMk (chi.contMDiff.contDiff.mul contDiff_const)
  have hVzero (p : E × Real) (hp : p ∉ J) : V p = 0 := by
    simp [V, hchi0 p hp]
  have hVline (p : E × Real) (hp : p ∈ K) (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      V (p.1, p.2 + t * d) = (0, d) := by
    have hmem : (p.1, p.2 + t * d) ∈ T := ⟨(p, t), ⟨hp, ht⟩, rfl⟩
    simp only [V, hchi.self_of_nhdsSet _ hmem, one_mul]
  obtain ⟨Phi, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support
      (fun p : Real × (E × Real) => V p.2) (hV.comp contDiff_snd) hJ
      (fun _ p hp => hVzero p hp)
  have hfirst (s t : Real) (p : E × Real) : (Phi s t p).1 = p.1 := by
    have hd (r : Real) : HasDerivAt (fun r => (Phi s r p).1) 0 r :=
      (ContinuousLinearMap.fst Real E Real).hasFDerivAt.comp_hasDerivAt r (ho s p r)
    have he := is_const_of_deriv_eq_zero
      (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) t s
    simpa only [hi] using he
  have hVc : HasCompactSupport V := by
    apply hJ.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hJ.isClosed
    intro p hp
    by_contra hn
    exact hp (hVzero p hn)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  refine ⟨J, hJ, hJO, Phi 0 1, hfix 0 1, hfirst 0 1, ?_, ?_⟩
  · intro p hp
    have hd (t : Real) : HasDerivAt (fun r : Real => (p.1, p.2 + r * d)) (0, d) t := by
      simpa using (hasDerivAt_const t p.1).prodMk
        (((hasDerivAt_id t).mul_const d).const_add p.2)
    have he := ODE_solution_unique (v := fun _ => V) (fun _ => hL)
      (f := fun t => Phi 0 t p) (g := fun t : Real => (p.1, p.2 + t * d))
      ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t _ => (ho 0 p t).hasDerivWithinAt)
      (by fun_prop)
      (fun t ht => by
        rw [hVline p hp t ⟨ht.1, ht.2.le⟩]
        exact (hd t).hasDerivWithinAt)
      (by simp only [hi, zero_mul, add_zero, Prod.eta])
    simpa only [one_mul] using he (show (1 : Real) ∈ Icc 0 1 by simp)
  · exact strictMono_vertical_of_compact_support
      (Phi 0 1).toHomeomorph (hfirst 0 1) hJ (hfix 0 1)

theorem exists_translation_along_within
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] {v : V} (hv : ‖v‖ = 1)
    {K O : Set V} (hK : IsCompact K) (hO : IsOpen O) (d : Real)
    (htrace : ∀ p ∈ K, ∀ t ∈ Icc (0 : Real) 1, p + (t * d) • v ∈ O) :
    ∃ J : Set V, IsCompact J ∧ J ⊆ O ∧
      ∃ F : Diffeomorph 𝓘(Real, V) 𝓘(Real, V) V V ∞,
        (∀ p ∉ J, F p = p) ∧
        (∀ p, (Real ∙ v)ᗮ.orthogonalProjectionOnto (F p) =
          (Real ∙ v)ᗮ.orthogonalProjectionOnto p) ∧
        (∀ p ∈ K, F p = p + d • v) ∧
        (∀ x : (Real ∙ v)ᗮ,
          StrictMono (fun z : Real => inner Real v (F (z • v + (x : V))))) := by
  let H := ((ContinuousLinearEquiv.prodComm Real (Real ∙ v)ᗮ Real).trans
    (Poincare.Geometry.Euclidean.heightCoordinates hv)).toDiffeomorph
  have hH (p : (Real ∙ v)ᗮ × Real) : H p = p.2 • v + (p.1 : V) := rfl
  have hHp (p : (Real ∙ v)ᗮ × Real) :
      (Real ∙ v)ᗮ.orthogonalProjectionOnto (H p) = p.1 := by
    rw [hH]
    simp
  have hHh (p : (Real ∙ v)ᗮ × Real) : inner Real v (H p) = p.2 := by
    change inner Real v
      (Poincare.Geometry.Euclidean.heightCoordinates hv (p.2, p.1)) = p.2
    exact Poincare.Geometry.Euclidean.inner_heightCoordinates hv _
  have hHadd (p : (Real ∙ v)ᗮ × Real) (r : Real) :
      H (p.1, p.2 + r) = H p + r • v := by
    simp only [hH, add_smul]
    abel
  obtain ⟨J, hJ, hJO, G, hGfix, hGfirst, hGmove, hGmono⟩ :=
    exists_vertical_translation_within (hK.image H.symm.continuous)
      (hO.preimage H.continuous) d (by
        rintro _ ⟨p, hp, rfl⟩ t ht
        change H ((H.symm p).1, (H.symm p).2 + t * d) ∈ O
        rw [hHadd, H.apply_symm_apply]
        exact htrace p hp t ht)
  let F := (H.symm.trans G).trans H
  refine ⟨H '' J, hJ.image H.continuous, ?_, F, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hJO hp
  · intro p hp
    have hn : H.symm p ∉ J := by
      intro hmem
      exact hp ⟨H.symm p, hmem, H.apply_symm_apply p⟩
    change H (G (H.symm p)) = p
    rw [hGfix _ hn, H.apply_symm_apply]
  · intro p
    change (Real ∙ v)ᗮ.orthogonalProjectionOnto (H (G (H.symm p))) = _
    rw [hHp, hGfirst, ← hHp, H.apply_symm_apply]
  · intro p hp
    change H (G (H.symm p)) = p + d • v
    rw [hGmove _ (mem_image_of_mem H.symm hp), hHadd, H.apply_symm_apply]
  · intro x a b hab
    change inner Real v (H (G (H.symm (H (x, a))))) <
      inner Real v (H (G (H.symm (H (x, b)))))
    simp only [H.symm_apply_apply, hHh]
    exact hGmono x hab

end Poincare.Manifold.Schoenflies.Reverse
