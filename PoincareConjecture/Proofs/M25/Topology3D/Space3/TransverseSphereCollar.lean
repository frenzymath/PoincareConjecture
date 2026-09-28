import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactProductTube
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Algebra.Module.Equiv

set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem mfderiv_sphere_product_time (C : UnitTwoSphere × ℝ → E3)
    (p : UnitTwoSphere)
    (hC : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) C (p, 0)) :
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) C (p, 0))
        ((0 : TangentSpace (𝓡 2) p), (1 : ℝ)) =
      deriv (fun s : ℝ => C (p, s)) 0 := by
  have htime : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun s : ℝ => (p, s)) 0 := mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hd := (hC.hasMFDerivAt.comp 0 htime.hasMFDerivAt).mfderiv
  rw [mfderiv_prod_right] at hd
  have he := congrArg (fun A : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) →L[ℝ]
      TangentSpace 𝓘(ℝ, E3) (C (p, 0)) => A (1 : ℝ)) hd
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) (fun s : ℝ => C (p, s)) 0) 1 =
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) C (p, 0))
      ((0 : TangentSpace (𝓡 2) p), (1 : ℝ)) at he
  rw [mfderiv_eq_fderiv] at he
  exact he.symm

theorem sphere_product_mfderiv_bijective_of_normal
    (C : UnitTwoSphere × ℝ → E3) (j : UnitTwoSphere → E3)
    (hcentral : ∀ q : UnitTwoSphere, C (q, 0) = j q)
    (p : UnitTwoSphere)
    (hC : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) C (p, 0))
    (hj : Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) j p))
    (N : E3)
    (horth : ∀ v : TangentSpace (𝓡 2) p,
      ⟪N, mfderiv (𝓡 2) 𝓘(ℝ, E3) j p v⟫_ℝ = 0)
    (htrans : ⟪N, (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) C (p, 0))
      ((0 : TangentSpace (𝓡 2) p), (1 : ℝ))⟫_ℝ ≠ 0) :
    Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) C (p, 0)) := by
  let A : (TangentSpace (𝓡 2) p × ℝ) →L[ℝ] E3 :=
    mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) C (p, 0)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) p) := by
    change FiniteDimensional ℝ E2
    infer_instance
  have hslice : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun q : UnitTwoSphere => (q, (0 : ℝ))) p :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hd := (hC.hasMFDerivAt.comp p hslice.hasMFDerivAt).mfderiv
  rw [mfderiv_prod_left] at hd
  have hsame : C ∘ (fun q : UnitTwoSphere => (q, (0 : ℝ))) = j := funext hcentral
  rw [hsame] at hd
  have htangent (v : TangentSpace (𝓡 2) p) :
      A (v, 0) = mvfderiv (𝓡 2) j p v := by
    exact congrArg (fun L => L v) hd.symm
  have hsplit (v : TangentSpace (𝓡 2) p) (s : ℝ) :
      A (v, s) = mvfderiv (𝓡 2) j p v + s • A (0, 1) := by
    have he : (v, s) = (v, (0 : ℝ)) + s • ((0 : TangentSpace (𝓡 2) p), (1 : ℝ)) := by
      simp
    rw [he, map_add, map_smul, htangent]
  have hAi : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    rintro ⟨v, s⟩ hv
    have he := congrArg (fun w : E3 => ⟪N, w⟫_ℝ) hv
    have horth' : ⟪N, mvfderiv (𝓡 2) j p v⟫_ℝ = 0 := horth v
    rw [hsplit, inner_add_right, real_inner_smul_right, horth', inner_zero_right,
      zero_add] at he
    have hs : s = 0 := (mul_eq_zero.mp he).resolve_right htrans
    subst s
    apply Prod.ext
    · apply hj
      change mvfderiv (𝓡 2) j p v = mvfderiv (𝓡 2) j p 0
      simpa only [map_zero] using (htangent v).symm.trans hv
    · rfl
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) p × ℝ) =
      Module.finrank ℝ E3 := by
    change Module.finrank ℝ (E2 × ℝ) = Module.finrank ℝ E3
    simp [E2, E3, Module.finrank_prod]
  exact ⟨hAi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := A.toLinearMap) hdim).mp hAi⟩

theorem exists_transverse_sphere_collar
    (C : UnitTwoSphere × ℝ → E3) (j : UnitTwoSphere → E3)
    {U : Set (UnitTwoSphere × ℝ)} (hU : IsOpen U)
    (hzero : ∀ p : UnitTwoSphere, (p, (0 : ℝ)) ∈ U)
    (hC : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ C U)
    (hcentral : ∀ p : UnitTwoSphere, C (p, 0) = j p)
    (hinj : Function.Injective j)
    (hderiv : ∀ p : UnitTwoSphere, Function.Bijective
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) C (p, 0)))
    {b : ℝ} (hb : 0 < b) :
    ∃ tau0 > (0 : ℝ), tau0 < b ∧ ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
      IsCollarEmbedding (fun z : UnitTwoSphere × ℝ => C (z.1, tau * z.2)) ∧
        (∀ z ∈ (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (UnitTwoSphere × ℝ)),
          (z.1, tau * z.2) ∈ U) ∧
        ∀ p : UnitTwoSphere, C (p, tau * 0) = j p := by
  have hcentral_inj : Function.Injective (fun p : UnitTwoSphere => C (p, 0)) := by
    intro p q hpq
    apply hinj
    simpa only [hcentral] using hpq
  obtain ⟨d, hd, hsource, hi, hregular⟩ :=
    exists_compact_product_regular_tube (E := E2) C hU hzero hC hcentral_inj hderiv
  refine ⟨min d b / 2, div_pos (lt_min hd hb) (by norm_num), ?_, ?_⟩
  · linarith [min_le_right d b]
  · intro tau htau htau0
    have htaud : tau < d := by linarith [min_le_left d b]
    let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 tau htau.ne')
    let R := (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞).prodCongr e.toDiffeomorph
    have hR (z : UnitTwoSphere × ℝ) : R z = (z.1, tau * z.2) := by
      apply Prod.ext
      · rfl
      · change z.2 * tau = tau * z.2
        exact mul_comm _ _
    have hmaps : MapsTo R (univ ×ˢ Ioo (-1 : ℝ) 1) (univ ×ˢ Ioo (-d) d) := by
      intro z hz
      rw [hR]
      refine ⟨mem_univ _, ?_, ?_⟩ <;> nlinarith [hz.2.1, hz.2.2]
    have hRU (z : UnitTwoSphere × ℝ) (hz : z ∈ univ ×ˢ Ioo (-1 : ℝ) 1) : R z ∈ U :=
      hsource (hmaps hz)
    have heq : C ∘ R = (fun z : UnitTwoSphere × ℝ => C (z.1, tau * z.2)) := by
      funext z
      simp only [Function.comp_apply, hR]
    have hemb : IsCollarEmbedding (C ∘ R) := by
      refine ⟨hC.comp R.contMDiff.contMDiffOn (fun z hz => hRU z hz), ?_, ?_⟩
      · intro z hz w hw hzw
        apply R.toEquiv.injective
        exact hi (hmaps hz) (hmaps hw) hzw
      · intro z hz
        have hRd : Function.Injective
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) R z) :=
          (R.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (mem_univ _)
        rw [mfderiv_comp z
          ((hC.contMDiffAt (hU.mem_nhds (hRU z hz))).mdifferentiableAt (by simp))
          (R.mdifferentiable (by simp) z)]
        exact (hregular (R z) (hmaps hz)).1.comp hRd
    refine ⟨heq ▸ hemb, ?_, ?_⟩
    · intro z hz
      simpa only [hR] using hRU z hz
    · intro p
      simpa only [mul_zero] using hcentral p

end PoincareConjecture.M25.Topology3D
