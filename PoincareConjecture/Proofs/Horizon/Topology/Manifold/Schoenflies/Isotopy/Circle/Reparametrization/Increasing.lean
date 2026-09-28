import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Reparametrization.Lift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.PeriodicCircle
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Extension



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 2) := ⟨by simp⟩
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩
private abbrev coordinates := Complex.orthonormalBasisOneI.repr

open PoincareConjecture Plane

private theorem unitCircleExp_injOn_Ico (a : Real) :
    InjOn unitCircleExp (Ico a (a + 1)) := by
  intro s hs t ht heq
  obtain ⟨n, hn⟩ := unitCircleExp_eq_iff.mp heq
  have hlow : (-1 : Real) < n := by linarith [hs.1, ht.2]
  have hhigh : (n : Real) < 1 := by linarith [hs.2, ht.1]
  have hl : (-1 : Int) < n := by exact_mod_cast hlow
  have hh : n < (1 : Int) := by exact_mod_cast hhigh
  have : n = 0 := by omega
  simpa [this] using hn

private theorem hasDerivAt_unitCircleExp_coe (s : Real) :
    HasDerivAt (fun t : Real => (unitCircleExp t : E2))
      ((2 * Real.pi) • coordinates (Complex.I *
        (Circle.exp ((2 * Real.pi) * s) : ℂ))) s := by
  convert! (hasDerivAt_sphereCircleParameter_coe coordinates ((2 * Real.pi) * s)).scomp s
    ((hasDerivAt_id s).const_mul (2 * Real.pi)) using 1
  simp



theorem exists_ambient_diffeomorph_of_increasing_circle_lift
    (L : Real ≃ₘ[Real] Real) (hm : StrictMono L)
    (hperiod : ∀ s, L (s + 1) = L s + 1) :
    ∃ G : E2 ≃ₘ[Real] E2,
      (∃ K : Set E2, IsCompact K ∧ ∀ x ∉ K, G x = x) ∧
      ∀ s, G (unitCircleExp s) = (unitCircleExp (L s) : E2) := by
  let B : Real → Real → Real := fun t s => (1 - t) * s + t * L s
  have hB : ContDiff Real ∞ (fun z : Real × Real => B z.1 z.2) :=
    ((contDiff_const.sub contDiff_fst).mul contDiff_snd).add
      (contDiff_fst.mul (L.contDiff.comp contDiff_snd))
  have hBp (t s : Real) : B t (s + 1) = B t s + 1 := by
    dsimp [B]
    rw [hperiod]
    ring
  have hBd (t s : Real) : HasDerivAt (B t) ((1 - t) + t * deriv L s) s := by
    convert! ((hasDerivAt_id s).const_mul (1 - t)).add
      (((L.contDiff.differentiable (by simp)) s).hasDerivAt.const_mul t) using 1
    simp
  have hBpos (t : Real) (ht : t ∈ Icc 0 1) (s : Real) :
      0 < (1 - t) + t * deriv L s := by
    have hpos : 0 < deriv L s :=
      lt_of_le_of_ne hm.monotone.deriv_nonneg (deriv_real_diffeomorph_ne_zero L s).symm
    by_cases hzero : t = 0
    · simp [hzero]
    · exact add_pos_of_nonneg_of_pos (by linarith [ht.2])
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hzero)) hpos)
  have hBm (t : Real) (ht : t ∈ Icc 0 1) : StrictMono (B t) :=
    strictMono_of_deriv_pos (fun s => by
      rw [(hBd t s).deriv]
      exact hBpos t ht s)
  let γ : Real → Real → E2 := fun t s => unitCircleExp (B t s)
  have hγ : ContDiff Real ∞ (fun z : Real × Real => γ z.1 z.2) :=
    ((contMDiff_coe_sphere (E := E2) (n := 1) (m := ∞)).comp
      contMDiff_unitCircleExp).contDiff.comp hB
  have hp (t : Real) : Periodic (γ t) 1 := by
    intro s
    dsimp [γ]
    rw [hBp, unitCircleExp_periodic]
  have hi (t : Real) (ht : t ∈ Icc 0 1) : InjOn (γ t) (Ico 0 1) := by
    intro s hs u hu heq
    apply (hBm t ht).injective
    apply unitCircleExp_injOn_Ico (B t 0)
    · exact ⟨(hBm t ht).monotone hs.1, by
        rw [← hBp, zero_add]; exact (hBm t ht) hs.2⟩
    · exact ⟨(hBm t ht).monotone hu.1, by
        rw [← hBp, zero_add]; exact (hBm t ht) hu.2⟩
    · exact Subtype.ext heq
  have hr (t : Real) (ht : t ∈ Icc 0 1) (s : Real) : deriv (γ t) s ≠ 0 := by
    have hd := (hasDerivAt_unitCircleExp_coe (B t s)).scomp s (hBd t s)
    change HasDerivAt (γ t) _ s at hd
    rw [hd.deriv]
    apply smul_ne_zero (ne_of_gt (hBpos t ht s))
    apply smul_ne_zero (ne_of_gt Real.two_pi_pos)
    exact norm_ne_zero_iff.mp (by
      simp only [coordinates.norm_map, norm_mul, Complex.norm_I, Circle.norm_coe, one_mul]
      norm_num)
  let c : Real → S1 → E2 := fun t => periodicCircleCurve 1 coordinates (γ t)
  have hc : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × S1 => c z.1 z.2) :=
    contMDiff_periodicCircleCurve_family (by norm_num) coordinates γ hγ hp
  have hc_exp (t s : Real) : c t (unitCircleExp s) = γ t s := by
    change periodicCircleCurve 1 coordinates (γ t)
      (sphereCircleParameter coordinates ((2 * Real.pi) * s)) = γ t s
    rw [periodicCircleCurve_sphereCircleParameter (by norm_num) coordinates (hp t)]
    congr 1
    field_simp
  have hγslice (t : Real) : ContDiff Real ∞ (γ t) :=
    hγ.comp (f := fun s : Real => (t, s))
      (show ContDiff Real ∞ (fun s : Real => (t, s)) from
      contDiff_const.prodMk contDiff_id)
  have hci (t : Real) (ht : t ∈ Icc 0 1) : Injective (c t) :=
    injective_periodicCircleCurve (by norm_num : (0 : Real) < 1)
      coordinates (hp t) (hi t ht)
  have hcm (t : Real) (ht : t ∈ Icc 0 1) (p : S1) :
      Injective (mfderiv (𝓡 1) (𝓡 2) (c t) p) :=
    mfderiv_periodicCircleCurve_injective (by norm_num : (0 : Real) < 1)
      coordinates (hp t) (hγslice t) (hr t ht) p
  obtain ⟨Phi, hPhi0, _, hcompact, hmotion⟩ :=
    exists_ambient_isotopy_of_smooth_circle_family
      (Orientation.map (Fin 2) coordinates.toLinearEquiv Complex.orientation)
      (unitCircleExp 0) c hc
      (a := 0) (b := 1) (by norm_num)
      hci hcm
  refine ⟨Phi 1, ?_, fun s => ?_⟩
  · obtain ⟨K, hK, hfix⟩ := hcompact
    exact ⟨K, hK, hfix 1⟩
  · have h := hmotion 1 (show (1 : Real) ∈ Icc 0 1 by norm_num) (unitCircleExp s)
    simpa [hc_exp, γ, B] using h

end Poincare.Manifold.Schoenflies
