import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Circle.Normal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Correction
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev P2 := Real × E2

private theorem isLocalDiffeomorphAt_of_contDiff_bijective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {F : E → E} (hF : ContDiff Real ∞ F)
    {a : E} (ha : Function.Bijective (fderiv Real F a)) :
    IsLocalDiffeomorphAt 𝓘(Real, E) 𝓘(Real, E) ∞ F a := by
  let U : Set E := {x | IsUnit (fderiv Real F x)}
  have hU : IsOpen U := Units.isOpen.preimage (hF.fderiv_right (m := ∞) (by simp)).continuous
  let A := ContinuousLinearEquiv.ofBijective (fderiv Real F a)
    (LinearMap.ker_eq_bot.mpr ha.1) (LinearMap.range_eq_top.mpr ha.2)
  have hd : HasFDerivAt F A.toContinuousLinearMap a :=
    (hF.differentiable (by simp) a).hasFDerivAt
  let Q := hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp)
  let H := Q.restr U
  have hHsource : H.source ⊆ U := fun z hz => interior_subset hz.2
  have heq : (H : E → E) = F := rfl
  have hHa : a ∈ H.source := by
    change a ∈ (Q.restr U).source
    rw [Q.restr_source' U hU]
    exact ⟨hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),
      ContinuousLinearMap.isUnit_iff_bijective.mpr ha⟩
  have hHi : ContMDiffOn 𝓘(Real, E) 𝓘(Real, E) ∞ H.symm H.target := by
    intro y hy
    have hz := H.map_target hy
    have hzbij := ContinuousLinearMap.isUnit_iff_bijective.mp (hHsource hz)
    let B := ContinuousLinearEquiv.ofBijective (fderiv Real F (H.symm y))
      (LinearMap.ker_eq_bot.mpr hzbij.1) (LinearMap.range_eq_top.mpr hzbij.2)
    have hdB : HasFDerivAt H B.toContinuousLinearMap (H.symm y) := by
      rw [heq]
      exact (hF.differentiable (by simp) _).hasFDerivAt
    exact (H.contDiffAt_symm hy hdB hF.contDiffAt).contMDiffWithinAt.mono (subset_univ _)
  let Φ : PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ := {
    toPartialEquiv := H.toPartialEquiv
    open_source := H.open_source
    open_target := H.open_target
    contMDiffOn_toFun := hF.contMDiff.contMDiffOn.congr (fun _ _ => rfl)
    contMDiffOn_invFun := hHi }
  exact ⟨Φ, hHa, fun _ _ => rfl⟩

theorem exists_parametric_circle_neighborhood
    {T : Set Real} (hT : IsCompact T) (G : P2 → E2)
    (hG : ContDiff Real ∞ G)
    (hf : ∀ t ∈ T, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun p : S1 => G (t, p))) :
    ∃ e : OpenPartialHomeomorph P2 P2,
      T ×ˢ sphere 0 1 ⊆ e.source ∧
      (fun z : P2 => (z.1, G z)) '' (T ×ˢ sphere 0 1) ⊆ e.target ∧
      ContMDiffOn 𝓘(Real, P2) 𝓘(Real, P2) ∞ e e.source ∧
      ContMDiffOn 𝓘(Real, P2) 𝓘(Real, P2) ∞ e.symm e.target ∧
      (∀ z ∈ e.source, (e z).1 = z.1) ∧
      ∀ t ∈ T, ∀ p : S1, e (t, p) = (t, G (t, p)) := by
  let A : P2 → E2 →L[Real] E2 := fun z =>
    (fderiv Real G z).comp (ContinuousLinearMap.inr Real Real E2)
  have hA : ContDiff Real ∞ A :=
    (hG.fderiv_right (by simp)).clm_comp contDiff_const
  have hslice (t : Real) : ContDiff Real ∞ (fun x : E2 => G (t, x)) :=
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hAslice (t : Real) (x : E2) : A (t, x) = fderiv Real (fun y => G (t, y)) x := by
    exact ((hG.differentiable (by simp) (t, x)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right t x)).fderiv.symm
  let N : P2 → E2 := fun z => circleNormal (A z) z.2
  have hN : ContDiff Real ∞ N :=
    circleQuarterTurn.toContinuousLinearEquiv.contDiff.comp
      (hA.clm_apply (circleQuarterTurn.toContinuousLinearEquiv.contDiff.comp contDiff_snd))
  let C : P2 → E2 := fun z =>
    G z + ((‖z.2‖ ^ 2 - 1) / 2) • (N z - A z z.2)
  have hC : ContDiff Real ∞ C :=
    hG.add (((((contDiff_snd (𝕜 := Real)).norm_sq (𝕜 := Real)).sub contDiff_const).div_const 2).smul
      (hN.sub (hA.clm_apply contDiff_snd)))
  have hCslice (t : Real) : (fun x => C (t, x)) =
      correctNormal (fun x => G (t, x)) (fun x => N (t, x)) := by
    funext x
    simp only [C, correctNormal, hAslice]
  have hrestrict (t : Real) (p : S1) : C (t, p) = G (t, p) := by
    simp [C]
  have hCbij (t : Real) (ht : t ∈ T) (p : S1) :
      Function.Bijective (fderiv Real (fun x => C (t, x)) p) := by
    have hNt : ContDiff Real ∞ (fun x => N (t, x)) :=
      hN.comp (contDiff_const.prodMk contDiff_id)
    have hinj := injective_tangent_add_circleNormal
      (fderiv Real (fun x => G (t, x)) p) p (by simp)
      (injOn_fderiv_extension_tangent_circle (hf t ht) (hslice t) (fun _ => rfl) p)
    have heq : (fderiv Real (fun x => C (t, x)) p : E2 → E2) =
        fun v => fderiv Real (fun x => G (t, x)) p
          (v - inner Real (p : E2) v • (p : E2)) + inner Real (p : E2) v • N (t, p) := by
      rw [hCslice]
      exact funext (fderiv_correctNormal (hslice t) hNt (by simp))
    have hi : Function.Injective (fderiv Real (fun x => C (t, x)) p) := by
      rw [heq]
      simpa only [N, hAslice] using hinj
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  let F : P2 → P2 := fun z => (z.1, C z)
  have hF : ContDiff Real ∞ F := contDiff_fst.prodMk hC
  have hFbij (t : Real) (ht : t ∈ T) (p : S1) :
      Function.Bijective (fderiv Real F (t, p)) := by
    have hder : fderiv Real F (t, (p : E2)) =
        (ContinuousLinearMap.fst Real Real E2).prod (fderiv Real C (t, (p : E2))) := by
      change fderiv Real (fun z : P2 => (z.1, C z)) (t, (p : E2)) = _
      have hh := ((contDiff_fst (𝕜 := Real) (n := ∞)).differentiable (by simp)
        (t, (p : E2))).fderiv_prodMk (hC.differentiable (by simp) (t, (p : E2)))
      rw [fderiv_fst] at hh
      exact hh
    have hvertical (v : E2) :
        (fderiv Real F (t, (p : E2)) (0, v)).2 = fderiv Real (fun x => C (t, x)) p v := by
      have h := ((hC.differentiable (by simp) (t, (p : E2))).hasFDerivAt.comp (p : E2)
        (hasFDerivAt_prodMk_right t (p : E2))).fderiv
      rw [hder]
      have hv := congrArg (fun L : E2 →L[Real] E2 => L v) h.symm
      change fderiv Real C (t, p) (0, v) = fderiv Real (fun x => C (t, x)) p v at hv
      simpa using hv
    have hi : Function.Injective (fderiv Real F (t, p)) := by
      intro u v huv
      have htime : u.1 = v.1 := by
        have h := congrArg Prod.fst huv
        have hu' : (fderiv Real F (t, p) u).1 = u.1 := by
          have hh := congrArg Prod.fst (congrArg (fun L : P2 →L[Real] P2 => L u) hder)
          change (fderiv Real F (t, (p : E2)) u).1 = u.1 at hh
          exact hh
        have hv' : (fderiv Real F (t, p) v).1 = v.1 := by
          have hh := congrArg Prod.fst (congrArg (fun L : P2 →L[Real] P2 => L v) hder)
          change (fderiv Real F (t, (p : E2)) v).1 = v.1 at hh
          exact hh
        exact hu'.symm.trans (h.trans hv')
      have hd : fderiv Real F (t, p) (0, u.2 - v.2) = 0 := by
        have he : (0, u.2 - v.2) = u - v := by ext <;> simp [htime]
        rw [he, map_sub]
        exact sub_eq_zero.mpr huv
      have hx : u.2 - v.2 = 0 := (hCbij t ht p).1 (by
        simpa only [hvertical, Prod.snd_zero, map_zero] using congrArg Prod.snd hd)
      exact Prod.ext htime (sub_eq_zero.mp hx)
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  have hinj : InjOn F (T ×ˢ sphere 0 1) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩ ⟨s, y⟩ ⟨hs, hy⟩ he
    have hts : t = s := congrArg Prod.fst he
    subst s
    have hxy : G (t, x) = G (t, y) := by
      simpa only [F, hrestrict t ⟨x, hx⟩, hrestrict t ⟨y, hy⟩] using congrArg Prod.snd he
    exact Prod.ext rfl (congrArg Subtype.val ((hf t ht).isEmbedding.injective
      (show G (t, (⟨x, hx⟩ : S1)) = G (t, (⟨y, hy⟩ : S1)) from hxy)))
  obtain ⟨e, he, ht, heq, hes, hei⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact
      (hT.prod (isCompact_sphere 0 1)) hinj (by
        rintro ⟨t, x⟩ ⟨ht, hx⟩
        exact isLocalDiffeomorphAt_of_contDiff_bijective hF (hFbij t ht ⟨x, hx⟩))
  refine ⟨e, he, ?_, hes, hei, ?_, ?_⟩
  · rintro y ⟨⟨t, x⟩, ⟨htt, hx⟩, rfl⟩
    apply ht
    exact ⟨(t, x), ⟨htt, hx⟩, Prod.ext rfl (hrestrict t ⟨x, hx⟩)⟩
  · intro z hz
    rw [heq hz]
  · intro t htt p
    have hp : (t, (p : E2)) ∈ T ×ˢ sphere 0 1 := ⟨htt, p.property⟩
    rw [heq (he hp)]
    exact Prod.ext rfl (hrestrict t p)

end Poincare.Manifold.Schoenflies
