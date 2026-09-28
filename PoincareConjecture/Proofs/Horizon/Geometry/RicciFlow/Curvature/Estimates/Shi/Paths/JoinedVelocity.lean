import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.Density
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.JoinedVariation
import Mathlib.Analysis.Calculus.Deriv.Comp













set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem shi_joined_second_add {f h : V → V}
    (hf : ContDiffAt ℝ 2 f 0) (hh : ContDiffAt ℝ 2 h 0) (v : V) :
    (fderiv ℝ (fderiv ℝ (f + h)) 0 v) v =
      (fderiv ℝ (fderiv ℝ f) 0 v) v + (fderiv ℝ (fderiv ℝ h) 0 v) v := by
  have he := congrArg
    (fun Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) V => Q (fun _ => v))
    (iteratedFDeriv_add_apply (i := 2) hf hh)
  simpa only [add_apply, iteratedFDeriv_two_apply] using he

private theorem shi_joined_second_sub {f h : V → V}
    (hf : ContDiffAt ℝ 2 f 0) (hh : ContDiffAt ℝ 2 h 0) (v : V) :
    (fderiv ℝ (fderiv ℝ (f - h)) 0 v) v =
      (fderiv ℝ (fderiv ℝ f) 0 v) v - (fderiv ℝ (fderiv ℝ h) 0 v) v := by
  have he := congrArg
    (fun Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) V => Q (fun _ => v))
    (iteratedFDeriv_sub_apply (i := 2) hf hh)
  simpa only [sub_apply, iteratedFDeriv_two_apply] using he

private theorem shi_joined_second_smul {f : V → V}
    (hf : ContDiffAt ℝ 2 f 0) (r : ℝ) (v : V) :
    (fderiv ℝ (fderiv ℝ (r • f)) 0 v) v =
      r • (fderiv ℝ (fderiv ℝ f) 0 v) v := by
  have he := congrArg
    (fun Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) V => Q (fun _ => v))
    (iteratedFDeriv_const_smul_apply (i := 2) (a := r) hf)
  simpa only [smul_apply, iteratedFDeriv_two_apply] using he

set_option backward.isDefEq.respectTransparency false in
private theorem shi_joined_quadratic_jets
    (x : V) (A : V →L[ℝ] V) (B : V →L[ℝ] V →L[ℝ] V) :
    ContDiffAt ℝ 2 (quadraticPathJet x A B) 0 ∧
      quadraticPathJet x A B 0 = x ∧
      fderiv ℝ (quadraticPathJet x A B) 0 = A ∧
      ∀ v, (fderiv ℝ (fderiv ℝ (quadraticPathJet x A B)) 0 v) v = B v v := by
  let C : V →L[ℝ] V →L[ℝ] V := (1 / 2 : ℝ) • (B + B.flip)
  have hd (z : V) : HasFDerivAt (quadraticPathJet x A B) (A + C z) z := by
    have h := (B.hasFDerivAt_of_bilinear
      (hasFDerivAt_id z) (hasFDerivAt_id z)).const_smul (1 / 2 : ℝ)
    have heq : (1 / 2 : ℝ) •
        (B.precompR V z (ContinuousLinearMap.id ℝ V) +
          B.precompL V (ContinuousLinearMap.id ℝ V) z) = C z := by
      ext v : 1
      change (1 / 2 : ℝ) • (B z v + B v z) =
        (1 / 2 : ℝ) • (B z v + B v z)
      rfl
    simp only [id_eq] at h
    rw [heq] at h
    simpa +instances only [quadraticPathJet, Pi.add_apply, Pi.smul_apply, zero_add]
      using! ((hasFDerivAt_const x z).add A.hasFDerivAt).add h
  have hfirst : fderiv ℝ (quadraticPathJet x A B) = fun z => A + C z :=
    funext fun z => (hd z).fderiv
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hx : ContDiffAt ℝ 2 (fun _ : V => x) 0 := contDiffAt_const
    simpa +instances only [quadraticPathJet, Pi.add_apply, Pi.smul_apply] using!
      (hx.add A.contDiff.contDiffAt).add
        ((B.contDiff.contDiffAt.clm_apply contDiffAt_id).const_smul (1 / 2 : ℝ))
  · simp [quadraticPathJet]
  · simpa only [map_zero, add_zero] using (hd 0).fderiv
  · intro v
    rw [hfirst, (C.hasFDerivAt.const_add A).fderiv]
    change (1 / 2 : ℝ) • (B v v + B v v) = B v v
    module

private theorem shi_joined_comp_deriv {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {G : V → Y} {x : ℝ → V} {s : Set ℝ} {t : ℝ} {T : V}
    (hG : DifferentiableAt ℝ G (x t)) (hx : HasDerivWithinAt x T s t) :
    HasDerivWithinAt (fun a => G (x a)) (fderiv ℝ G (x t) T) s t := by
  exact HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ) (F := V) (E := Y)
    (l := G) (f := x) t hG.hasFDerivAt hx

private theorem shi_joined_clm_deriv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) {f : ℝ → X} {f' : X} {s : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun a => L (f a)) (L f') s t := by
  exact HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ) (F := X) (E := Y)
    (l := L) (f := f) t L.hasFDerivAt hf

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem shi_joined_bilinear_deriv
    {G : ℝ → V →L[ℝ] V →L[ℝ] V} {A : ℝ → V →L[ℝ] V}
    {H : V →L[ℝ] V →L[ℝ] V} {J : V →L[ℝ] V} {s : Set ℝ} {t : ℝ}
    (hG : HasDerivWithinAt G H s t) (hA : HasDerivWithinAt A J s t) :
    HasDerivWithinAt (fun a => -(G a).bilinearComp (A a) (A a))
      (-H.bilinearComp (A t) (A t) - (G t).bilinearComp J (A t) -
        (G t).bilinearComp (A t) J) s t := by
  let L :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V V).toLinearIsometry.toContinuousLinearMap
  have hflip {f : ℝ → V →L[ℝ] V →L[ℝ] V} {f' : V →L[ℝ] V →L[ℝ] V}
      (hf : HasDerivWithinAt f f' s t) :
      HasDerivWithinAt (fun a => (f a).flip) f'.flip s t := by
    have hh := shi_joined_clm_deriv
      (X := V →L[ℝ] V →L[ℝ] V) (Y := V →L[ℝ] V →L[ℝ] V) L hf
    simpa +instances only [L, ContinuousLinearMap.coe_flipₗᵢ] using! hh
  have h := hflip ((hflip (hG.clm_comp hA)).clm_comp hA)
  have hneg : HasDerivWithinAt
      (fun a => -(((G a).comp (A a)).flip.comp (A a)).flip)
      (-(((H.comp (A t) + (G t).comp J).flip.comp (A t) +
          ((G t).comp (A t)).flip.comp J).flip)) s t := by
    simpa +instances only [Pi.neg_apply] using!
      HasDerivWithinAt.neg (𝕜 := ℝ) (F := V →L[ℝ] V →L[ℝ] V) h
  have hfun :
      (fun a => -(((G a).comp (A a)).flip.comp (A a)).flip) =
        (fun a => -(G a).bilinearComp (A a) (A a)) := by
    funext a
    rfl
  rw [← hfun]
  have heq : -(((H.comp (A t) + (G t).comp J).flip.comp (A t) +
      ((G t).comp (A t)).flip.comp J).flip) =
      -H.bilinearComp (A t) (A t) - (G t).bilinearComp J (A t) -
        (G t).bilinearComp (A t) J := by
    ext v w : 2
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.bilinearComp_apply, add_apply, sub_apply, neg_apply]
    abel
  rw [heq] at hneg
  exact hneg

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem shiChart_joined_density_second_jet [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M V}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ c.symm c.target)
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (x : ℝ → V) (P : ℝ → V →L[ℝ] V) {T : V}
    (ha : x a ∈ c.target) (hb : x b ∈ c.target) (hx : x t ∈ c.target)
    (hxd : HasDerivWithinAt x T (Icc a b) t)
    (hPd : HasDerivWithinAt P
      (-((shiChartChristoffel D c (x t) T).comp (P t))) (Icc a b) t)
    {left right : V → V}
    (hl : ContDiffAt ℝ 2 left 0) (hr : ContDiffAt ℝ 2 right 0)
    (hl0 : left 0 = x a) (hr0 : right 0 = x b)
    (hl1 : fderiv ℝ left 0 = a • P a) (hr1 : fderiv ℝ right 0 = b • P b)
    (hl2 : ∀ v, (fderiv ℝ (fderiv ℝ left) 0 v) v =
      -shiChartChristoffel D c (x a) (a • P a v) (a • P a v))
    (hr2 : ∀ v, (fderiv ℝ (fderiv ℝ right) 0 v) v =
      -shiChartChristoffel D c (x b) (b • P b v) (b • P b v)) :
    let A : ℝ → V →L[ℝ] V := fun s => s • P s
    let B : ℝ → V →L[ℝ] V →L[ℝ] V := fun s =>
      -(shiChartChristoffel D c (x s)).bilinearComp (A s) (A s)
    let F := joinedCoordinateVariation a b x A B left right
    let W : V → V := fun z => derivWithin (fun s => F s z) (Icc a b) t
    let e : V → ℝ := fun z => shiChartMetric g c (F t z) (W z) (W z)
    let S := mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (x t)
    ContDiffAt ℝ 2 e 0 ∧ e 0 = shiChartMetric g c (x t) T T ∧
      (∀ v, fderiv ℝ e 0 v = 2 * shiChartMetric g c (x t) (P t v) T) ∧
      ∀ v, (fderiv ℝ (fderiv ℝ e) 0 v) v =
        2 * (shiChartMetric g c (x t) (P t v) (P t v) -
          D.curvatureTensor (c.symm (x t)) (S T) (S (t • P t v))
            (S T) (S (t • P t v))) := by
  let Γ := shiChartChristoffel D c
  let A : ℝ → V →L[ℝ] V := fun s => s • P s
  let B : ℝ → V →L[ℝ] V →L[ℝ] V := fun s =>
    -(Γ (x s)).bilinearComp (A s) (A s)
  let F := joinedCoordinateVariation a b x A B left right
  let W : V → V := fun z => derivWithin (fun s => F s z) (Icc a b) t
  let J : V →L[ℝ] V := P t - (Γ (x t) T).comp (A t)
  let H := fderiv ℝ Γ (x t) T
  let B1 := -H.bilinearComp (A t) (A t) -
    (Γ (x t)).bilinearComp J (A t) - (Γ (x t)).bilinearComp (A t) J
  have hA : HasDerivWithinAt A J (Icc a b) t := by
    have h := (hasDerivWithinAt_id t (Icc a b)).smul hPd
    apply h.congr_deriv
    ext v : 1
    simp only [J, A, Γ, id_eq, one_smul, add_apply, sub_apply, neg_apply,
      smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_neg]
    abel
  have hΓ : DifferentiableAt ℝ Γ (x t) :=
    ((shiChartChristoffel_smooth D hc hi).contDiffAt
      (c.open_target.mem_nhds hx)).differentiableAt (by simp)
  have hG : HasDerivWithinAt (fun s => Γ (x s)) H (Icc a b) t :=
    shi_joined_comp_deriv (Y := V →L[ℝ] V →L[ℝ] V) (G := Γ) hΓ hxd
  have hB : HasDerivWithinAt B B1 (Icc a b) t := shi_joined_bilinear_deriv hG hA
  let q : ℝ → V → V := fun s => quadraticPathJet (x s) (A s) (B s)
  let l : V → V := fun z => left z - q a z
  let r : V → V := fun z => right z - q b z
  have hq (s : ℝ) := shi_joined_quadratic_jets (x s) (A s) (B s)
  have hlc : ContDiffAt ℝ 2 l 0 := hl.sub (hq a).1
  have hrc : ContDiffAt ℝ 2 r 0 := hr.sub (hq b).1
  have hlv : l 0 = 0 := by simp [l, q, quadraticPathJet, hl0]
  have hrv : r 0 = 0 := by simp [r, q, quadraticPathJet, hr0]
  have hld : HasFDerivAt l (0 : V →L[ℝ] V) 0 := by
    have hqa : HasFDerivAt (q a) (A a) 0 := by
      simpa only [q, (hq a).2.2.1] using
        ((hq a).1.differentiableAt (by norm_num)).hasFDerivAt
    simpa only [l, hl1, A, sub_self] using!
      (hl.differentiableAt (by norm_num)).hasFDerivAt.sub hqa
  have hrd : HasFDerivAt r (0 : V →L[ℝ] V) 0 := by
    have hqb : HasFDerivAt (q b) (A b) 0 := by
      simpa only [q, (hq b).2.2.1] using
        ((hq b).1.differentiableAt (by norm_num)).hasFDerivAt
    simpa only [r, hr1, A, sub_self] using!
      (hr.differentiableAt (by norm_num)).hasFDerivAt.sub hqb
  have hlh (v : V) : (fderiv ℝ (fderiv ℝ l) 0 v) v = 0 := by
    change (fderiv ℝ (fderiv ℝ (left - quadraticPathJet (x a) (A a) (B a))) 0 v) v = 0
    rw [shi_joined_second_sub hl (hq a).1 v, hl2, (hq a).2.2.2]
    simp only [B, Γ, A, neg_apply, ContinuousLinearMap.bilinearComp_apply,
      smul_apply, sub_self]
  have hrh (v : V) : (fderiv ℝ (fderiv ℝ r) 0 v) v = 0 := by
    change (fderiv ℝ (fderiv ℝ (right - quadraticPathJet (x b) (A b) (B b))) 0 v) v = 0
    rw [shi_joined_second_sub hr (hq b).1 v, hr2, (hq b).2.2.2]
    simp only [B, Γ, A, neg_apply, ContinuousLinearMap.bilinearComp_apply,
      smul_apply, sub_self]
  have hFc : ContDiffAt ℝ 2 (F t) 0 :=
    ((hq t).1.add (hlc.const_smul ((b - t) / (b - a)))).add
      (hrc.const_smul ((t - a) / (b - a)))
  have hF0 : F t 0 = x t := by
    change q t 0 + ((b - t) / (b - a)) • l 0 +
      ((t - a) / (b - a)) • r 0 = x t
    simp only [q, (hq t).2.1, hlv, hrv, smul_zero, add_zero]
  have hF1 : fderiv ℝ (F t) 0 = A t := by
    have h := (((hq t).1.differentiableAt (by norm_num)).hasFDerivAt.add
      (hld.const_smul ((b - t) / (b - a)))).add
        (hrd.const_smul ((t - a) / (b - a)))
    simpa only [(hq t).2.2.1, smul_zero, add_zero] using! h.fderiv
  have hF2 (v : V) : (fderiv ℝ (fderiv ℝ (F t)) 0 v) v =
      -Γ (x t) (A t v) (A t v) := by
    change (fderiv ℝ (fderiv ℝ
      (quadraticPathJet (x t) (A t) (B t) +
        ((b - t) / (b - a)) • l + ((t - a) / (b - a)) • r)) 0 v) v = _
    rw [shi_joined_second_add
      (f := quadraticPathJet (x t) (A t) (B t) + ((b - t) / (b - a)) • l)
      (h := ((t - a) / (b - a)) • r)
      ((hq t).1.add (hlc.const_smul ((b - t) / (b - a))))
      (hrc.const_smul ((t - a) / (b - a))) v,
      shi_joined_second_add (f := quadraticPathJet (x t) (A t) (B t))
        (h := ((b - t) / (b - a)) • l)
        (hq t).1 (hlc.const_smul ((b - t) / (b - a))) v,
      shi_joined_second_smul hlc, shi_joined_second_smul hrc, hlh, hrh,
      (hq t).2.2.2]
    simp only [B, neg_apply, ContinuousLinearMap.bilinearComp_apply, smul_zero, add_zero]

  have hWeq : W = fun z => quadraticPathJet T J B1 z + (b - a)⁻¹ • (r z - l z) := by
    funext z
    exact (hasDerivWithinAt_joinedCoordinateVariation a b t z x A B left right
      T J B1 hxd hA hB).derivWithin ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt ht)
  have hQ := shi_joined_quadratic_jets T J B1
  have hWc : ContDiffAt ℝ 2 W 0 := by
    rw [hWeq]
    exact hQ.1.add ((hrc.sub hlc).const_smul _)
  have hW0 : W 0 = T := by
    rw [hWeq]
    simp only [hQ.2.1, hrv, hlv, sub_self, smul_zero, add_zero]
  have hW1 : fderiv ℝ W 0 = J := by
    rw [hWeq]
    have h := (hQ.1.differentiableAt (by norm_num)).hasFDerivAt.add
      ((hrd.sub hld).const_smul (b - a)⁻¹)
    simpa only [hQ.2.2.1, sub_self, smul_zero, add_zero] using! h.fderiv
  have hW2 (v : V) : (fderiv ℝ (fderiv ℝ W) 0 v) v =
      -(fderiv ℝ Γ (x t) T) (A t v) (A t v) -
        (2 : ℝ) • Γ (x t) (fderiv ℝ W 0 v) (A t v) := by
    have hdiag : (fderiv ℝ (fderiv ℝ W) 0 v) v = B1 v v := by
      rw [hWeq]
      change (fderiv ℝ (fderiv ℝ
        (quadraticPathJet T J B1 + (b - a)⁻¹ • (r - l))) 0 v) v = B1 v v
      rw [shi_joined_second_add (f := quadraticPathJet T J B1)
          (h := (b - a)⁻¹ • (r - l)) hQ.1 ((hrc.sub hlc).const_smul (b - a)⁻¹) v,
        shi_joined_second_smul (f := r - l) (hrc.sub hlc),
        shi_joined_second_sub hrc hlc,
        hrh, hlh, hQ.2.2.2]
      simp only [sub_self, smul_zero, add_zero]
    rw [hdiag, hW1]
    simp only [B1, H, sub_apply, neg_apply, ContinuousLinearMap.bilinearComp_apply]
    rw [shiChartChristoffel_symm D hc hi hx (A t v) (J v)]
    module
  have hd := shiChart_density_second_jet D hc hi hx hFc hWc hF0 hW0 hF1 hW1 hF2 hW2
  refine ⟨hd.1, ?_, hd.2.1, ?_⟩
  · change shiChartMetric g c (F t 0) (W 0) (W 0) = _
    rw [hF0, hW0]
  · simpa only [A, smul_apply] using! hd.2.2


end PoincareConjecture.RicciFlowAnalysis
